// ==UserScript==
// @name         kino.watch — вторые субтитры (RU) + навигация по фразам + скорость + история на паузе
// @namespace    local.kino.dualsubs
// @version      1.3
// @description  Вторая дорожка субтитров (RU) поверх плеера; , и . — по английским фразам; Shift+, и Shift+. — скорость; пауза пробелом показывает последние N фраз с переводом.
// @match        https://kino.watch/*
// @run-at       document-start
// @grant        none
// ==/UserScript==

(function () {
  'use strict';

  /* ---------- константы ---------- */
  const LS = 'kwDualSubs';
  const SPEEDS = [0.25, 0.5, 0.75, 1, 1.25, 1.5, 1.75, 2]; // шаги скорости, как на YouTube
  const LEAD = 0.2;          // за сколько секунд до начала фразы приземляемся
  const REPLAY_AFTER = 1.2;  // «,» повторяет текущую фразу, если с её начала прошло больше стольких секунд
  const MERGE_GAP = 1.2;     // реплики ближе этого (и без точки в конце) склеиваются в одну фразу
  const SKIP_SOUND = true;   // пропускать реплики вида (BANGING), [music], ♪

  /* ---------- настройки (сохраняются в localStorage) ---------- */
  const cfg = Object.assign(
    { on: true, lang: 'rus', track: '', offset: 0, size: 22, pos: 16, hist: true, histN: 5 },
    (() => { try { return JSON.parse(localStorage.getItem(LS) || '{}'); } catch (e) { return {}; } })()
  );
  const save = () => { try { localStorage.setItem(LS, JSON.stringify(cfg)); } catch (e) {} };

  /* ---------- ловим URL мастер-плейлиста HLS ---------- */
  let masterUrl = null;
  try { performance.setResourceTimingBufferSize(5000); } catch (e) {}
  const scan = list => { for (const r of list) if (/manifest\/hls4\/.*\.m3u8/.test(r.name)) masterUrl = r.name; };
  try {
    scan(performance.getEntriesByType('resource'));
    new PerformanceObserver(l => scan(l.getEntries())).observe({ type: 'resource', buffered: true });
  } catch (e) {}

  /* ---------- состояние ---------- */
  let curMaster = null, tracks = [], cues = [], loadId = 0, shown = null, styleKey = '';
  let refName = '', refId = 0, phrases = [];            // тайминги фраз (английская дорожка)
  let ruMsg = '', refMsg = '';
  const cache = new Map();                               // uri -> Promise<cues>
  let rootEl, sh, subEl, panelEl, btnEl, selEl, stEl, toastEl, toastTimer, histEl, histVisible = false;
  let boundVideo = null, spaceBefore = null, panelOpen = false;
  let vOff, vSize, vPos, vHn;

  /* ---------- утилиты ---------- */
  const getHost = () => document.querySelector('media-player');
  const getVideo = () => { const h = getHost(); return h && h.querySelector('video'); };
  const el = (tag, cls, text) => {
    const n = document.createElement(tag);
    if (cls) n.className = cls;
    if (text != null) n.textContent = text;
    return n;
  };

  const get = async url => {
    const r = await fetch(url);
    if (!r.ok) throw new Error('HTTP ' + r.status);
    return r.text();
  };

  function parseMaster(text, base) {
    const out = [];
    for (const line of text.split(/\r?\n/)) {
      if (!line.startsWith('#EXT-X-MEDIA:') || !/TYPE=SUBTITLES/.test(line)) continue;
      const a = {};
      for (const m of line.matchAll(/([A-Z0-9-]+)=("[^"]*"|[^,]*)/g)) a[m[1]] = m[2].replace(/^"|"$/g, '');
      if (a.URI) out.push({ name: a.NAME, lang: a.LANGUAGE, uri: new URL(a.URI, base).href });
    }
    return out;
  }

  const ts = s => {
    const p = s.trim().replace(',', '.').split(':').map(parseFloat);
    return p.length === 3 ? p[0] * 3600 + p[1] * 60 + p[2] : p[0] * 60 + p[1];
  };

  function parseVTT(text, out) {
    for (const block of text.replace(/\r/g, '').split(/\n\n+/)) {
      const lines = block.split('\n');
      const i = lines.findIndex(l => l.includes('-->'));
      if (i < 0) continue;
      const m = lines[i].match(/([\d:.,]+)\s*-->\s*([\d:.,]+)/);
      if (!m) continue;
      const t = lines.slice(i + 1).join('\n').replace(/<[^>]+>/g, '').trim();
      if (t) out.push({ s: ts(m[1]), e: ts(m[2]), t });
    }
  }

  // скачивает и разбирает дорожку целиком; результат кэшируется
  function loadCues(tr) {
    if (!cache.has(tr.uri)) {
      const p = (async () => {
        const pl = await get(tr.uri);
        const segs = pl.split(/\r?\n/).filter(l => l && l[0] !== '#').map(l => new URL(l, tr.uri).href);
        const texts = await Promise.all(segs.map(get));
        const all = [];
        texts.forEach(t => parseVTT(t, all));
        all.sort((a, b) => a.s - b.s || a.e - b.e);
        return all.filter((c, i) => !i || c.s !== all[i - 1].s || c.t !== all[i - 1].t);
      })();
      p.catch(() => cache.delete(tr.uri));
      cache.set(tr.uri, p);
    }
    return cache.get(tr.uri);
  }

  // индекс последнего элемента с s <= t (или -1)
  function bs(arr, t) {
    let lo = 0, hi = arr.length - 1, idx = -1;
    while (lo <= hi) {
      const mid = (lo + hi) >> 1;
      if (arr[mid].s <= t) { idx = mid; lo = mid + 1; } else hi = mid - 1;
    }
    return idx;
  }

  const isSound = t => t.replace(/\[[^\]]*\]|\([^)]*\)|[♪♫#]/g, '').replace(/[\s-]/g, '') === '';

  // реплики -> фразы: выкидываем звуки, склеиваем куски одного предложения
  function buildPhrases(list) {
    const ph = [];
    for (const c of list) {
      if (SKIP_SOUND && isSound(c.t)) continue;
      const last = ph[ph.length - 1];
      if (last && c.s - last.e < MERGE_GAP && !/[.?!…"”♪)\]]$/.test(last.t.trim())) {
        last.e = Math.max(last.e, c.e);
        last.t += '\n' + c.t;
      } else {
        ph.push({ s: c.s, e: c.e, t: c.t });
      }
    }
    return ph;
  }

  const pickRu = () =>
    tracks.find(t => t.name === cfg.track) ||
    tracks.find(t => t.lang === cfg.lang && !/forced/i.test(t.name)) ||
    tracks.find(t => /^ru/i.test(t.lang || ''));

  function current(t) {
    const idx = bs(cues, t);
    const res = [];
    for (let i = idx; i >= 0 && i > idx - 6; i--) if (cues[i].e > t) res.unshift(cues[i].t);
    return res.join('\n');
  }

  /* ---------- статус ---------- */
  const kindOf = s => !s ? 'idle' : /ошибка|не найден/i.test(s) ? 'err' : /…$/.test(s) ? 'load' : 'ok';
  function renderStatus() {
    if (!stEl) return;
    stEl.textContent = '';
    [['RU', ruMsg], ['EN', refMsg]].forEach(([tag, msg]) => {
      const row = el('div', 'st');
      row.append(el('i', 'dot ' + kindOf(msg)), el('b', '', tag), el('span', '', msg || '—'));
      stEl.appendChild(row);
    });
  }
  const setRu = s => { ruMsg = s; renderStatus(); };
  const setRef = s => { refMsg = s; renderStatus(); };

  /* ---------- загрузка дорожек ---------- */
  async function initMaster(url) {
    cues = []; tracks = []; phrases = []; refName = ''; cache.clear();
    setRu('Загружаю список дорожек…'); setRef('');
    try {
      tracks = parseMaster(await get(url), url);
      fillSelect();
      const t = pickRu();
      if (t) await loadTrack(t); else setRu('Русская дорожка не найдена');
      syncRef();
    } catch (e) {
      setRu('Ошибка: ' + e.message + ' — обновите страницу (F5)');
    }
  }

  async function loadTrack(tr) {
    const my = ++loadId;
    cues = [];
    cfg.track = tr.name; save();
    if (selEl) selEl.value = String(tracks.indexOf(tr));
    setRu('Загружаю «' + tr.name + '»…');
    try {
      const c = await loadCues(tr);
      if (my !== loadId) return;
      cues = c;
      setRu('«' + tr.name + '» · реплик ' + cues.length);
    } catch (e) {
      if (my === loadId) setRu('Ошибка: ' + e.message + ' — обновите страницу (F5)');
    }
  }

  // тайминги берём с английской дорожки, которую сейчас выбрал плеер (иначе — первая ENG)
  function syncRef() {
    if (!tracks.length) return;
    let want = null;
    try {
      const sel = getHost().textTracks.selected;
      const t = sel && tracks.find(x => x.name === sel.label);
      if (t && /^en/i.test(t.lang || '')) want = t;
    } catch (e) {}
    if (!want) want = tracks.find(t => /^en/i.test(t.lang || '') && !/forced/i.test(t.name));
    if (!want) { if (!refName) setRef('Английская дорожка не найдена'); return; }
    if (want.name === refName) return;
    refName = want.name;
    const my = ++refId;
    phrases = [];
    setRef('«' + want.name + '» · загружаю…');
    loadCues(want).then(c => {
      if (my !== refId) return;
      phrases = buildPhrases(c);
      setRef('«' + want.name + '» · фраз ' + phrases.length);
    }).catch(e => { if (my === refId) { refName = ''; setRef('Ошибка: ' + e.message); } });
  }

  /* ---------- перемотка по фразам ---------- */
  function seek(t) {
    const h = getHost(), v = getVideo();
    if (!v) return;
    t = Math.max(0, t);
    try { h.currentTime = t; } catch (e) { v.currentTime = t; }
  }

  function jump(dir) {
    const v = getVideo();
    if (!v) return;
    if (!phrases.length) { toast('Нет таймингов фраз'); return; }
    const t = v.currentTime;
    const EPS = LEAD + 0.05;            // чтобы после приземления «текущей» считалась именно эта фраза
    const i = bs(phrases, t + EPS);     // текущая или последняя прозвучавшая фраза
    if (dir > 0) {
      const k = i + 1;
      if (k >= phrases.length) { toast('Конец'); return; }
      seek(phrases[k].s - LEAD);
    } else {
      if (i < 0) { seek(0); return; }
      if (t - phrases[i].s > REPLAY_AFTER) seek(phrases[i].s - LEAD);       // повтор текущей фразы
      else seek(phrases[Math.max(0, i - 1)].s - LEAD);                      // предыдущая фраза
    }
  }

  /* ---------- скорость ---------- */
  const fmtRate = r => (Number.isInteger(r) ? r.toFixed(1) : String(r)) + '×';

  function changeSpeed(dir) {
    const h = getHost(), v = getVideo();
    if (!v) return;
    const cur = (h && h.playbackRate) || v.playbackRate || 1;
    let idx;
    if (dir > 0) {
      idx = SPEEDS.findIndex(s => s > cur + 1e-6);
      if (idx < 0) idx = SPEEDS.length - 1;
    } else {
      idx = -1;
      for (let i = SPEEDS.length - 1; i >= 0; i--) if (SPEEDS[i] < cur - 1e-6) { idx = i; break; }
      if (idx < 0) idx = 0;
    }
    const r = SPEEDS[idx];
    try { h.playbackRate = r; } catch (e) { v.playbackRate = r; }
    toast(fmtRate(r));
  }

  function toast(text) {
    if (!toastEl) return;
    toastEl.textContent = text;
    toastEl.style.opacity = '1';
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => { toastEl.style.opacity = '0'; }, 1000);
  }

  /* ---------- история фраз на паузе ---------- */
  function hideHistory() {
    histVisible = false;
    if (histEl) histEl.style.display = 'none';
  }

  function showHistory() {
    const host = getHost(), v = getVideo();
    if (!host || !v || !histEl || !cfg.hist) return;
    if (!phrases.length) { toast('Нет таймингов фраз'); return; }
    const last = bs(phrases, v.currentTime + 0.05);   // текущая или последняя прозвучавшая фраза
    if (last < 0) return;
    const P = phrases.slice(Math.max(0, last - cfg.histN + 1), last + 1);

    // русские реплики раскладываем по английским фразам (по наибольшему пересечению по времени)
    const ru = P.map(() => []);
    if (cues.length) {
      const from = P[0].s - 1, to = P[P.length - 1].e + 1;
      for (let i = Math.max(0, bs(cues, from - cfg.offset) - 3); i < cues.length; i++) {
        const c = cues[i], cs = c.s + cfg.offset, ce = c.e + cfg.offset;
        if (cs > to) break;
        if (ce < from) continue;
        let best = -1, bo = 0.05;
        P.forEach((p, k) => { const o = Math.min(ce, p.e) - Math.max(cs, p.s); if (o > bo) { bo = o; best = k; } });
        if (best >= 0) ru[best].push(c.t.replace(/\n/g, ' '));
      }
    }

    histEl.textContent = '';
    const wrap = el('div', 'h-wrap');
    P.forEach((p, k) => {
      const item = el('div', 'h-item' + (k === P.length - 1 ? ' cur' : ''));
      item.appendChild(el('div', 'h-en', p.t.replace(/\s*\n\s*/g, ' ')));   // жёсткие переносы из субтитров убираем
      if (ru[k].length) item.appendChild(el('div', 'h-ru', ru[k].join(' ')));
      wrap.appendChild(item);
    });
    histEl.appendChild(wrap);
    histEl.style.display = 'flex';
    histVisible = true;

    // подгоняем размер шрифта, чтобы всё влезло
    const h = host.clientHeight;
    let scale = 1;
    const apply = () => histEl.style.setProperty('--hs', Math.max(11, 26 * h / 600 * scale) + 'px');
    apply();
    while (wrap.offsetHeight > histEl.clientHeight * 0.9 && scale > 0.35) { scale *= 0.9; apply(); }
  }

  // не реагируем на клавиши, когда пользователь печатает или работает с нашей панелью
  // (события из shadow DOM на window приходят с target = #kwds-root)
  const typing = e => {
    const t = e.target;
    return !!(t && (t.isContentEditable || /^(INPUT|TEXTAREA|SELECT)$/.test(t.tagName) ||
      (t.closest && t.closest('#kwds-root'))));
  };

  // пробел: запоминаем состояние до нажатия, после отпускания (плеер к этому моменту переключился) решаем
  window.addEventListener('keydown', e => {
    if (e.code === 'Escape') { hideHistory(); closePanel(); return; }
    if (e.code !== 'Space' || e.repeat || e.ctrlKey || e.metaKey || e.altKey || typing(e)) return;
    const v = getVideo();
    spaceBefore = v ? v.paused : null;
  }, true);
  window.addEventListener('keyup', e => {
    if (e.code !== 'Space' || typing(e)) return;
    const v = getVideo(), before = spaceBefore;
    spaceBefore = null;
    if (!v || before === null) return;
    setTimeout(() => {
      if (v.paused && !before) showHistory();   // поставили на паузу пробелом
      else if (!v.paused) hideHistory();        // сняли с паузы
    }, 150);
  }, true);

  // клавиши: , . — фразы; Shift+, Shift+. — скорость (по физическим клавишам, раскладка не важна)
  window.addEventListener('keydown', e => {
    if (e.code !== 'Comma' && e.code !== 'Period') return;
    if (e.ctrlKey || e.metaKey || e.altKey) return;
    const t = e.target;
    if (t && (t.isContentEditable || /^(INPUT|TEXTAREA|SELECT)$/.test(t.tagName))) return;
    if (!getVideo()) return;
    e.preventDefault();
    e.stopImmediatePropagation();
    const dir = e.code === 'Period' ? 1 : -1;
    if (e.shiftKey) changeSpeed(dir); else jump(dir);
  }, true);

  // клик вне панели закрывает её
  window.addEventListener('pointerdown', e => {
    if (panelOpen && rootEl && !e.composedPath().includes(rootEl)) closePanel();
  }, true);

  /* ---------- интерфейс ---------- */
  const CSS = `
    :host{all:initial}
    *{box-sizing:border-box;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,system-ui,sans-serif}
    button{font:inherit;color:inherit;border:0;background:none;cursor:pointer;padding:0;margin:0}

    /* вторые субтитры */
    #sub{position:absolute;z-index:0;left:5%;right:5%;text-align:center;white-space:pre-line;color:#ffe08a;
      font-weight:600;line-height:1.25;text-shadow:0 0 4px #000,0 0 4px #000,1px 1px 2px #000;display:none}

    /* история на паузе */
    #hist{position:absolute;z-index:1;inset:0;display:none;flex-direction:column;justify-content:center;
      padding:3% 6%;background:rgba(0,0,0,.84);overflow:hidden;pointer-events:none}
    .h-wrap{font-size:var(--hs,26px);display:flex;flex-direction:column;gap:.9em}
    .h-item{opacity:.72;border-left:3px solid transparent;padding-left:.6em}
    .h-item.cur{opacity:1;border-left-color:#ffe08a}
    .h-en{color:#fff;font-weight:600;line-height:1.25}
    .h-ru{color:#ffe08a;font-size:.78em;line-height:1.25;margin-top:.25em}

    /* подсказка скорости */
    #toast{position:absolute;z-index:3;top:12%;left:50%;transform:translateX(-50%);padding:6px 18px;border-radius:12px;
      background:rgba(0,0,0,.72);color:#fff;font-size:32px;font-weight:700;opacity:0;transition:opacity .25s;pointer-events:none}

    /* кнопка */
    #btn{position:absolute;z-index:4;top:12px;right:12px;pointer-events:auto;display:flex;align-items:center;gap:6px;
      height:32px;padding:0 13px 0 10px;border-radius:16px;background:rgba(20,20,24,.55);
      -webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px);border:1px solid rgba(255,255,255,.14);
      color:#ffe08a;font-size:13px;font-weight:700;letter-spacing:.4px;opacity:.55;transition:opacity .15s,background .15s}
    #btn:hover,#btn.on{opacity:1;background:rgba(20,20,24,.82)}
    #btn svg{display:block}

    /* панель */
    #panel{position:absolute;z-index:5;top:56px;right:12px;width:min(332px,calc(100% - 24px));
      max-height:calc(100% - 68px);overflow:auto;pointer-events:none;opacity:0;
      transform:translateY(-6px) scale(.985);transform-origin:top right;transition:opacity .16s,transform .16s;
      background:rgba(24,24,29,.9);-webkit-backdrop-filter:blur(18px) saturate(1.2);backdrop-filter:blur(18px) saturate(1.2);
      border:1px solid rgba(255,255,255,.12);border-radius:16px;box-shadow:0 18px 50px rgba(0,0,0,.55);
      color:#ececf1;font-size:13px;line-height:1.35;padding:14px 14px 12px;scrollbar-width:thin}
    #panel.open{opacity:1;transform:none;pointer-events:auto}
    .hd{display:flex;align-items:center;justify-content:space-between}
    .hd .t{font-size:14px;font-weight:650;display:flex;flex-direction:column}
    .hd .t small{font-size:11px;font-weight:400;opacity:.5;margin-top:1px}
    .x{width:26px;height:26px;border-radius:8px;display:grid;place-items:center;opacity:.6;font-size:15px}
    .x:hover{opacity:1;background:rgba(255,255,255,.09)}
    .sec{margin-top:14px}
    .sec>h4{margin:0 0 6px 2px;font-size:10.5px;font-weight:600;letter-spacing:.09em;text-transform:uppercase;opacity:.45}
    .card{background:rgba(255,255,255,.05);border-radius:12px;padding:2px 12px}
    .row{display:flex;align-items:center;justify-content:space-between;gap:10px;min-height:40px}
    .row+.row{border-top:1px solid rgba(255,255,255,.07)}
    .lbl{flex:1}

    /* переключатель */
    .sw{position:relative;width:38px;height:22px;flex:none}
    .sw input{position:absolute;inset:0;width:100%;height:100%;opacity:0;margin:0;cursor:pointer;z-index:1}
    .sw i{position:absolute;inset:0;border-radius:11px;background:rgba(255,255,255,.2);transition:background .18s}
    .sw i::after{content:"";position:absolute;top:2px;left:2px;width:18px;height:18px;border-radius:50%;background:#fff;
      box-shadow:0 1px 3px rgba(0,0,0,.4);transition:transform .18s}
    .sw input:checked+i{background:#e9b82c}
    .sw input:checked+i::after{transform:translateX(16px)}
    .sw input:focus-visible+i{outline:2px solid #ffe08a;outline-offset:2px}

    /* выбор дорожки */
    select{width:100%;height:36px;appearance:none;-webkit-appearance:none;border-radius:10px;
      border:1px solid rgba(255,255,255,.12);padding:0 30px 0 12px;font-size:13px;color:#ececf1;cursor:pointer;
      background:rgba(255,255,255,.06) url("data:image/svg+xml;utf8,<svg xmlns='http://www.w3.org/2000/svg' width='12' height='12' viewBox='0 0 24 24' fill='none' stroke='%23aaaaaa' stroke-width='3' stroke-linecap='round' stroke-linejoin='round'><path d='M6 9l6 6 6-6'/></svg>") no-repeat right 11px center}
    select:focus-visible{outline:2px solid #ffe08a;outline-offset:1px}
    select option{background:#232328;color:#eee}

    /* степпер */
    .step{display:flex;align-items:center;height:28px;border-radius:9px;background:rgba(255,255,255,.07);overflow:hidden;flex:none}
    .step button{width:30px;height:100%;display:grid;place-items:center;font-size:15px;opacity:.85}
    .step button:hover{background:rgba(255,255,255,.13)}
    .step button:active{background:rgba(255,255,255,.2)}
    .step output{min-width:58px;text-align:center;font-size:12.5px;font-weight:600;font-variant-numeric:tabular-nums}
    .step output[data-a]{cursor:pointer}
    .step output[data-a]:hover{color:#ffe08a}

    /* статус */
    .st{display:flex;align-items:center;gap:8px;min-height:32px;font-size:12px}
    .st+.st{border-top:1px solid rgba(255,255,255,.07)}
    .st b{width:20px;font-size:10.5px;font-weight:700;opacity:.55}
    .st span{flex:1;min-width:0;opacity:.88;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
    .dot{width:7px;height:7px;border-radius:50%;background:#777;flex:none}
    .dot.ok{background:#4ade80}.dot.load{background:#fbbf24;animation:pulse 1s infinite}.dot.err{background:#f87171}
    @keyframes pulse{50%{opacity:.3}}

    /* горячие клавиши */
    .keys{display:grid;grid-template-columns:auto 1fr;gap:8px 12px;align-items:center;font-size:12px}
    .keys span{opacity:.8}
    .kg{display:flex;gap:4px}
    kbd{display:inline-block;min-width:22px;padding:2px 6px;text-align:center;border-radius:6px;
      background:rgba(255,255,255,.1);border:1px solid rgba(255,255,255,.14);border-bottom-width:2px;
      font:600 11.5px ui-monospace,SFMono-Regular,Menlo,monospace;color:#f4f4f6}
  `;

  const HTML = `
    <div id="sub"></div>
    <div id="hist"></div>
    <div id="toast"></div>
    <button id="btn" type="button" title="Двойные субтитры">
      <svg width="17" height="17" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"
           stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="5" width="18" height="14" rx="3"/>
        <path d="M7 11h4M7 15h2M14 11h3M12 15h5"/></svg>
      <span>RU</span>
    </button>
    <div id="panel" role="dialog" aria-label="Двойные субтитры">
      <div class="hd">
        <div class="t">Двойные субтитры<small>русский перевод вторым слоем</small></div>
        <button class="x" type="button" data-a="close" title="Закрыть">✕</button>
      </div>

      <div class="sec"><h4>Показ</h4>
        <div class="card">
          <div class="row"><span class="lbl">Русские субтитры</span>
            <label class="sw"><input type="checkbox" id="c-on"><i></i></label></div>
          <div class="row"><span class="lbl">История на паузе (пробел)</span>
            <label class="sw"><input type="checkbox" id="c-hist"><i></i></label></div>
        </div>
      </div>

      <div class="sec"><h4>Русская дорожка</h4><select id="sel"></select></div>

      <div class="sec"><h4>Настройка</h4>
        <div class="card">
          <div class="row"><span class="lbl">Сдвиг</span>
            <div class="step"><button type="button" data-a="off-">−</button>
              <output id="v-off" data-a="off0" title="Нажмите, чтобы сбросить"></output>
              <button type="button" data-a="off+">+</button></div></div>
          <div class="row"><span class="lbl">Размер</span>
            <div class="step"><button type="button" data-a="size-">−</button><output id="v-size"></output>
              <button type="button" data-a="size+">+</button></div></div>
          <div class="row"><span class="lbl">Высота над низом</span>
            <div class="step"><button type="button" data-a="pos-">−</button><output id="v-pos"></output>
              <button type="button" data-a="pos+">+</button></div></div>
          <div class="row"><span class="lbl">Фраз в истории</span>
            <div class="step"><button type="button" data-a="hn-">−</button><output id="v-hn"></output>
              <button type="button" data-a="hn+">+</button></div></div>
        </div>
      </div>

      <div class="sec"><h4>Дорожки</h4><div class="card" id="st"></div></div>

      <div class="sec"><h4>Горячие клавиши</h4>
        <div class="card" style="padding:10px 12px"><div class="keys">
          <div class="kg"><kbd>,</kbd><kbd>.</kbd></div><span>Фраза назад / вперёд</span>
          <div class="kg"><kbd>⇧ ,</kbd><kbd>⇧ .</kbd></div><span>Скорость − / +</span>
          <div class="kg"><kbd>Пробел</kbd></div><span>Пауза и последние фразы</span>
          <div class="kg"><kbd>Esc</kbd></div><span>Закрыть историю / панель</span>
        </div></div>
      </div>
    </div>`;

  function openPanel() { panelOpen = true; panelEl.classList.add('open'); btnEl.classList.add('on'); }
  function closePanel() {
    panelOpen = false;
    if (panelEl) panelEl.classList.remove('open');
    if (btnEl) btnEl.classList.remove('on');
  }

  function fillSelect() {
    if (!selEl) return;
    selEl.textContent = '';
    tracks.forEach((t, i) => {
      const o = document.createElement('option');
      o.value = String(i);
      o.textContent = t.name;
      selEl.appendChild(o);
    });
    const t = pickRu();
    if (t) selEl.value = String(tracks.indexOf(t));
  }

  function showValues() {
    if (!vOff) return;
    vOff.textContent = (cfg.offset > 0 ? '+' : '') + cfg.offset.toFixed(1) + ' с';
    vSize.textContent = String(cfg.size);
    vPos.textContent = cfg.pos + '%';
    vHn.textContent = String(cfg.histN);
  }

  function mount(host) {
    if (host.querySelector('#kwds-root')) return;
    if (getComputedStyle(host).position === 'static') host.style.position = 'relative';

    rootEl = document.createElement('div');
    rootEl.id = 'kwds-root';
    // стили сайта в shadow DOM не проникают; сам хост задаём инлайном
    rootEl.style.cssText = 'all:initial;display:block;position:absolute;inset:0;pointer-events:none;z-index:9999';
    sh = rootEl.attachShadow({ mode: 'open' });
    sh.innerHTML = '<style>' + CSS + '</style>' + HTML;
    host.appendChild(rootEl);

    const $ = s => sh.querySelector(s);
    subEl = $('#sub'); histEl = $('#hist'); toastEl = $('#toast');
    btnEl = $('#btn'); panelEl = $('#panel'); selEl = $('#sel'); stEl = $('#st');
    vOff = $('#v-off'); vSize = $('#v-size'); vPos = $('#v-pos'); vHn = $('#v-hn');
    const onEl = $('#c-on'), histOnEl = $('#c-hist');
    onEl.checked = cfg.on;
    histOnEl.checked = cfg.hist;

    // клики и клавиши в нашем интерфейсе не должны управлять плеером
    const isolate = n => ['click', 'dblclick', 'keydown', 'keyup', 'pointerdown', 'mousedown', 'touchstart', 'wheel']
      .forEach(ev => n.addEventListener(ev, e => e.stopPropagation()));
    isolate(panelEl); isolate(btnEl);

    btnEl.addEventListener('click', () => { if (panelOpen) closePanel(); else openPanel(); });
    onEl.addEventListener('change', () => { cfg.on = onEl.checked; save(); });
    histOnEl.addEventListener('change', () => { cfg.hist = histOnEl.checked; save(); if (!cfg.hist) hideHistory(); });
    selEl.addEventListener('change', () => { const t = tracks[+selEl.value]; if (t) loadTrack(t); });
    panelEl.addEventListener('click', e => {
      const b = e.target.closest && e.target.closest('[data-a]');
      const a = b && b.dataset.a;
      if (!a) return;
      if (a === 'close') { closePanel(); return; }
      if (a === 'off-') cfg.offset = Math.round((cfg.offset - 0.5) * 10) / 10;
      if (a === 'off+') cfg.offset = Math.round((cfg.offset + 0.5) * 10) / 10;
      if (a === 'off0') cfg.offset = 0;
      if (a === 'size-') cfg.size = Math.max(10, cfg.size - 2);
      if (a === 'size+') cfg.size = Math.min(60, cfg.size + 2);
      if (a === 'pos-') cfg.pos = Math.max(0, cfg.pos - 2);
      if (a === 'pos+') cfg.pos = Math.min(80, cfg.pos + 2);
      if (a === 'hn-') cfg.histN = Math.max(1, cfg.histN - 1);
      if (a === 'hn+') cfg.histN = Math.min(20, cfg.histN + 1);
      save(); showValues(); styleKey = '';
    });

    if (tracks.length) fillSelect();
    showValues();
    renderStatus();
    panelOpen = false;
  }

  /* ---------- главный цикл ---------- */
  function frame() {
    requestAnimationFrame(frame);
    const host = getHost();
    const v = host && host.querySelector('video');
    if (!v || !subEl || !subEl.isConnected) return;

    const txt = cfg.on && cues.length && !histVisible ? current(v.currentTime - cfg.offset) : '';
    if (txt !== shown) {
      shown = txt;
      subEl.textContent = txt;
      subEl.style.display = txt ? 'block' : 'none';
    }
    const key = cfg.size + '|' + cfg.pos + '|' + host.clientHeight;
    if (key !== styleKey) {
      styleKey = key;
      subEl.style.fontSize = Math.max(12, cfg.size * host.clientHeight / 600) + 'px';
      subEl.style.bottom = cfg.pos + '%';
    }
  }

  setInterval(() => {
    const host = getHost();
    if (!host) return;
    mount(host);
    const vid = getVideo();
    if (vid && vid !== boundVideo) {          // любое возобновление или перемотка закрывает историю
      boundVideo = vid;
      vid.addEventListener('play', hideHistory);
      vid.addEventListener('seeking', hideHistory);
    }
    if (masterUrl && masterUrl !== curMaster) { curMaster = masterUrl; initMaster(masterUrl); }
    else if (!masterUrl) setRu('Манифест не найден — обновите страницу (F5)');
    else syncRef();
  }, 1000);

  requestAnimationFrame(frame);
})();
