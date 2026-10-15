/* ============================================================
   Naralingo Graeca — 古典ギリシア語の自習アプリ（ひとり用）
   ・ログイン：MORITA7k3q / shika（ID の大文字・小文字は区別しない。パスワードはハッシュだけを置く）
   ・記録：この端末の localStorage。config.js に Apps Script の URL を書けば、端末どうしで同期
   ・画面：#/（ホーム） #/day/N/step（レッスン） #/review（復習） #/tables（文法表）
   ・復習カード（間隔反復）：1段目→翌日 / 2→3日後 / 3→1週間後 / 4→2週間後 / 5→1か月後 / 6＝定着（2か月後）
   ============================================================ */
(function () {
"use strict";
const CFG = window.GRK_CONFIG || {};
const COURSE = window.COURSE;
const LOGIN_HASH = "d708a9d7fc86722a5a5d1aa9d36118ed5adbbbfedd4d2296c0d3c92d21d6e192";
const LOGIN_KEY = "grkLogin", PREF_KEY = "grkPrefs";
const INT = [0, 1, 3, 7, 14, 30, 60];
const STEPS = [["intro", "解説"], ["vocab", "単語"], ["drill", "練習"], ["read", "読解"], ["test", "テスト"]];
const PASS = 0.8, ROUND = 10, REVIEW_MAX = 30;
const $ = (s, r) => (r || document).querySelector(s);
const $$ = (s, r) => Array.prototype.slice.call((r || document).querySelectorAll(s));
const app = () => $("#app");
function esc(s) { return String(s == null ? "" : s).replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c])); }
function shuffle(a) { a = a.slice(); for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; }
function today() { return Math.floor((Date.now() + 9 * 3600e3) / 864e5); }        // 日本時間の日の番号
function dstr(n) { return new Date(n * 864e5).toISOString().slice(0, 10); }
function lsGet(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }
function lsSet(k, v) { try { localStorage.setItem(k, v); } catch (e) {} }
function lsDel(k) { try { localStorage.removeItem(k); } catch (e) {} }
function jget(k, d) { try { const v = JSON.parse(lsGet(k)); return v == null ? d : v; } catch (e) { return d; } }
function fmtDur(ms) { const m = Math.round((ms || 0) / 60000); return m < 60 ? m + "分" : Math.floor(m / 60) + "時間" + (m % 60 ? (m % 60) + "分" : ""); }
async function sha256(s) {
  const b = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(s));
  return Array.prototype.map.call(new Uint8Array(b), x => ("0" + x.toString(16)).slice(-2)).join("");
}
/* ギリシア文字の語を <span class="g"> で包む（書体を変えるため）。タグの中は触らない */
function gk(h) {
  return String(h == null ? "" : h).replace(/(<[^>]+>)|([Ͱ-Ͽἀ-῿][Ͱ-Ͽἀ-῿̀-ͯ]*)/g,
    (m, tag, w) => tag ? tag : '<span class="g">' + w + '</span>');
}

/* ============================================================
   ギリシア文字の入力と照合
   ============================================================ */
const GK = (function () {
  const MAP = { a: "α", b: "β", g: "γ", d: "δ", e: "ε", z: "ζ", h: "η", q: "θ", i: "ι", k: "κ", l: "λ", m: "μ", n: "ν", c: "ξ", o: "ο", p: "π", r: "ρ", s: "σ", t: "τ", u: "υ", f: "φ", x: "χ", y: "ψ", w: "ω" };
  const MARK = { ")": "̓", "(": "̔", "/": "́", "\\": "̀", "=": "͂", "|": "ͅ", "j": "ͅ", "+": "̈" };
  const CLS = { "̓": 1, "̔": 1, "̈": 2, "́": 3, "̀": 3, "͂": 3, "ͅ": 4 };
  const VOW = "αεηιουωΑΕΗΙΟΥΩ";
  function ok(b, m) {
    if (CLS[m] === 1 && "ρΡ".indexOf(b) >= 0) return true;
    if (CLS[m] === 4) return "αηωΑΗΩ".indexOf(b) >= 0;
    if (CLS[m] === 3 && m === "͂") return "αηιυωΑΗΙΥΩ".indexOf(b) >= 0;
    return VOW.indexOf(b) >= 0;
  }
  /* ローマ字（ベータコード風）→ ギリシア文字。記号は直前の母音に付く */
  function conv(str) {
    const out = [];
    function attach(m) {
      const c = out[out.length - 1];
      if (!c || !ok(c.b, m)) return;
      if (CLS[m] == null) { c.m.push(m); return; }
      c.m = c.m.filter(x => CLS[x] !== CLS[m]); c.m.push(m);
    }
    for (const ch of String(str).normalize("NFD")) {
      if (/[̀-ͯ]/.test(ch)) { const c = out[out.length - 1]; if (c) attach(ch); continue; }
      if (MARK[ch] !== undefined) { attach(MARK[ch]); continue; }
      const lo = ch.toLowerCase();
      if (MAP[lo]) { out.push({ b: ch === lo ? MAP[lo] : MAP[lo].toUpperCase(), m: [] }); continue; }
      out.push({ b: ch, m: [] });
    }
    return out.map(c => (c.b + c.m.slice().sort((x, y) => (CLS[x] || 9) - (CLS[y] || 9)).join("")).normalize("NFC")).join("");
  }
  function sigma(s) { return s.replace(/σ(?![\p{L}\p{M}])/gu, "ς").replace(/ς(?=[\p{L}])/gu, "σ"); }
  /* 照合用に整える。mode 2＝記号まで、1＝ι下書きだけ残す、0＝記号をすべて落とす */
  function nrm(s, mode) {
    s = String(s == null ? "" : s).normalize("NFD").toLowerCase()
      .replace(/[’'ʼ᾿᾽]/g, "'").replace(/[.,;:!?;··]/g, " ")
      .replace(/ς/g, "σ").replace(/̀/g, "́").replace(/\s+/g, " ").trim();
    if (mode < 2) s = s.replace(/[̀-̈́͆-ͯ]/g, "");
    if (mode < 1) s = s.replace(/ͅ/g, "");
    return s;
  }
  /* 2＝完全一致 1＝アクセント・気息だけちがう -1＝ι下書きだけちがう 0＝ちがう */
  function judge(input, answers) {
    if (answers.some(a => nrm(input, 2) === nrm(a, 2))) return 2;
    if (answers.some(a => nrm(input, 1) === nrm(a, 1))) return 1;
    if (answers.some(a => nrm(input, 0) === nrm(a, 0))) return -1;
    return 0;
  }
  function key(s) { return String(s).normalize("NFD").replace(/̀/g, "́").normalize("NFC"); }
  function attachInput(el) {
    el.setAttribute("autocomplete", "off"); el.setAttribute("autocapitalize", "off"); el.setAttribute("spellcheck", "false"); el.setAttribute("autocorrect", "off");
    function run(force) {
      if (!force && !prefs().conv) { el.value = sigma(el.value.normalize("NFC")); return; }
      const v = el.value, pos = el.selectionStart == null ? v.length : el.selectionStart;
      const a = conv(v.slice(0, pos)), b = conv(v.slice(pos)), nv = sigma(a + b);
      if (nv !== v) { el.value = nv; try { el.setSelectionRange(a.length, a.length); } catch (e) {} }
    }
    el.addEventListener("input", e => { if (e.isComposing) return; run(false); });
    el.addEventListener("compositionend", () => run(false));
    el._gkRun = run;
  }
  /* 記号ボタン：カーソルの前の文字に付ける */
  function insertMark(el, sym) {
    const v = el.value, p = el.selectionStart == null ? v.length : el.selectionStart;
    el.value = v.slice(0, p) + sym + v.slice(p);
    try { el.setSelectionRange(p + 1, p + 1); } catch (e) {}
    el._gkRun(true); el.focus();
  }
  return { conv, sigma, nrm, judge, key, attachInput, insertMark };
})();

/* ============================================================
   設定（この端末だけ）
   ============================================================ */
let prefCache = null;
function prefs() {
  if (!prefCache) { prefCache = jget(PREF_KEY, {}) || {}; if (prefCache.conv === undefined) prefCache.conv = true; }
  return prefCache;
}
function setPref(k, v) { prefs()[k] = v; lsSet(PREF_KEY, JSON.stringify(prefCache)); }

/* ============================================================
   ログイン
   ============================================================ */
let user = jget(LOGIN_KEY, null) || (function () { try { return JSON.parse(sessionStorage.getItem(LOGIN_KEY)); } catch (e) { return null; } })();
if (user && user.ver !== 2) user = null;   // ID を変える前のログイン情報は使わない（同期の鍵が変わったので、ログインし直す）
async function login(id, pw, remember) {
  id = String(id || "").normalize("NFKC").trim().toLowerCase(); pw = String(pw || "").normalize("NFKC").trim();
  const h = await sha256("naralingo-greek:login:" + id + ":" + pw);
  if (h !== LOGIN_HASH) return false;
  const sk = await sha256("naralingo-greek:sync:" + id + ":" + pw);
  user = { id: "MORITA", name: "森田", sk, ver: 2 };   // 記録の保存先（grk_v1_MORITA）は ID を変えても同じ
  const rec = JSON.stringify(user);
  if (remember) lsSet(LOGIN_KEY, rec); else { try { sessionStorage.setItem(LOGIN_KEY, rec); } catch (e) {} }
  store = null; S();
  return true;
}
function logout() { flushTime(); save(true); user = null; store = null; lsDel(LOGIN_KEY); try { sessionStorage.removeItem(LOGIN_KEY); } catch (e) {} }

/* ============================================================
   記録
   ============================================================ */
let store = null;
function SKEY() { return "grk_v1_" + (user ? user.id : "GUEST"); }
function blank() { return { v: 1, u: 0, days: [], ms: 0, ans: 0, cor: 0, les: {}, it: {}, cards: {}, log: {}, wel: 0 }; }
function S() {
  if (!store) { store = Object.assign(blank(), jget(SKEY(), {}) || {}); }
  return store;
}
let pushTimer = 0;
function save(noPush) {
  const s = S(); s.u = Date.now();
  lsSet(SKEY(), JSON.stringify(s));
  if (!noPush && CFG.SCRIPT_URL) { clearTimeout(pushTimer); pushTimer = setTimeout(() => sync(), 8000); }
}
function les(n) { const s = S(); return s.les[n] || (s.les[n] = { st: {} }); }
function logDay() { const s = S(), k = dstr(today()); return s.log[k] || (s.log[k] = { ms: 0, a: 0, c: 0 }); }
function markStudy() { const s = S(), t = dstr(today()); if (s.days.indexOf(t) < 0) { s.days.push(t); s.days.sort(); if (s.days.length > 500) s.days = s.days.slice(-500); } }
function countAns(ok) { const s = S(), l = logDay(); s.ans++; l.a++; if (ok) { s.cor++; l.c++; } markStudy(); }
/* 継続：1日あいてもつながる（2日あくと切れる） */
function chain() {
  const set = {}; S().days.forEach(d => set[d] = 1);
  const t = today(); let cur = null, gap = -1;
  for (let g = 0; g <= 2; g++) if (set[dstr(t - g)]) { cur = t - g; gap = g; break; }
  let n = 0;
  while (cur != null) { n++; cur = set[dstr(cur - 1)] ? cur - 1 : set[dstr(cur - 2)] ? cur - 2 : null; }
  return { n, gap, doneToday: gap === 0, risk: gap === 2 };
}
/* 勉強時間：操作してから60秒以内のあいだ、学習画面にいた時間だけ数える */
let lastAct = Date.now(), pendMs = 0, studyView = false;
["pointerdown", "keydown", "input", "scroll", "touchstart"].forEach(ev => document.addEventListener(ev, () => { lastAct = Date.now(); }, { passive: true, capture: true }));
setInterval(() => {
  if (!user || !studyView || document.hidden || Date.now() - lastAct > 60000) return;
  pendMs += 5000; if (pendMs >= 30000) flushTime(true);
}, 5000);
function flushTime(doSave) {
  if (!pendMs || !user) return;
  const s = S(); s.ms += pendMs; logDay().ms += pendMs; pendMs = 0;
  if (doSave) save();
}
window.addEventListener("pagehide", () => { flushTime(); if (user) save(true); });

/* ---- 同期（Apps Script）：端末とサーバーの記録を合わせる ---- */
function merge(a, b) {
  if (!b || typeof b !== "object") return a;
  if (!a) return b;
  const o = blank();
  const set = {}; (a.days || []).concat(b.days || []).forEach(d => set[d] = 1); o.days = Object.keys(set).sort().slice(-500);
  ["ms", "ans", "cor", "wel"].forEach(k => o[k] = Math.max(a[k] || 0, b[k] || 0));
  o.u = Math.max(a.u || 0, b.u || 0);
  const ks = (x, y) => Object.keys(Object.assign({}, x || {}, y || {}));
  ks(a.les, b.les).forEach(n => {
    const x = (a.les || {})[n] || { st: {} }, y = (b.les || {})[n] || { st: {} }, z = { st: {} };
    ks(x.st, y.st).forEach(k => { const p = x.st[k], q = y.st[k]; z.st[k] = p && q ? Math.min(p, q) : (p || q); });
    z.best = Math.max(x.best || 0, y.best || 0);
    if (x.pass || y.pass) z.pass = x.pass && y.pass ? Math.min(x.pass, y.pass) : (x.pass || y.pass);
    o.les[n] = z;
  });
  ks(a.it, b.it).forEach(k => { const p = (a.it || {})[k], q = (b.it || {})[k]; o.it[k] = !p ? q : !q ? p : ((q.u || 0) > (p.u || 0) ? q : p); });
  ks(a.cards, b.cards).forEach(k => { const p = (a.cards || {})[k], q = (b.cards || {})[k]; o.cards[k] = !p ? q : !q ? p : ((q.u || 0) > (p.u || 0) ? q : p); });
  ks(a.log, b.log).forEach(k => { const p = (a.log || {})[k] || {}, q = (b.log || {})[k] || {}; o.log[k] = { ms: Math.max(p.ms || 0, q.ms || 0), a: Math.max(p.a || 0, q.a || 0), c: Math.max(p.c || 0, q.c || 0) }; });
  return o;
}
let syncing = false, syncState = { at: 0, ok: null, msg: "" };
async function call(action, extra) {
  const ctl = new AbortController(), tm = setTimeout(() => ctl.abort(), 25000);
  try {
    const r = await fetch(CFG.SCRIPT_URL, { method: "POST", signal: ctl.signal, body: JSON.stringify(Object.assign({ action, key: user.sk }, extra || {})) });
    return await r.json();
  } finally { clearTimeout(tm); }
}
async function sync() {
  if (!CFG.SCRIPT_URL || !user || !user.sk || syncing) return;
  syncing = true; flushTime();
  try {
    const r = await call("get");
    if (!r.ok) throw new Error(r.error || "error");
    const local = S(), m = merge(local, r.data);
    const ms = JSON.stringify(m);
    if (ms !== JSON.stringify(local)) { store = m; lsSet(SKEY(), ms); }
    if (!r.data || ms !== JSON.stringify(r.data)) { const w = await call("put", { data: m }); if (!w.ok) throw new Error(w.error || "error"); }
    syncState = { at: Date.now(), ok: true, msg: "" };
  } catch (e) { syncState = { at: Date.now(), ok: false, msg: String(e && e.message || e) }; }
  syncing = false;
  const el = $("#syncSt"); if (el) el.innerHTML = syncHTML();
}
function syncHTML() {
  if (!CFG.SCRIPT_URL) return "同期はオフ（config.js に URL を書くとオン）。記録はこの端末だけ。";
  if (syncing) return "同期中…";
  if (syncState.ok === null) return "まだ同期していない";
  const t = new Date(syncState.at).toLocaleTimeString("ja-JP", { hour: "2-digit", minute: "2-digit" });
  return syncState.ok ? "同期済み（" + t + "）" : '<span class="warn">同期できなかった（' + esc(syncState.msg) + "）</span>";
}

/* ============================================================
   復習カード
   ============================================================ */
const CARD = {};
const DAYS = COURSE.days;
function dayOf(n) { return DAYS[n - 1]; }
(function build() {
  COURSE.alpha.forEach(a => CARD["L:" + a[2]] = { kind: "letter", day: 1, a });
  DAYS.forEach(d => {
    (d.vocab || []).forEach(w => CARD["V:" + d.n + ":" + w.g] = { kind: "vocab", day: d.n, w });
    (d.cards || []).forEach(pid => {
      const p = COURSE.par[pid];
      if (p.kind === "v") p.f.forEach((f, i) => CARD["F:" + pid + ":" + i] = { kind: "form", day: d.n, p, f, lab: ["1人称・単数", "2人称・単数", "3人称・単数", "1人称・複数", "2人称・複数", "3人称・複数"][i] });
      else ["sg", "pl"].forEach(nb => p[nb].forEach((f, i) => CARD["F:" + pid + ":" + nb + i] = { kind: "form", day: d.n, p, f, lab: ["主格", "属格", "与格", "対格"][i] + "・" + (nb === "sg" ? "単数" : "複数") }));
    });
    if (d.read && d.read.kind === "sents") d.read.items.forEach((s, i) => CARD["S:" + d.n + ":" + i] = { kind: "sent", day: d.n, g: s[0], ja: s[1] });
  });
})();
function addCards(pred) {
  const s = S(), t = today(); let n = 0;
  Object.keys(CARD).forEach(id => { if (!s.cards[id] && pred(id, CARD[id])) { s.cards[id] = { l: 1, d: t + 1, w: 0, n: 0, u: Date.now() }; n++; } });
  if (n) save();
  return n;
}
function dueIds() { const s = S(), t = today(); return Object.keys(s.cards).filter(id => CARD[id] && s.cards[id].d <= t); }
function gradeCard(id, ok) {
  const c = S().cards[id]; if (!c) return;
  const t = today(); c.n++; c.u = Date.now();
  if (ok) { if (c.d <= t) { c.l = Math.min(6, c.l + 1); c.d = t + INT[c.l]; } }
  else { c.l = 1; c.d = t + 1; c.w++; }
}
function inDays(n) { return n <= 0 ? "今日" : n === 1 ? "明日" : n < 7 ? n + "日後" : n < 30 ? Math.round(n / 7) + "週間後" : Math.round(n / 30) + "か月後"; }

/* カード → 問題 */
const ALL_VOCAB = () => Object.keys(CARD).filter(k => CARD[k].kind === "vocab").map(k => CARD[k].w);
function pick4(a, pool) { return [a].concat(shuffle(pool.filter(x => x !== a)).slice(0, 3)); }
function vocabChoice(w, pool) {
  const ja = pick4(w.ja, (pool || ALL_VOCAB()).map(x => x.ja).filter((x, i, ar) => ar.indexOf(x) === i));
  return { t: "c", q: '<span class="big">' + w.g + '</span><div class="qsub">' + esc(w.h || "") + '</div>', a: w.ja, o: ja, ex: (w.note ? w.note : "") };
}
function cardItem(id) {
  const c = CARD[id], st = S().cards[id], l = st ? st.l : 1;
  let it;
  if (c.kind === "letter") {
    const a = c.a, A = COURSE.alpha, r = l <= 2 ? 0 : Math.floor(Math.random() * 3);
    if (r === 0) it = { t: "c", q: '<span class="big">' + a[1] + '</span> の名前は？', a: a[2], o: pick4(a[2], A.map(x => x[2])), ex: a[1] + " ＝ " + a[2] + "（" + a[3] + "）" };
    else if (r === 1) it = { t: "c", q: '<span class="big">' + a[1] + '</span> の音は？', a: a[3], o: pick4(a[3], A.map(x => x[3])), ex: a[4] };
    else it = { t: "c", q: '大文字 <span class="big">' + a[0] + '</span> の小文字は？', a: a[1], o: pick4(a[1], A.map(x => x[1])), ex: a[0] + " → " + a[1] };
  } else if (c.kind === "vocab") {
    const w = c.w;
    if (l <= 2) it = vocabChoice(w);
    else it = { t: "w", q: "「" + esc(w.ja) + "」をギリシア語で" + (l === 3 ? '<div class="qsub">ヒント：' + esc(w.g.normalize("NFD").replace(/[̀-ͯ]/g, "").charAt(0)) + "…</div>" : ""), a: w.a || [w.g], ex: w.g + (w.h ? "（" + w.h + "）" : "") };
  } else if (c.kind === "form") {
    const p = c.p, q = p.lemma + "（" + p.ja + "）の <b>" + c.lab + "</b>";
    const all = (p.kind === "v" ? p.f : p.sg.concat(p.pl)).filter((x, i, ar) => ar.indexOf(x) === i);
    if (l <= 1) it = { t: "c", q, a: c.f, o: pick4(c.f, all), ex: tableText(p) };
    else it = { t: "w", q, a: [c.f], ex: tableText(p) };
  } else it = { t: "s", g: c.g, ja: c.ja };
  it.cid = id; it.id = "c:" + id;
  return it;
}
function tableText(p) { return p.kind === "v" ? p.f.join(" ") : p.sg.join(" ") + " | " + p.pl.join(" "); }

/* ============================================================
   画面の部品
   ============================================================ */
const DEER = '<svg width="SZ" height="SZ" aria-hidden="true" viewBox="0 0 32 32" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"><path d="M11.5 9.5C9.6 7.3 9.2 5.1 10 2.8M10.2 5.9 7.4 4.6M12.6 9.2c-.6-1.8-.1-3.4 1-4.6"/><path d="M20.5 9.5c1.9-2.2 2.3-4.4 1.5-6.7M21.8 5.9l2.8-1.3M19.4 9.2c.6-1.8.1-3.4-1-4.6"/><path d="M11.4 11.6 6.6 10.4c.9 1.9 2.6 3 4.9 3.1"/><path d="M20.6 11.6l4.8-1.2c-.9 1.9-2.6 3-4.9 3.1"/><path d="M11.3 11.2c.3-1.4 2.2-2.1 4.7-2.1s4.4.7 4.7 2.1l-1.1 8.2c-.5 3.6-1.9 6.4-3.6 6.4s-3.1-2.8-3.6-6.4z"/><circle cx="13.9" cy="14.8" r=".7" fill="currentColor" stroke="none"/><circle cx="18.1" cy="14.8" r=".7" fill="currentColor" stroke="none"/><path d="M15 24.3h2"/></svg>';
function deer(sz) { return DEER.replace(/SZ/g, sz); }
function crown(small) {
  return '<div class="crown' + (small ? " small" : "") + '"><div class="crest">' + deer(small ? 28 : 44) + '</div>' +
    '<h1 class="brand">Naralingo</h1><div class="eyebrow">Ἑλληνική · 古典ギリシア語</div></div>';
}
function parTable(p) {
  if (!p) return "";
  let h = '<div class="par"><div class="par-h">' + gk(esc(p.title || p.lemma)) + '</div><table>';
  if (p.kind === "v") {
    h += '<tr><th></th><th>単数</th><th>複数</th></tr>';
    ["1人称", "2人称", "3人称"].forEach((r, i) => h += '<tr><th>' + r + '</th><td>' + gk(p.f[i]) + '</td><td>' + gk(p.f[i + 3] + (i === 2 ? "(ν)" : "")) + '</td></tr>');
  } else {
    h += '<tr><th></th><th>単数</th><th>複数</th></tr>';
    ["主格", "属格", "与格", "対格"].forEach((r, i) => h += '<tr><th>' + r + '</th><td>' + gk(p.sg[i]) + '</td><td>' + gk(p.pl[i]) + '</td></tr>');
  }
  return h + '</table></div>';
}
function alphaTable() {
  return '<div class="alpha">' + COURSE.alpha.map(a =>
    '<div class="al"><span class="al-l">' + gk(a[0] + " " + a[1] + (a[1] === "σ" ? " ς" : "")) + '</span><span class="al-n">' + a[2] + '</span><span class="al-t">' + esc(a[3]) + '</span></div>').join("") + '</div>';
}
function fill(html) {
  return gk(html).replace(/<div data-par="([^"]+)"><\/div>/g, (m, id) => parTable(COURSE.par[id]))
    .replace(/<div class="tbl-alpha" data-alpha><\/div>/g, alphaTable());
}
/* 文の語をタップすると語釈 */
function lookup(tok) {
  const w = tok.replace(/^[«"(]+|[»",.;·:!?;·)]+$/g, "");
  const L = COURSE.lex, k = GK.key(w);
  return { w, g: L[k] || L[GK.key(w.toLowerCase())] || null };
}
function sentHTML(s) {
  return s.split(/\s+/).map(t => { const r = lookup(t); return '<span class="w' + (r.g ? "" : " nog") + '" data-w="' + esc(r.w) + '">' + esc(t) + '</span>'; }).join(" ");
}
function bindGloss(root, box) {
  $$(".w", root).forEach(sp => sp.addEventListener("click", () => {
    $$(".w.on", root).forEach(x => x.classList.remove("on")); sp.classList.add("on");
    const r = lookup(sp.dataset.w), b = typeof box === "function" ? box(sp) : box;
    b.innerHTML = r.g ? r.g.map(x => '<div>' + gk(esc(x)).replace("｜", '<span class="sep">｜</span>') + '</div>').join("") : '<div class="muted">（語釈なし）</div>';
    b.classList.remove("hidden");
  }));
}

/* ============================================================
   問題の実行（練習・テスト・復習で共通）
   ============================================================ */
function runQuiz(o) {
  /* o: {items, mode:"practice"|"test"|"review", title, back, onAnswer(it, ok), onFinish(res)} */
  studyView = true;
  const q = o.items.slice(), total = q.length, t0 = Date.now();
  let done = 0, score = 0, wrong = [], tried = {}, cur = null, answered = false;
  const root = app();
  root.innerHTML = '<div class="wrap">' +
    '<div class="panel qz"><div class="qz-top"><button class="ic-nav" id="qzBack" aria-label="やめる">' + ICON.x + '</button>' +
    '<div class="qz-bar"><i id="qzFill"></i></div><span class="qz-n" id="qzN"></span></div>' +
    '<div class="qz-title">' + esc(o.title || "") + '</div><div id="qzStage"></div></div></div>';
  $("#qzBack").onclick = () => { if (confirmLeave()) o.back(); };
  function confirmLeave() { return done === 0 || o.mode === "review" || window.confirm("途中でやめる？（ここまでの記録は残る）"); }
  function prog() { $("#qzFill").style.width = (done / total * 100) + "%"; $("#qzN").textContent = Math.min(done + 1, total) + " / " + total; }
  function next() {
    if (!q.length) return finish();
    cur = q.shift(); answered = false; prog(); window.GRK && (window.GRK.cur = cur);
    const st = $("#qzStage"); st.innerHTML = render(cur); st.classList.remove("slide"); void st.offsetWidth; st.classList.add("slide");
    bind(cur);
  }
  function render(it) {
    const kind = { c: "選ぶ", w: "書く", b: "作文", s: "読む" }[it.t];
    let h = '<div class="qz-kind k-' + it.t + '">' + kind + '</div>';
    if (it.t === "c") {
      h += '<div class="qz-q">' + gk(it.q) + '</div><div class="opts">' +
        shuffle(it.o).map((x, i) => '<button class="opt" data-v="' + esc(x) + '"><i>' + (i + 1) + '</i><span>' + gk(esc(x)) + '</span></button>').join("") + '</div>';
    } else if (it.t === "w") {
      h += '<div class="qz-q">' + gk(it.q) + '</div><div class="win"><input id="ans" class="gin" type="text" placeholder="ローマ字で打つとギリシア文字に"><button class="btn pri" id="ok">答える</button></div>' +
        '<div class="marks">' + [[")", "᾿", "滑らか"], ["(", "῾", "粗い"], ["/", "´", "鋭"], ["\\", "`", "重"], ["=", "῀", "曲"], ["j", "ι", "ι下書き"]].map(m =>
          '<button class="mk" data-m="' + esc(m[0]) + '" title="' + m[2] + '"><span>' + m[1] + '</span><small>' + m[2] + '</small></button>').join("") + '</div>' +
        '<details class="keys"><summary>入力のしかた</summary>' + KEYS_HELP + '</details>' +
        '<button class="link giveup" id="giveup">わからない（答えを見る）</button>';
    } else if (it.t === "b") {
      h += '<div class="qz-q">' + gk(esc(it.ja)) + '</div><div class="qsub">札を選んで文を作る（順番は自由）</div>' +
        '<div class="slot" id="slot"></div><div class="bank" id="bank">' +
        shuffle(it.a.concat(it.x)).map(x => '<button class="tile" data-v="' + esc(x) + '">' + gk(esc(x)) + '</button>').join("") + '</div>' +
        '<div class="brow"><button class="btn" id="clr">やり直す</button><button class="btn pri" id="ok" disabled>答える</button></div>';
    } else if (it.t === "s") {
      h += '<div class="qz-q sent">' + gk(sentHTML(it.g)) + '</div><div class="gloss hidden" id="gl"></div>' +
        '<div class="qsub">語をタップすると意味が出る。訳を考えてから開く。</div>' +
        '<div class="brow"><button class="btn pri" id="reveal">訳を見る</button></div><div class="tr hidden" id="tr">' + esc(it.ja) + '</div>' +
        '<div class="brow hidden" id="self"><button class="btn ng" id="sNo">あやしい</button><button class="btn ok" id="sYes">読めた</button></div>';
    }
    return h + '<div class="fb hidden" id="fb"></div>';
  }
  function bind(it) {
    if (it.t === "c") {
      $$(".opt").forEach(b => b.onclick = () => { if (answered) return; b.classList.add("pick"); grade(b.dataset.v === it.a ? 2 : 0, b.dataset.v); });
    } else if (it.t === "w") {
      const inp = $("#ans"); GK.attachInput(inp); setTimeout(() => inp.focus(), 50);
      $$(".mk").forEach(b => { b.onpointerdown = e => e.preventDefault(); b.onclick = e => { e.preventDefault(); GK.insertMark(inp, b.dataset.m); }; });
      const go = () => { if (answered || !inp.value.trim()) return; inp.blur(); grade(GK.judge(inp.value, it.a), inp.value); };
      $("#ok").onclick = go; inp.addEventListener("keydown", e => { if (e.key === "Enter" && !e.isComposing) { e.preventDefault(); go(); } });
      $("#giveup").onclick = () => { if (!answered) grade(0, ""); };
    } else if (it.t === "b") {
      const slot = $("#slot"), bank = $("#bank"), ok = $("#ok");
      function upd() { ok.disabled = !slot.children.length; }
      bank.addEventListener("click", e => { const t = e.target.closest(".tile"); if (!t || answered) return; slot.appendChild(t); upd(); });
      slot.addEventListener("click", e => { const t = e.target.closest(".tile"); if (!t || answered) return; bank.appendChild(t); upd(); });
      $("#clr").onclick = () => { if (answered) return; $$(".tile", slot).forEach(t => bank.appendChild(t)); upd(); };
      ok.onclick = () => {
        if (answered) return;
        const got = $$(".tile", slot).map(t => t.dataset.v);
        const same = got.length === it.a.length && got.slice().sort().join("\u0001") === it.a.slice().sort().join("\u0001");
        grade(same ? 2 : 0, got.join(" "));
      };
    } else if (it.t === "s") {
      bindGloss($(".qz-q"), $("#gl"));
      $("#reveal").onclick = () => { $("#tr").classList.remove("hidden"); $("#self").classList.remove("hidden"); $("#reveal").parentNode.classList.add("hidden"); };
      $("#sYes").onclick = () => { if (!answered) grade(2, "", true); };
      $("#sNo").onclick = () => { if (!answered) grade(0, "", true); };
    }
  }
  function grade(r, given, self) {
    answered = true;
    const strict = prefs().strict, okv = r === 2 || (r === 1 && !strict);
    const first = !tried[cur.id]; tried[cur.id] = 1;
    if (first) { done++; if (okv) score++; else wrong.push(cur); }
    countAns(okv);
    if (o.onAnswer) o.onAnswer(cur, okv, first);
    if (cur.id && cur.id.charAt(0) === "d") { const s = S(), x = s.it[cur.id] || (s.it[cur.id] = { c: 0, w: 0 }); if (okv) x.c++; else x.w++; x.last = okv ? 1 : 0; x.u = Date.now(); }
    save();
    if (!okv && o.mode !== "test") q.splice(Math.min(3, q.length), 0, cur);   // まちがえた問題は3問あとにもう一度
    prog(); $("#qzFill").style.width = (done / total * 100) + "%";
    // 見た目
    if (cur.t === "c") $$(".opt").forEach(b => { if (b.dataset.v === cur.a) b.classList.add("right"); else if (b.classList.contains("pick")) b.classList.add("bad"); b.disabled = true; });
    if (cur.t === "w") $("#ans").disabled = true;
    if (cur.t === "b") { $$(".tile").forEach(t => t.disabled = true); $("#ok").disabled = true; $("#clr").disabled = true; }
    if (self) { $("#self").classList.add("hidden"); }
    const fb = $("#fb");
    let h = '<div class="fb-h ' + (okv ? "ok" : "ng") + '">' + (okv ? (r === 1 ? "正解（記号に注意）" : "正解") : (r === -1 ? "おしい：ι下書き" : r === 1 ? "記号がちがう" : self ? "もう一度あとで" : "ざんねん")) + '</div>';
    if (cur.t === "w" && r !== 2) h += '<div class="fb-a">正しくは <b>' + gk(esc(cur.a[0])) + '</b>' + (given ? '<span class="you">あなた：' + gk(esc(given)) + '</span>' : "") + '</div>';
    if (cur.t === "c" && !okv) h += '<div class="fb-a">正しくは <b>' + gk(esc(cur.a)) + '</b></div>';
    if (cur.t === "b") h += '<div class="fb-a">' + (okv ? "" : "正しくは ") + '<b>' + gk(esc(cur.a.join(" "))) + '</b></div>';
    if (cur.ex) h += '<div class="fb-ex">' + gk(cur.ex) + '</div>';
    h += '<button class="btn pri next" id="nx">次へ ' + ICON.next + '</button>';
    fb.innerHTML = h; fb.classList.remove("hidden");
    const nx = $("#nx"); nx.onclick = next; setTimeout(() => { nx.focus(); try { nx.scrollIntoView({ block: "nearest", behavior: "smooth" }); } catch (e) {} }, 30);
    if (okv && prefs().auto && cur.t !== "s") setTimeout(() => { if ($("#nx") === nx) next(); }, 1100);
  }
  function finish() {
    flushTime(); save();
    const pct = total ? score / total : 0, res = { score, total, pct, wrong, ms: Date.now() - t0 };
    if (o.onFinish && o.onFinish(res) === false) return;
    const pass = o.mode === "test" ? pct >= PASS : null;
    root.innerHTML = '<div class="wrap"><div class="panel result">' +
      '<div class="r-face">' + (pass === false ? "…" : pct >= .9 ? "◎" : pct >= .7 ? "○" : "△") + '</div>' +
      '<div class="r-score">' + score + '<small> / ' + total + '</small></div>' +
      '<div class="r-msg">' + (o.mode === "test" ? (pass ? "合格！ よくできた。" : "あと少し。8割で合格。もう一度どうぞ。") : o.mode === "review" ? "今日の復習、おつかれさま。" : "練習おわり。まちがえた問題はくり返し出した。") + '</div>' +
      (wrong.length ? '<div class="r-wrong"><div class="r-wh">まちがえた問題</div>' + wrong.map(w => '<div class="rw">' + rwText(w) + '</div>').join("") + '</div>' : "") +
      '<div class="brow"><button class="btn" id="rAgain">もう一度</button><button class="btn pri" id="rBack">' + esc(o.backLabel || "もどる") + '</button></div></div></div>';
    $("#rAgain").onclick = () => o.again ? o.again() : runQuiz(o);
    $("#rBack").onclick = o.back;
  }
  function rwText(w) {
    if (w.t === "b") return gk(esc(w.ja)) + ' → <b>' + gk(esc(w.a.join(" "))) + '</b>';
    if (w.t === "s") return gk(esc(w.g)) + '<br><small>' + esc(w.ja) + '</small>';
    return '<span class="rq">' + gk(w.q) + '</span> → <b>' + gk(esc(Array.isArray(w.a) ? w.a[0] : w.a)) + '</b>';
  }
  next();
}
const KEYS_HELP = '<div class="kh"><p>ローマ字を打つと、その場でギリシア文字に変わる（設定でオフにできる）。</p><table>' +
  '<tr><td>a b g d e z</td><td>α β γ δ ε ζ</td></tr><tr><td>h q i k l m n</td><td>η θ ι κ λ μ ν</td></tr>' +
  '<tr><td>c o p r s t u</td><td>ξ ο π ρ σ τ υ</td></tr><tr><td>f x y w</td><td>φ χ ψ ω</td></tr>' +
  '<tr><td>) ( / \\ = j</td><td>᾿ ῾ ´ ` ῀ ι下書き（母音のあとに打つ）</td></tr></table>' +
  '<p>例：<code>xw/ra|</code> → χώρᾳ、<code>h(me/ra</code> → ἡμέρα。アクセント・気息は省いても正解（設定で厳しくできる）。ι下書きは省くと不正解（与格の印なので）。</p></div>';
const ICON = {
  x: '<svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><path d="M7 7l10 10M17 7 7 17"/></svg>',
  back: '<svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M15 5l-7 7 7 7"/></svg>',
  next: '<svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" style="vertical-align:-3px"><path d="M5 12h13"/><path d="M13 6l6 6-6 6"/></svg>',
  check: '<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round"><path d="M5 12.5l4.5 4.5L19 7.5"/></svg>'
};

/* ============================================================
   ルーター
   ============================================================ */
function go(h) { if (location.hash === h) route(); else location.hash = h; }
window.addEventListener("hashchange", route);
function route() {
  flushTime(); window.scrollTo(0, 0);
  if (!user) { studyView = false; return viewLogin(); }
  const h = location.hash.replace(/^#\/?/, "").split("/");
  if (h[0] === "day" && dayOf(+h[1])) return viewDay(+h[1], h[2] || null);
  if (h[0] === "review") return viewReview();
  if (h[0] === "tables") return viewTables();
  return viewHome();
}

/* ---------- ログイン ---------- */
function viewLogin() {
  app().innerHTML = '<div class="wrap">' + crown() + '<div class="panel">' +
    '<p class="hello">ログイン</p><div class="logform">' +
    '<label class="fld"><span>ID</span><input id="lid" class="idin" type="text" autocomplete="username" autocapitalize="none" spellcheck="false"></label>' +
    '<label class="fld"><span>パスワード</span><input id="lpw" class="idin" type="password" autocomplete="current-password" autocapitalize="none"></label>' +
    '<button class="btn pri big" id="lgo">ログイン</button></div>' +
    '<label class="remember"><input type="checkbox" id="lrem" checked> この端末にログインを記憶する</label>' +
    '<div class="note warn hidden" id="lnote"></div></div></div>';
  const go2 = async () => {
    const ok = await login($("#lid").value, $("#lpw").value, $("#lrem").checked);
    if (!ok) { const n = $("#lnote"); n.textContent = "ID かパスワードがちがう。"; n.classList.remove("hidden"); return; }
    if (CFG.SCRIPT_URL) sync().then(route);
    route();
  };
  $("#lgo").onclick = go2;
  $("#lpw").addEventListener("keydown", e => { if (e.key === "Enter") go2(); });
  $("#lid").addEventListener("keydown", e => { if (e.key === "Enter") $("#lpw").focus(); });
  $("#lid").focus();
}

/* ---------- ホーム ---------- */
function stepDone(n, k) { return !!les(n).st[k]; }
function nextStep() {
  for (const d of DAYS) { const L = les(d.n); if (L.pass) continue; for (const s of STEPS) if (!L.st[s[0]]) return { d, s }; return { d, s: STEPS[4] }; }
  return null;
}
function viewHome() {
  studyView = false;
  const s = S(), c = chain(), due = dueIds().length, nx = nextStep(), t = today();
  const cards = Object.keys(s.cards).filter(k => CARD[k]), fixed = cards.filter(k => s.cards[k].l >= 4).length;
  let week = ""; for (let i = 6; i >= 0; i--) { const d = dstr(t - i), on = s.days.indexOf(d) >= 0; week += '<i class="' + (on ? "on" : "") + (i === 0 ? " today" : "") + '" title="' + d + '"><b>' + "日月火水木金土"[new Date((t - i) * 864e5).getUTCDay()] + '</b></i>'; }
  const tiles = DAYS.map(d => {
    const L = les(d.n), n = STEPS.filter(x => L.st[x[0]]).length, cur = nx && nx.d.n === d.n;
    return '<a class="day' + (L.pass ? " pass" : "") + (cur ? " cur" : "") + '" href="#/day/' + d.n + '">' +
      '<span class="dn">Day ' + d.n + '</span><span class="dt">' + gk(esc(d.title)) + '</span><span class="dsub">' + gk(esc(d.sub)) + '</span>' +
      '<span class="dots">' + STEPS.map(x => '<i class="' + (L.st[x[0]] ? "on" : "") + '"></i>').join("") + '</span>' +
      (L.pass ? '<span class="dpass">' + ICON.check + Math.round((L.best || 0) * 100) + '%</span>' : cur ? '<span class="dnow">いまここ</span>' : "") + '</a>';
  }).join("");
  app().innerHTML = '<div class="wrap">' + crown() + '<div class="panel">' +
    '<div class="bar"><p class="hello">Χαῖρε, ' + esc(user.name) + '</p>' +
    '<span class="streak" title="1日あいてもつながる（2日あくと切れる）">継続 <b>' + c.n + '</b> 日' + (c.doneToday ? '<small>今日済</small>' : c.risk ? '<small class="warn">今日がラスト</small>' : '<small>今日はまだ</small>') + '</span></div>' +
    '<div class="week">' + week + '</div>' +
    '<div class="todo">' +
    (due ? '<a class="go-btn rev" href="#/review"><span class="go-k">復習</span><span class="go-t">今日のカード <b>' + due + '</b> 枚</span><span class="go-s">忘れかけた語・形・文をもう一度</span></a>' : '<div class="go-done">今日の復習カードはなし' + (cards.length ? "。次は " + inDays(Math.min.apply(null, cards.map(k => s.cards[k].d)) - t) : "") + '</div>') +
    (nx ? '<a class="go-btn les" href="#/day/' + nx.d.n + '/' + nx.s[0] + '"><span class="go-k">Day ' + nx.d.n + '</span><span class="go-t">' + esc(nx.d.title) + ' ・ ' + nx.s[1] + '</span><span class="go-s">' + esc(nx.d.src) + '</span></a>' : '<div class="go-done">第1週はすべて合格。第2週を準備中。</div>') +
    '</div>' +
    '<div class="sumgrid"><div class="sum"><div class="n">' + fmtDur(s.ms) + '</div><div class="l">勉強時間</div></div>' +
    '<div class="sum"><div class="n">' + s.ans + '</div><div class="l">解答数</div></div>' +
    '<div class="sum"><div class="n">' + (s.ans ? Math.round(s.cor / s.ans * 100) + "%" : "—") + '</div><div class="l">正答率</div></div>' +
    '<div class="sum"><div class="n">' + fixed + '<small>/' + cards.length + '</small></div><div class="l">定着カード</div></div></div>' +
    '<div class="sec-h">第1週　White, <i>First Greek Book</i> Lesson I–VI</div><div class="days">' + tiles + '</div>' +
    '<div class="links"><a class="card" href="#/tables"><span class="ti">文法表</span><span class="de">これまでの変化表・アルファベット</span></a>' +
    '<a class="card" href="#/review"><span class="ti">復習カード</span><span class="de">' + cards.length + ' 枚（今日 ' + due + '）</span></a></div>' +
    '<details class="prefs"><summary class="prefs-h">このコースについて</summary><div class="about">' + ABOUT + '</div></details>' +
    '<details class="prefs"><summary class="prefs-h">設定</summary>' +
    prefRow("conv", "ローマ字 → ギリシア文字", [["1", "変換する"], ["0", "しない"]]) +
    prefRow("strict", "アクセント・気息", [["0", "省略しても正解"], ["1", "厳密に判定"]]) +
    prefRow("auto", "正解のあと", [["0", "「次へ」を押す"], ["1", "自動で次へ"]]) + '</details>' +
    '<details class="prefs"><summary class="prefs-h">記録のバックアップ</summary>' +
    '<p class="pref-note" id="syncSt">' + syncHTML() + '</p>' +
    '<div class="brow left">' + (CFG.SCRIPT_URL ? '<button class="btn" id="bSync">いま同期</button>' : "") +
    '<button class="btn" id="bExp">ファイルに書き出す</button><label class="btn">ファイルから戻す<input type="file" id="bImp" accept="application/json,.json" hidden></label></div></details>' +
    '<div class="foot"><button class="ic-nav" id="bGuide" title="使い方">?</button><button class="ic-nav" id="bOut" title="ログアウト">' + ICON.x + '</button></div>' +
    '</div></div>';
  $$("[data-pref]").forEach(b => b.onclick = () => {
    setPref(b.dataset.pref, b.dataset.v === "1");
    $$('[data-pref="' + b.dataset.pref + '"]').forEach(x => x.classList.toggle("on", x === b));
  });
  $("#bOut").onclick = () => { if (window.confirm("ログアウトする？")) { logout(); route(); } };
  $("#bGuide").onclick = welcome;
  $("#bExp").onclick = () => {
    flushTime(); save(true);
    const b = new Blob([JSON.stringify(S())], { type: "application/json" }), a = document.createElement("a");
    a.href = URL.createObjectURL(b); a.download = "naralingo-greek-" + dstr(today()) + ".json"; a.click(); setTimeout(() => URL.revokeObjectURL(a.href), 2000);
  };
  $("#bImp").onchange = e => {
    const f = e.target.files[0]; if (!f) return;
    f.text().then(t => { const d = JSON.parse(t); store = merge(S(), d); save(); viewHome(); alert("記録を合わせた。"); }).catch(() => alert("読み込めなかった。"));
  };
  if ($("#bSync")) $("#bSync").onclick = () => { $("#syncSt").textContent = "同期中…"; sync().then(viewHome); };
  if (!s.wel) welcome();
}
function prefRow(k, label, vals) {
  const cur = prefs()[k] ? "1" : "0";
  return '<div class="pref-row"><span class="pref-l">' + label + '</span><span class="pref-t">' +
    vals.map(v => '<button type="button" data-pref="' + k + '" data-v="' + v[0] + '" class="' + (v[0] === cur ? "on" : "") + '">' + v[1] + '</button>').join("") + '</span></div>';
}
const ABOUT = '<p><b>目標</b>：クセノポン『アナバシス』など、古典期アッティカ散文を辞書と注釈を手に読めるようになる。</p>' +
  '<p><b>教科書</b>：J. W. White, <i>The First Greek Book</i>（1896、全80課）。文法の順序と例文はこの本にそろえ、解説は日本語で短くまとめた。第13課から『アナバシス』を易しくした読み物が始まり、80課を終えると原文の第1巻に入れる。</p>' +
  '<p><b>1日の流れ</b>：①復習カード（5〜10分）→ ②その日のレッスン（解説 → 単語 → 練習 → 読解 → テスト、20〜30分）。テスト8割で合格。</p>' +
  '<p><b>復習カード</b>：単語・変化形・読んだ文が、忘れかけたころ（翌日 → 3日後 → 1週間後 → 2週間後 → 1か月後）にもう一度出る。まちがえたら翌日にもどる。</p>' +
  '<p><b>この先</b>：第2週＝Lesson VII–XII（未完了過去・第二変化・未来とアオリスト・男性名詞・完了）。</p>';
function welcome() {
  const SL = [
    ["Χαῖρε!", "古典ギリシア語を、毎日少しずつ。<br>ゴールはクセノポン『アナバシス』を自分で読むこと。"],
    ["1日の流れ", "<b>復習カード</b>（5〜10分）→ <b>その日のレッスン</b>（20〜30分）。<br>レッスンは 解説 → 単語 → 練習 → 読解 → テスト の順。"],
    ["ギリシア文字の入力", "ローマ字で打つとギリシア文字に変わる：<code>xw/ra|</code> → χώρᾳ。<br>アクセントは省略しても正解。ι下書き（<code>j</code>）は与格の印なので必要。"],
    ["さあ、はじめよう", "まずは Day 1 のアルファベットから。"]
  ];
  let i = 0; const el = document.createElement("div"); el.className = "wel";
  function draw() {
    const last = i === SL.length - 1;
    el.innerHTML = '<div class="wel-box"><div class="wel-deer">' + deer(44) + '</div><div class="wel-t">' + gk(SL[i][0]) + '</div><div class="wel-b">' + gk(SL[i][1]) + '</div>' +
      '<div class="wel-dots">' + SL.map((_, k) => '<i class="' + (k === i ? "on" : "") + '"></i>').join("") + '</div>' +
      '<div class="wel-btns"><button class="btn" id="wB">' + (i ? "もどる" : "スキップ") + '</button><button class="btn pri" id="wN">' + (last ? "はじめる" : "次へ") + '</button></div></div>';
    $("#wN", el).onclick = () => { if (last) close(); else { i++; draw(); } };
    $("#wB", el).onclick = () => { if (i) { i--; draw(); } else close(); };
  }
  function close() { S().wel = 1; save(); el.remove(); }
  document.body.appendChild(el); draw();
}

/* ---------- レッスン ---------- */
function viewDay(n, step) {
  studyView = true;
  const d = dayOf(n), L = les(n);
  if (!step) { const f = STEPS.find(s => !L.st[s[0]]); step = f ? f[0] : "intro"; }
  const tabs = STEPS.map((s, i) => '<a class="tab' + (s[0] === step ? " on" : "") + (L.st[s[0]] ? " done" : "") + '" href="#/day/' + n + '/' + s[0] + '"><i>' + (L.st[s[0]] ? ICON.check : i + 1) + '</i>' + s[1] + '</a>').join("");
  const pdf = d.page ? ' ・ <a href="The First Greek Book.pdf#page=' + (d.page + 12) + '" target="_blank" rel="noopener">原典 p.' + d.page + '</a>' : "";
  app().innerHTML = '<div class="wrap"><div class="panel lesson">' +
    '<div class="l-top"><a class="ic-nav" href="#/" aria-label="ホーム">' + ICON.back + '</a><div class="l-ttl"><span class="l-day">Day ' + n + '</span>' + esc(d.title) +
    '<small>' + esc(d.sub) + '</small><small class="l-src">White, <i>First Greek Book</i> ' + esc(d.src) + pdf + '</small></div></div>' +
    '<nav class="tabs">' + tabs + '</nav><div id="lbody"></div></div></div>';
  const body = $("#lbody");
  const done = k => { if (!L.st[k]) { L.st[k] = Date.now(); markStudy(); save(); } };
  const nextBtn = (k, label) => { const i = STEPS.findIndex(s => s[0] === k), nx = STEPS[i + 1]; return '<div class="brow"><button class="btn pri big" id="stepNext">' + label + (nx ? ' → ' + nx[1] + 'へ' : '') + '</button></div>'; };
  const toNext = k => { const i = STEPS.findIndex(s => s[0] === k), nx = STEPS[i + 1]; go(nx ? "#/day/" + n + "/" + nx[0] : "#/"); };
  const back = () => go("#/day/" + n + "/" + step);

  if (step === "intro") {
    body.innerHTML = d.intro.map((s, i) => '<section class="ib"><h3><span>' + (i + 1) + '</span>' + gk(esc(s.h)) + '</h3>' + fill(s.b) + '</section>').join("") + nextBtn("intro", "読んだ");
    $("#stepNext").onclick = () => { done("intro"); toNext("intro"); };
  }
  else if (step === "vocab") {
    let list, quizItems;
    if (d.letters) {
      list = '<p class="lead">' + esc(d.vocabNote) + '</p>' + alphaTable();
      quizItems = () => shuffle(COURSE.alpha).slice(0, 12).map(a => ({ t: "c", id: "v1-" + a[2], q: '<span class="big">' + a[1] + '</span> の名前は？', a: a[2], o: pick4(a[2], COURSE.alpha.map(x => x[2])), ex: a[1] + " ＝ " + a[2] + "（" + a[3] + "）。" + a[4] }));
    } else if (d.vocabReview) {
      list = '<p class="lead">今週出てきた単語を総ざらい。15語をランダムに出す。</p><div class="vlist">' + ALL_VOCAB().map(vRow).join("") + '</div>';
      quizItems = () => shuffle(ALL_VOCAB()).slice(0, 15).map(w => Object.assign(vocabChoice(w), { id: "vr-" + w.g }));
    } else {
      list = (d.vocabNote ? '<p class="lead">' + gk(esc(d.vocabNote)) + '</p>' : '') + '<div class="vlist">' + d.vocab.map(vRow).join("") + '</div>';
      quizItems = () => shuffle(d.vocab).map(w => Object.assign(vocabChoice(w, d.vocab.length >= 4 ? d.vocab : null), { id: "v" + n + "-" + w.g }));
    }
    body.innerHTML = list + '<p class="note">単語を眺めたら、ミニテストで意味を確かめる。終えると復習カードに入る（明日から出る）。</p>' +
      '<div class="brow"><button class="btn pri big" id="vq">ミニテスト' + (L.st.vocab ? "（もう一度）" : "") + '</button></div>';
    $("#vq").onclick = () => runQuiz({ items: quizItems(), mode: "practice", title: "Day " + n + " 単語ミニテスト", back, backLabel: "レッスンにもどる",
      onFinish: () => { done("vocab"); addCards((id, c) => c.day === n && (c.kind === "vocab" || c.kind === "letter")); } });
  }
  else if (step === "drill") {
    const pool = d.review ? DAYS.slice(0, n - 1).reduce((a, x) => a.concat(x.drills), []) : d.drills;
    const it = S().it, okN = pool.filter(x => it[x.id] && it[x.id].last === 1).length;
    body.innerHTML = '<p class="lead">' + (d.review ? "Day 1〜6 の問題をまぜて出す。" : "この日の問題から10問。") + '1回分を終えると、この日の変化形が復習カードに入る。</p>' +
      '<div class="meter"><span class="m-bar"><i style="width:' + (pool.length ? okN / pool.length * 100 : 0) + '%"></i></span><span class="m-v">' + okN + ' / ' + pool.length + ' 問 正解済み</span></div>' +
      '<div class="brow"><button class="btn pri big" id="dq">練習する（10問）</button></div>' +
      '<details class="memo"><summary>この日の解説をもう一度見る</summary>' + d.intro.map(s => '<h4>' + gk(esc(s.h)) + '</h4>' + fill(s.b)).join("") + '</details>';
    const start = () => runQuiz({ items: drillPick(pool, ROUND), mode: "practice", title: "Day " + n + " 練習", back, backLabel: "レッスンにもどる",
      again: start, onFinish: () => { done("drill"); addCards((id, c) => c.day === n && c.kind === "form"); } });
    $("#dq").onclick = start;
  }
  else if (step === "read") {
    const R = d.read;
    if (R.kind === "words") {
      body.innerHTML = '<p class="lead">' + esc(R.lead) + '</p><div class="words">' + R.items.map(w =>
        '<button class="wd"><span class="wd-g">' + gk(esc(w[0])) + '</span><span class="wd-r hidden"><b>' + esc(w[1]) + '</b>' + gk(esc(w[2])) + '</span></button>').join("") + '</div>' + nextBtn("read", "読み終えた");
      $$(".wd").forEach(b => b.onclick = () => $(".wd-r", b).classList.toggle("hidden"));
    } else {
      body.innerHTML = '<p class="lead">' + esc(R.lead) + '</p>' + R.items.map((s, i) =>
        '<div class="rs' + (s[2] && s[2].goal ? " goal" : "") + '">' + (s[2] && s[2].goal ? '<div class="goal-h">最終目標の一文</div>' : '') +
        '<div class="rs-n">' + (i + 1) + '</div><div class="rs-g">' + gk(sentHTML(s[0])) + '</div><div class="gloss hidden"></div>' +
        '<button class="link rs-t">訳</button><div class="tr hidden">' + esc(s[1]) + '</div></div>').join("") +
        '<p class="note">読み終えると、これらの文が復習カードに入る。</p>' + nextBtn("read", "読み終えた");
      $$(".rs").forEach(r => { bindGloss(r, $(".gloss", r)); $(".rs-t", r).onclick = () => $(".tr", r).classList.toggle("hidden"); });
    }
    $("#stepNext").onclick = () => { done("read"); addCards((id, c) => c.day === n && c.kind === "sent"); toNext("read"); };
  }
  else if (step === "test") {
    const N = d.review ? 15 : 10;
    body.innerHTML = '<p class="lead">' + N + '問。8割で合格。まちがえても、くり返しは出ない（本番）。</p>' +
      (L.pass ? '<div class="passed">' + ICON.check + ' 合格済み（最高 ' + Math.round((L.best || 0) * 100) + '%）</div>' : (L.best ? '<div class="note">最高 ' + Math.round(L.best * 100) + '%</div>' : '')) +
      '<div class="brow"><button class="btn pri big" id="tq">テストを始める</button></div>';
    $("#tq").onclick = () => runQuiz({ items: testPick(d, N), mode: "test", title: "Day " + n + " テスト", back: () => go("#/day/" + n + "/test"), backLabel: "レッスンにもどる",
      onFinish: r => { done("test"); L.best = Math.max(L.best || 0, r.pct); if (r.pct >= PASS && !L.pass) L.pass = Date.now(); save(); } });
  }
}
function vRow(w) {
  return '<div class="vrow"><span class="vg">' + gk(esc(w.g)) + '</span><span class="vh">' + gk(esc(w.h || "")) + '</span><span class="vj">' + esc(w.ja) + '</span>' +
    (w.note ? '<span class="vn">' + gk(esc(w.note)) + '</span>' : '') + '</div>';
}
/* 練習の10問：まだ正解していない問題・まちがえた問題を先に。自動生成の文字問題は少なめに */
function drillPick(pool, n) {
  const it = S().it, score = x => { const s = it[x.id]; return (s ? (s.last === 1 ? 2 : 0) + Math.min(s.c, 3) * .3 - s.w * .2 : -1) + Math.random() * 1.2 + (x.gen ? .6 : 0); };
  return pool.slice().sort((a, b) => score(a) - score(b)).slice(0, n);
}
function testPick(d, n) {
  if (d.review) {
    const out = [];
    DAYS.slice(0, d.n - 1).forEach(x => { const p = shuffle(x.drills.filter(y => !y.gen)); out.push.apply(out, p.slice(0, x.n <= 2 ? 2 : 3)); });
    return shuffle(out).slice(0, n);
  }
  const hard = shuffle(d.drills.filter(x => x.t !== "c")), easy = shuffle(d.drills.filter(x => x.t === "c" && !x.gen)), gen = shuffle(d.drills.filter(x => x.gen));
  const k = Math.min(hard.length, Math.ceil(n * .4));
  return shuffle(hard.slice(0, k).concat(easy.slice(0, n - k - (gen.length ? 3 : 0))).concat(gen.slice(0, 3))).slice(0, n);
}

/* ---------- 復習 ---------- */
function viewReview() {
  studyView = true;
  const ids = shuffle(dueIds()), s = S(), all = Object.keys(s.cards).filter(k => CARD[k]);
  if (!ids.length) {
    const lv = [0, 0, 0, 0, 0, 0, 0]; all.forEach(k => lv[s.cards[k].l]++);
    const nextD = all.length ? Math.min.apply(null, all.map(k => s.cards[k].d)) - today() : null;
    app().innerHTML = '<div class="wrap"><div class="panel"><div class="l-top"><a class="ic-nav" href="#/" aria-label="ホーム">' + ICON.back + '</a><div class="l-ttl">復習カード</div></div>' +
      '<p class="lead">' + (all.length ? "今日の分はおわり。次は " + inDays(nextD) + "。" : "カードはまだない。レッスンの「単語」を終えると入る。") + '</p>' +
      levelChart(lv, all.length) + '</div></div>';
    return;
  }
  const take = ids.slice(0, REVIEW_MAX);
  let moved = 0;
  runQuiz({ items: take.map(cardItem), mode: "review", title: "復習カード（今日 " + ids.length + " 枚）", back: () => go("#/"), backLabel: "ホームへ",
    again: () => viewReview(),
    onAnswer: (it, ok, first) => { if (first && it.cid) { gradeCard(it.cid, ok); moved++; } },
    onFinish: () => { save(); } });
}
function levelChart(lv, total) {
  const lab = ["", "翌日", "3日", "1週", "2週", "1か月", "定着"], mx = Math.max.apply(null, lv.slice(1).concat([1]));
  return '<div class="lvl">' + lv.slice(1).map((v, i) => '<div class="lv"><span class="lv-b"><i style="height:' + (v / mx * 100) + '%"></i></span><b>' + v + '</b><small>' + lab[i + 1] + '</small></div>').join("") +
    '</div><p class="note">段ごとのカードの数（全 ' + total + ' 枚）。正解するたびに右の段へ進み、次に出るまでの間がのびる。</p>';
}

/* ---------- 文法表 ---------- */
function viewTables() {
  studyView = false;
  let h = '<div class="wrap"><div class="panel"><div class="l-top"><a class="ic-nav" href="#/" aria-label="ホーム">' + ICON.back + '</a><div class="l-ttl">文法表<small>第1週で学んだ変化</small></div></div>' +
    '<details class="memo" open><summary>アルファベット（Day 1）</summary>' + alphaTable() + '</details>';
  DAYS.forEach(d => {
    const main = d.pars.map(id => COURSE.par[id]).filter(p => !p.hide), rest = d.pars.map(id => COURSE.par[id]).filter(p => p.hide);
    if (!main.length && !rest.length) return;
    h += '<details class="memo"' + (les(d.n).st.intro ? " open" : "") + '><summary>Day ' + d.n + '　' + esc(d.title) + '</summary><div class="pars">' + main.map(parTable).join("") + '</div>' +
      (rest.length ? '<details class="sub"><summary>同じ型の語（' + rest.length + '）</summary><div class="pars">' + rest.map(p => parTable(Object.assign({}, p, { title: p.lemma + (p.adj ? "（女性形）" : "") + "　" + p.ja }))).join("") + '</div></details>' : "") + '</details>';
  });
  app().innerHTML = h + '</div></div>';
}

/* ---------- 起動 ---------- */
document.addEventListener("click", e => { const c = e.target.closest && e.target.closest(".crown"); if (c && !e.target.closest("a,button")) go("#/"); });
if (user && CFG.SCRIPT_URL) sync().then(() => { if (!location.hash || location.hash === "#/") route(); });
route();
window.GRK = { GK, S, merge, CARD, cardItem, sync };   // 確認用
})();
