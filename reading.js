/* ============================================================
   読み（ローマ字転写と IPA）
   ・ローマ字：学術式の転写。長母音に横棒（ā ē ī ō ȳ）、アクセントの記号はギリシア語と同じ位置に（á à â）
   ・IPA：紀元前5〜4世紀アッティカの復元発音（W. S. Allen, Vox Graeca に基づく）。
         アクセントは高さ：[á] 高い、[ǎː] 長母音・二重母音の後半が高い（鋭）、[âː] 高く始まって下がる（曲）
   α ι υ は綴りでは長短がわからないので、語ごとに長さを登録する（下の WORDS と変化表の型）。
   登録のない語の α ι υ は、IPA で [a(ː)] のように「長短未確定」として示す。
   ============================================================ */
(function () {
"use strict";
const C = window.COURSE;
/* ---- 1. 語ごとの母音の長さ：母音のあとの _ ＝長い、? ＝長短未確定。α ι υ が短い語・二重母音だけの語も「確認済み」として載せる ---- */
const WORDS = `
ἡ τῆς τῇ τήν αἱ τῶν ταῖς τά_ς
φιλοσοφία_ θέα_τρον ψυ_χή κόσμος χάος δρᾶμα ἄγγελος μοῦσα Ζεύς Σωκράτης Ξενοφῶν Κῦρος
ὁπλί_της υἱός ᾤκησα ὧδε φοβερός αὐτός αὐτόν Ἑλληνικός ψέλιον Ἄρτεμις οἴκοι ῥήτωρ ἐπ ἐπί
θάλασσα ἄνθρωπος ἀνθρώπου λόγος λόγου λόγοι δῶρον δώρου ἀγγέλου υἱοῦ ἀγαθός ἀγαθόν
ἐν ἦν ἦσαν καί ἐκ ἐξ οὐ οὐκ οὐχ εἰς οἰκέω
Δα?ρείου Πα?ρυ?σά?τι?δος γίγνονται παῖδες δύο πρεσβύτερος μέν Ἀ?ρτα?ξέρξης νεώτερος δέ
`;
/* ---- 2. 変化表：主格単数の長さと型（a＝ᾱ、h＝η、sa＝短い α・属与は ᾱ、sh＝短い α・属与は η）。動詞は1人称単数 ---- */
const PAR = {
  chora: ["χώρα_", "a"], stratia: ["στρατιά_", "a"], agora: ["ἀγορά_", "a"], hemera: ["ἡμέρα_", "a"], thura: ["θύρα_", "a"],
  oikia: ["οἰκία_", "a"], mikra: ["μι_κρά_", "a"], makra: ["μακρά_", "a"], fobera: ["φοβερά_", "a"],
  kome: ["κώμη", "h"], skene: ["σκηνή", "h"], kale: ["καλή", "h"], kake: ["κακή", "h"], krauge: ["κραυγή", "h"], mache: ["μάχη", "h"],
  sfendone: ["σφενδόνη", "h"], hellenike: ["Ἑλληνική", "h"], pule: ["πύλη", "h"], phulake: ["φυλακή", "h"], pelte: ["πέλτη", "h"],
  agathe: ["ἀγαθή", "h"], stene: ["στενή", "h"],
  gefura: ["γέφυ_ρα", "sa"], machaira: ["μάχαιρα", "sa"], thalatta: ["θάλαττα", "sh"], hamaxa: ["ἅμαξα", "sh"], trapeza: ["τράπεζα", "sh"],
  luo: ["λύ_ω", "v"], bouleuo: ["βουλεύω", "v"], pempo: ["πέμπω", "v"], harpazo: ["ἁρπάζω", "v"], ago: ["ἄγω", "v"], echo: ["ἔχω", "v"]
};

const MAP = {};
function key(s) { return String(s).normalize("NFD").replace(/̀/g, "́").normalize("NFC").toLowerCase(); }
function bare(s) { return String(s).normalize("NFD").replace(/[̀-ͯ_?]/g, "").toLowerCase(); }
function isG(ch) { return /[Ͱ-Ͽἀ-῿]/.test(ch) && !/[᾽᾿·;]/.test(ch); }
/* 記法つきの語 → {w: きれいな語, L: 長い母音の位置, U: 未確定の位置}（位置＝ギリシア文字だけを数えた番号） */
function parse(n) {
  const L = new Set(), U = new Set(); let w = "", i = -1;
  for (const ch of n.normalize("NFD")) {
    if (ch === "_") { L.add(i); continue; }
    if (ch === "?") { U.add(i); continue; }
    if (!/[̀-ͯ]/.test(ch) && isG(ch)) i++;
    w += ch;
  }
  return { w: w.normalize("NFC"), L, U };
}
function put(w, L, U) { MAP[key(w)] = { L, U: U || new Set() }; }
WORDS.trim().split(/\s+/).forEach(n => { const p = parse(n); put(p.w, p.L, p.U); });
/* 変化表から：語幹の長さは主格単数から写し、語尾の α は型と格で決める */
Object.keys(PAR).forEach(id => {
  const p = C.par[id]; if (!p) return;
  const spec = parse(PAR[id][0]), type = PAR[id][1], NB = bare(spec.w), stem = NB.slice(0, -1);
  const forms = type === "v" ? p.f.concat([p.f[5] + "ν"]).map(f => [f, -1, -1]) :
    p.sg.map((f, i) => [f, 0, i]).concat(p.pl.map((f, i) => [f, 1, i]));
  forms.forEach(([f, pl, cs]) => {
    const B = bare(f), L = new Set();
    if (B.slice(0, stem.length) === stem) spec.L.forEach(ix => { if (ix < stem.length) L.add(ix); });
    if (type !== "v" && B.charAt(stem.length) === "α" && B.charAt(stem.length + 1) !== "ι") {
      const long = pl ? cs === 3 : (type === "a" ? true : cs === 1);
      if (long) L.add(stem.length);
    }
    put(f, L);
  });
});

/* ---- 3. 変換 ---- */
const DIPH = { "αι": 1, "ει": 1, "οι": 1, "υι": 1, "αυ": 1, "ευ": 1, "ηυ": 1, "ου": 1, "ωυ": 1 };
const CONS_R = { β: "b", γ: "g", δ: "d", ζ: "z", θ: "th", κ: "k", λ: "l", μ: "m", ν: "n", ξ: "x", π: "p", ρ: "r", σ: "s", ς: "s", τ: "t", φ: "ph", χ: "ch", ψ: "ps" };
const CONS_I = { β: "b", γ: "g", δ: "d", ζ: "zd", θ: "tʰ", κ: "k", λ: "l", μ: "m", ν: "n", ξ: "ks", π: "p", ρ: "r", σ: "s", ς: "s", τ: "t", φ: "pʰ", χ: "kʰ", ψ: "ps" };
const ACU = "́", GRA = "̀", CIRC = "͂", SUB = "ͅ", ROUGH = "̔", DIA = "̈";
/* 語を文字（基本の字＋記号）に分ける */
function units(word) {
  const out = [];
  for (const ch of word.normalize("NFD")) {
    if (/[̀-ͯ]/.test(ch)) { if (out.length && out[out.length - 1].g) out[out.length - 1].m += ch; continue; }
    const g = isG(ch);
    out.push({ c: g ? ch.toLowerCase() : ch, up: g && ch !== ch.toLowerCase(), m: "", g });
  }
  return out;
}
function info(word) {
  const k = key(word.replace(/[^Ͱ-Ͽἀ-῿̀-ͯ]/g, "")).replace(/[᾿᾽]/g, "");
  return MAP[k] || null;
}
/* 音節の核（母音・二重母音）をまとめる */
function nuclei(us) {
  const res = []; let gi = -1;
  for (let i = 0; i < us.length; i++) {
    const u = us[i];
    if (!u.g) { res.push({ t: "x", s: u.c }); continue; }
    gi++;
    const v = "αεηιουω".indexOf(u.c) >= 0;
    if (!v) { res.push({ t: "c", c: u.c, m: u.m, up: u.up, gi }); continue; }
    const n = us[i + 1];
    if (n && n.g && DIPH[u.c + n.c] && n.m.indexOf(DIA) < 0 && !/[̀-̂̓̔͂]/.test(u.m)) {
      res.push({ t: "d", a: u.c, b: n.c, m: u.m + n.m, up: u.up, gi, gi2: gi + 1 }); i++; gi++; continue;
    }
    res.push({ t: "v", c: u.c, m: u.m, up: u.up, gi });
  }
  return res;
}
function accentOf(m) { return m.indexOf(CIRC) >= 0 ? "c" : m.indexOf(ACU) >= 0 ? "a" : m.indexOf(GRA) >= 0 ? "g" : ""; }
/* 長さ：1＝長い、0＝短い、-1＝未確定 */
function len(n, inf) {
  if (n.c === "η" || n.c === "ω") return 1;
  if (n.c === "ε" || n.c === "ο") return 0;
  if (n.m.indexOf(CIRC) >= 0 || n.m.indexOf(SUB) >= 0) return 1;
  if (!inf || inf.U.has(n.gi)) return -1;
  return inf.L.has(n.gi) ? 1 : 0;
}
function cap(s) { return s.charAt(0).toUpperCase() + s.slice(1); }
function roman(word) {
  const inf = info(word), ns = nuclei(units(word)); let out = "", first = true, up = false;
  ns.forEach((n, k) => {
    if (n.t === "x") { out += n.s === "᾿" || n.s === "᾽" ? "’" : n.s; return; }
    if (first) { up = n.up; }
    const rough = first && n.m.indexOf(ROUGH) >= 0; first = false;
    if (n.t === "c") {
      if (n.c === "γ") { const nx = ns[k + 1]; out += nx && nx.t === "c" && "γκχξ".indexOf(nx.c) >= 0 ? "n" : "g"; return; }
      out += n.c === "ρ" && rough ? "rh" : CONS_R[n.c]; return;
    }
    const acc = accentOf(n.m), am = acc === "a" ? ACU : acc === "g" ? GRA : acc === "c" ? "̂" : "";
    if (rough) out += "h";
    if (n.t === "d") {
      const a = n.a === "η" ? "ē" : n.a === "ω" ? "ō" : n.a === "υ" ? "u" : { α: "a", ε: "e", ο: "o" }[n.a];
      const b = n.b === "υ" ? "u" : "i";
      out += a + b + am;
      return;
    }
    const l = len(n, inf), base = { α: "a", ε: "e", η: "e", ι: "i", ο: "o", υ: "y", ω: "o" }[n.c];
    const sub = n.m.indexOf(SUB) >= 0 ? "i" : "";
    if (acc === "c") out += base + "̂" + sub;
    else out += base + (l === 1 ? "̄" : "") + am + sub;
  });
  out = out.normalize("NFC");
  return up ? cap(out) : out;
}
function ipa(word) {
  const inf = info(word), ns = nuclei(units(word)); let out = "", first = true, unk = false;
  ns.forEach((n, k) => {
    if (n.t === "x") { return; }
    const rough = first && n.m.indexOf(ROUGH) >= 0; first = false;
    if (n.t === "c") {
      const nx = ns[k + 1];
      if (n.c === "γ" && nx && nx.t === "c" && "γκχξ".indexOf(nx.c) >= 0) { out += "ŋ"; return; }
      if (n.c === "ρ" && rough) { out += "r̥"; return; }
      if ((n.c === "σ") && nx && nx.t === "c" && "βγδμ".indexOf(nx.c) >= 0) { out += "z"; return; }
      out += CONS_I[n.c]; return;
    }
    if (rough) out += "h";
    const acc = accentOf(n.m);
    let core, long = true;
    if (n.t === "d") {
      const pair = n.a + n.b;
      if (pair === "ει") core = ["e", "ː"]; else if (pair === "ου") core = ["u", "ː"];
      else core = [{ α: "a", ε: "e", ο: "o", η: "ɛ", υ: "y", ω: "ɔ" }[n.a], (n.a === "η" || n.a === "ω" ? "ː" : "") + (n.b === "ι" ? "i̯" : "u̯")];
    } else {
      const sub = n.m.indexOf(SUB) >= 0, l = len(n, inf), q = { α: "a", ε: "e", η: "ɛ", ι: "i", ο: "o", υ: "y", ω: "ɔ" }[n.c];
      if (l === -1) { unk = true; long = false; core = [q, "(ː)"]; }
      else { long = l === 1; core = [q, (long ? "ː" : "") + (sub ? "i̯" : "")]; }
    }
    const mk = acc === "c" ? "̂" : acc === "a" ? (long ? "̌" : "́") : "";
    out += core[0] + mk + core[1];
  });
  return { s: out.normalize("NFC"), unk };
}
/* 句や文：語ごとに変換してつなぐ */
function read(text) {
  const ws = String(text).replace(/[«»"“”(),.;:·;!?·;]/g, " ").split(/\s+/).filter(w => w && isG(w.charAt(0)));
  let unk = false;
  const r = String(text).split(/(\s+)/).map(t => /[Ͱ-Ͽἀ-῿]/.test(t) ? t.replace(/[^\s«»"“”(),.;:·;!?·;]+/g, w => roman(w)) : t).join("").replace(/·/g, "·").replace(/;/g, ";");
  const i = ws.map(w => { const x = ipa(w); if (x.unk) unk = true; return x.s; }).join(" ");
  return { r, i, unk };
}
C.read = read; C.roman = roman; C.ipa = ipa; C.readInfo = info;
C.alphaIPA = { α: "a / aː", β: "b", γ: "g（ŋ）", δ: "d", ε: "e", ζ: "zd", η: "ɛː", θ: "tʰ", ι: "i / iː", κ: "k", λ: "l", μ: "m", ν: "n", ξ: "ks", ο: "o", π: "p", ρ: "r", σ: "s", τ: "t", υ: "y / yː", φ: "pʰ", χ: "kʰ", ψ: "ps", ω: "ɔː" };
})();
