/* Islamic Archive Audio Player
   Pure Vanilla JS architecture (modules via IIFE objects)
   - Archive.org Advanced Search + Metadata endpoints
   - Smart Arabic normalization + fuzzy match
   - Islamic-only filtering (blocked keywords)
   - Spotify-like UI, playlist drawer, advanced player, caching, history, favorites
*/

(() => {
  "use strict";

  /***********************
   * Utilities & Security
   ***********************/
  const Util = {
    qs: (sel, root = document) => root.querySelector(sel),
    qsa: (sel, root = document) => Array.from(root.querySelectorAll(sel)),
    clamp: (n, a, b) => Math.max(a, Math.min(b, n)),
    debounce(fn, ms = 250) {
      let t;
      return (...args) => {
        clearTimeout(t);
        t = setTimeout(() => fn(...args), ms);
      };
    },
    throttle(fn, ms = 250) {
      let last = 0;
      return (...args) => {
        const now = Date.now();
        if (now - last >= ms) {
          last = now;
          fn(...args);
        }
      };
    },
    // Escape to prevent XSS when inserting user/API data into HTML
    esc(str) {
      return String(str ?? "")
        .replaceAll("&", "&amp;")
        .replaceAll("<", "&lt;")
        .replaceAll(">", "&gt;")
        .replaceAll('"', "&quot;")
        .replaceAll("'", "&#039;");
    },
    // Basic safe text extraction
    safeText(v, max = 400) {
      const s = String(v ?? "").replace(/\s+/g, " ").trim();
      return s.length > max ? s.slice(0, max - 1) + "…" : s;
    },
    formatNumber(n) {
      const x = Number(n);
      if (!Number.isFinite(x)) return "—";
      return new Intl.NumberFormat("ar").format(x);
    },
    formatTime(sec) {
      sec = Math.max(0, Number(sec) || 0);
      const m = Math.floor(sec / 60);
      const s = Math.floor(sec % 60);
      return `${m}:${String(s).padStart(2, "0")}`;
    },
    uid() {
      return Math.random().toString(36).slice(2) + Date.now().toString(36);
    }
  };

  /***********************
   * Cache Manager
   ***********************/
  const Cache = (() => {
    const mem = new Map(); // key -> {t, v}
    const TTL_DEFAULT = 1000 * 60 * 10; // 10 min

    function get(key) {
      const it = mem.get(key);
      if (!it) return null;
      if (Date.now() - it.t > it.ttl) {
        mem.delete(key);
        return null;
      }
      return it.v;
    }

    function set(key, value, ttl = TTL_DEFAULT) {
      mem.set(key, { t: Date.now(), v: value, ttl });
      return value;
    }

    function getLS(key, fallback = null) {
      try {
        const raw = localStorage.getItem(key);
        if (!raw) return fallback;
        return JSON.parse(raw);
      } catch {
        return fallback;
      }
    }

    function setLS(key, value) {
      try {
        localStorage.setItem(key, JSON.stringify(value));
      } catch {}
    }

    return { get, set, getLS, setLS };
  })();

  /***********************
   * Arabic Normalization Engine
   ***********************/
  const Arabic = (() => {
    // tashkeel + tatweel
    const DIACRITICS = /[\u0610-\u061A\u064B-\u065F\u0670\u06D6-\u06ED]/g;
    const TATWEEL = /\u0640/g;

    const HAMZA_FORMS = /[أإآٱ]/g;
    const YA_FORMS = /[ى]/g;
    const TA_MARBUTA = /[ة]/g;

    // Common prefixes to optionally ignore during matching
    const PREFIXES = ["ال", "و", "ف", "ب", "ك", "ل", "لل"];

    function normalize(text) {
      let s = String(text ?? "");
      s = s.replace(DIACRITICS, "");
      s = s.replace(TATWEEL, "");
      s = s.replace(HAMZA_FORMS, "ا");
      s = s.replace(YA_FORMS, "ي");
      s = s.replace(TA_MARBUTA, "ه");
      s = s.replace(/ؤ/g, "و").replace(/ئ/g, "ي");
      s = s.replace(/\s+/g, " ").trim();
      // unify Arabic/Latin digits? keep as-is; but remove punctuation
      s = s.replace(/[^\p{L}\p{N}\s]/gu, " ");
      s = s.replace(/\s+/g, " ").trim();
      return s;
    }

    function tokenize(text) {
      const s = normalize(text);
      if (!s) return [];
      return s.split(" ").filter(Boolean);
    }

    function stripPrefixes(token) {
      let t = token;
      for (const p of PREFIXES) {
        if (t.startsWith(p) && t.length > p.length + 1) {
          t = t.slice(p.length);
          break;
        }
      }
      return t;
    }

    // Very light stemming-ish: remove common plural/affixes (approximate)
    function lightStem(token) {
      let t = stripPrefixes(token);
      // suffixes
      t = t.replace(/(ات|ون|ين|ان|يه|ية|ه|ها|هم|كما|كم|نا)$/g, (m) => {
        // keep meaningful short words
        if (t.length - m.length < 2) return m;
        return "";
      });
      // normalize again
      return normalize(t);
    }

    // Basic fuzzy: token containment + edit distance threshold for short tokens
    function levenshtein(a, b) {
      a = a || ""; b = b || "";
      const m = a.length, n = b.length;
      if (m === 0) return n;
      if (n === 0) return m;
      const dp = Array.from({ length: m + 1 }, () => new Array(n + 1).fill(0));
      for (let i = 0; i <= m; i++) dp[i][0] = i;
      for (let j = 0; j <= n; j++) dp[0][j] = j;
      for (let i = 1; i <= m; i++) {
        for (let j = 1; j <= n; j++) {
          const cost = a[i - 1] === b[j - 1] ? 0 : 1;
          dp[i][j] = Math.min(
            dp[i - 1][j] + 1,
            dp[i][j - 1] + 1,
            dp[i - 1][j - 1] + cost
          );
        }
      }
      return dp[m][n];
    }

    function fuzzyTokenMatch(qToken, textToken) {
      if (!qToken || !textToken) return false;
      if (textToken.includes(qToken) || qToken.includes(textToken)) return true;

      // For small tokens tolerate 1 edit, otherwise 2
      const d = levenshtein(qToken, textToken);
      const limit = qToken.length <= 4 ? 1 : 2;
      return d <= limit;
    }

    function buildSearchIndex(obj) {
      // Combine fields
      const fields = [
        obj?.title, obj?.creator, obj?.description, obj?.collection
      ].filter(Boolean).join(" ");
      const tokens = tokenize(fields).map(lightStem).filter(Boolean);
      return {
        raw: fields,
        norm: normalize(fields),
        tokens
      };
    }

    return { normalize, tokenize, lightStem, fuzzyTokenMatch, buildSearchIndex };
  })();

  /***********************
   * Islamic Content Filtering
   ***********************/
  const IslamicFilter = (() => {
    const blockedEN = [
      "music","rock","reggae","film","movie","cinema","rap","dance","dj","guitar",
      "instrumental","podcast","entertainment","netflix","anime","manga","pop","concert",
      "song","album"
    ];
    const blockedAR = [
      "موسيقى","اغاني","أغاني","فيلم","افلام","أفلام","رقص","روك","ريغي","بوب","حفلة",
      "سينما","تمثيل"
    ];

    // Islamic positive signals (boost + allow)
    const allowedSignalsAR = [
      "قران","قرآن","تلاوه","تلاوة","تجويد","حفص","ورش","شعبة",
      "تفسير","حديث","فقه","عقيده","عقيدة","سيره","سيرة","محاضره","محاضرة",
      "خطب","خطبه","خطبة","درس","دروس","فتاوى","فتوى","اذكار","أذكار",
      "سنه","سنة","صحيح","مسند","موطا","موطأ","رياض الصالحين",
      "اسلام","إسلام","السلف","توحيد","عقيده","شيخ","الشيخ","امام","إمام",
      "لغة عربية","نحو","صرف","بلاغه","بلاغة","تاريخ اسلامي"
    ];

    const blockedNorm = [...blockedEN, ...blockedAR].map(Arabic.normalize);

    function isBlocked(text) {
      const s = Arabic.normalize(text || "");
      if (!s) return false;
      return blockedNorm.some(w => w && s.includes(w));
    }

    function seemsIslamic(doc) {
      const combined = [
        doc?.title, doc?.creator, doc?.description,
        Array.isArray(doc?.collection) ? doc.collection.join(" ") : doc?.collection
      ].filter(Boolean).join(" ");

      if (isBlocked(combined)) return false;

      const norm = Arabic.normalize(combined);
      const signals = allowedSignalsAR.map(Arabic.normalize);

      // Strong allow if any signal appears
      if (signals.some(sig => sig && norm.includes(sig))) return true;

      // Otherwise, allow if in known Islamic-ish collections keywords
      // (soft heuristic; strict mode can require signals)
      const soft = ["islam", "quran", "qur", "hadith", "sunnah", "tafsir", "fiqh", "arabic"];
      const n2 = norm.toLowerCase();
      if (soft.some(k => n2.includes(k))) return true;

      return false;
    }

    return { isBlocked, seemsIslamic };
  })();

  /***********************
   * API Manager (Archive.org)
   ***********************/
  const API = (() => {
    const ADV = "https://archive.org/advancedsearch.php";
    const META = "https://archive.org/metadata/";

    async function fetchJSON(url, { retries = 2, timeoutMs = 12000 } = {}) {
      const ctrl = new AbortController();
      const t = setTimeout(() => ctrl.abort(), timeoutMs);

      try {
        const res = await fetch(url, { signal: ctrl.signal, headers: { "Accept": "application/json" } });
        if (!res.ok) throw new Error(`HTTP ${res.status}`);
        return await res.json();
      } catch (e) {
        if (retries > 0) {
          await new Promise(r => setTimeout(r, 450));
          return fetchJSON(url, { retries: retries - 1, timeoutMs });
        }
        throw e;
      } finally {
        clearTimeout(t);
      }
    }

    function buildQuery(userQuery, filterType, strictIslamic) {
      // Build IA query string. We restrict to audio mediatype.
      // We'll query widely, then apply client-side Islamic filtering.
      const qNorm = Arabic.normalize(userQuery);

      const base = [
        `mediatype:audio`,
        `-collection:(opensource_audio music audio_music)`,
        `-title:(${blockedIAQuery()})`,
        `-description:(${blockedIAQuery()})`
      ];

      // Domain type boost queries
      const typeMap = {
        all: "",
        quran: "(قرآن OR قران OR quran OR recitation OR تلاوة OR تلاوه OR tajweed OR تجويد)",
        tafsir: "(تفسير OR tafsir)",
        hadith: "(حديث OR hadith OR sunnah OR سنة OR سنه)",
        fiqh: "(فقه OR fiqh)",
        aqidah: "(عقيدة OR عقيده OR aqidah OR توحيد OR tawhid)",
        seerah: "(سيرة OR سيره OR seerah)",
        lectures: "(محاضرة OR محاضره OR درس OR دروس OR khutbah OR خطبة OR خطبه)",
        adhkar: "(أذكار OR اذكار OR adhkar)",
        arabic: "(نحو OR صرف OR بلاغة OR بلاغه OR لغة OR arabic)",
        history: "(تاريخ OR history OR اسلامي OR إسلامي)"
      };

      const typeQ = typeMap[filterType] || "";
      const userPart = qNorm
        ? `(title:(${escapeIA(qNorm)}) OR creator:(${escapeIA(qNorm)}) OR description:(${escapeIA(qNorm)}) OR collection:(${escapeIA(qNorm)}))`
        : `(title:(${typeQ || "اسلام OR إسلام OR quran OR hadith OR tafsir"}) OR description:(${typeQ || "اسلام OR إسلام OR quran OR hadith OR tafsir"}))`;

      const combined = [...base, typeQ ? `(${typeQ})` : "", userPart].filter(Boolean).join(" AND ");

      // strictIslamic: we still do client filtering; strict will later require positive signals
      return combined;
    }

    function blockedIAQuery() {
      const words = [
        "music","rock","reggae","film","movie","cinema","rap","dance","dj","guitar",
        "instrumental","netflix","anime","manga","pop","concert","song","album",
        "موسيقى","اغاني","أغاني","فيلم","افلام","أفلام","رقص","روك","ريغي","بوب","حفلة","سينما","تمثيل"
      ];
      return words.map(w => `"${w}"`).join(" OR ");
    }

    function escapeIA(s) {
      // Light escape for IA query syntax
      return String(s).replace(/[^\p{L}\p{N}\s]/gu, " ").trim();
    }

    async function search({ userQuery, filterType = "all", rows = 50, page = 1, sort = "downloads_desc" }) {
      const sortMap = {
        downloads_desc: "downloads desc",
        relevance: "", // IA default relevance (omit sort)
        title_asc: "titleSorter asc"
      };

      const q = buildQuery(userQuery, filterType, true);
      const fl = [
        "identifier","title","creator","description","mediatype","downloads","item_size","collection"
      ];

      const params = new URLSearchParams();
      params.set("q", q);
      fl.forEach(f => params.append("fl[]", f));
      params.set("rows", String(rows));
      params.set("page", String(page));
      if (sortMap[sort]) params.set("sort[]", sortMap[sort]);
      params.set("output", "json");

      const url = `${ADV}?${params.toString()}`;
      const cacheKey = `search:${rows}:${page}:${sort}:${filterType}:${Arabic.normalize(userQuery)}`;
      const cached = Cache.get(cacheKey);
      if (cached) return cached;

      const data = await fetchJSON(url);
      return Cache.set(cacheKey, data, 1000 * 60 * 6);
    }

    async function metadata(identifier) {
      const id = encodeURIComponent(identifier);
      const url = `${META}${id}`;
      const cacheKey = `meta:${identifier}`;
      const cached = Cache.get(cacheKey);
      if (cached) return cached;
      const data = await fetchJSON(url);
      return Cache.set(cacheKey, data, 1000 * 60 * 30);
    }

    return { search, metadata };
  })();

  /***********************
   * Search Engine
   ***********************/
  const Search = (() => {
    function scoreDoc(doc, qTokens) {
      const idx = Arabic.buildSearchIndex(doc);
      if (!qTokens.length) return 1;

      let score = 0;
      const textTokens = idx.tokens;

      for (const qt0 of qTokens) {
        const qt = Arabic.lightStem(qt0);
        if (!qt) continue;

        // exact containment in normalized string
        if (idx.norm.includes(qt)) score += 4;

        // fuzzy token matches
        let matched = false;
        for (const tt of textTokens) {
          if (Arabic.fuzzyTokenMatch(qt, tt)) {
            matched = true;
            break;
          }
        }
        if (matched) score += 2;
      }

      // Boost Quran-ish
      const norm = idx.norm;
      if (norm.includes("قران") || norm.includes("قرآن") || norm.includes("quran")) score += 1.5;
      return score;
    }

    function filterAndRank(docs, userQuery, strictIslamic) {
      const qTokens = Arabic.tokenize(userQuery);

      // Filter Islamic and block non-Islamic
      let filtered = docs.filter(d => {
        const combined = [d.title, d.creator, d.description, (d.collection || "")].join(" ");
        if (IslamicFilter.isBlocked(combined)) return false;

        const islamic = IslamicFilter.seemsIslamic(d);
        return strictIslamic ? islamic : true;
      });

      // Rank by our score (client relevance)
      filtered = filtered
        .map(d => ({ d, s: scoreDoc(d, qTokens) }))
        .sort((a, b) => b.s - a.s)
        .map(x => x.d);

      return filtered;
    }

    function suggest(userQuery) {
      const q = Arabic.normalize(userQuery);
      if (!q) return [];

      const tokens = Arabic.tokenize(q).slice(0, 6);

      const templates = [
        { tag: "قرآن", q: `${q} تلاوة` },
        { tag: "تفسير", q: `${q} تفسير` },
        { tag: "حديث", q: `${q} حديث` },
        { tag: "فقه", q: `${q} فقه` },
        { tag: "محاضرات", q: `${q} محاضرة` },
      ];

      // If already looks like category, just return token suggestions
      const tokenSug = tokens.map(t => ({ tag: "كلمة", q: t }));

      const uniq = new Map();
      [...templates, ...tokenSug].forEach(x => uniq.set(x.q, x));
      return Array.from(uniq.values()).slice(0, 8);
    }

    return { filterAndRank, suggest };
  })();

  /***********************
   * Playlist Manager
   ***********************/
  const Playlist = (() => {
    const state = {
      currentCollection: null,
      tracks: [],
      filteredTracks: [],
      sortMode: "track",
      sliceSize: 60,
      rendered: 0
    };

    function extractMP3Tracks(meta) {
      const files = meta?.files || [];

      // Explicit blocklist of non-playable formats/extensions
      const blockedFormats = ["zip","rar","tar","gz","7z","pdf","doc","docx","txt","html","htm","xml","json","csv","jpg","jpeg","png","gif","bmp","svg","mp4","avi","mkv","mov","wmv","m4v","rm","ra","ram","exe","iso","apk"];
      const blockedNames = blockedFormats.map(e => `.${e}`);

      // Keep only mp3 and playable sources
      const mp3 = files
        .filter(f => {
          const fmt = String(f?.format || "").toLowerCase();
          const name = String(f?.name || "").toLowerCase();
          if (blockedFormats.some(b => fmt.includes(b) || fmt === b)) return false;
          if (blockedNames.some(b => name.endsWith(b))) return false;
          return fmt.includes("mp3") || name.endsWith(".mp3");
        })
        .filter(f => !String(f?.name || "").toLowerCase().includes("_meta"))
        .map((f, i) => {
          const name = f.name;
          const title = f.title || f.original || name;
          const length = Number(f.length) || Number(f.duration) || 0;
          const track = {
            id: `${meta?.metadata?.identifier || "x"}:${name}:${i}`,
            name,
            title: Util.safeText(title, 160),
            duration: length,
            track: Number(f.track) || (i + 1),
            artist: Util.safeText(meta?.metadata?.creator || meta?.metadata?.uploader || "", 120),
            identifier: meta?.metadata?.identifier,
            // IA stream URL pattern
            url: `https://archive.org/download/${encodeURIComponent(meta?.metadata?.identifier)}/${encodeURIComponent(name)}`
          };
          return track;
        });

      // Deduplicate by URL
      const seen = new Set();
      return mp3.filter(t => (seen.has(t.url) ? false : (seen.add(t.url), true)));
    }

    function applyFilter(query) {
      const qTokens = Arabic.tokenize(query);
      if (!qTokens.length) {
        state.filteredTracks = [...state.tracks];
        return;
      }
      state.filteredTracks = state.tracks.filter(tr => {
        const idx = Arabic.buildSearchIndex({ title: tr.title, creator: tr.artist, description: tr.name, collection: "" });
        return qTokens.every(qt => idx.norm.includes(Arabic.lightStem(qt)) || idx.tokens.some(tt => Arabic.fuzzyTokenMatch(Arabic.lightStem(qt), tt)));
      });
    }

    function applySort(mode) {
      state.sortMode = mode;
      const arr = state.filteredTracks;

      if (mode === "duration") arr.sort((a, b) => (a.duration || 0) - (b.duration || 0));
      else if (mode === "title") arr.sort((a, b) => a.title.localeCompare(b.title, "ar"));
      else arr.sort((a, b) => (a.track || 0) - (b.track || 0));
    }

    function resetRender() {
      state.rendered = 0;
    }

    function nextSlice() {
      const start = state.rendered;
      const end = Math.min(state.filteredTracks.length, start + state.sliceSize);
      const slice = state.filteredTracks.slice(start, end);
      state.rendered = end;
      return slice;
    }

    function hasMore() {
      return state.rendered < state.filteredTracks.length;
    }

    return { state, extractMP3Tracks, applyFilter, applySort, resetRender, nextSlice, hasMore };
  })();

  /***********************
   * Audio Player Engine
   ***********************/
  const Player = (() => {
    const audio = Util.qs("#audio");
    const ui = {
      btnPlayPause: Util.qs("#btnPlayPause"),
      btnPrev: Util.qs("#btnPrevTrack"),
      btnNext: Util.qs("#btnNextTrack"),
      btnShuffle: Util.qs("#btnShuffle"),
      btnRepeat: Util.qs("#btnRepeat"),
      seek: Util.qs("#seek"),
      timeCurrent: Util.qs("#timeCurrent"),
      timeTotal: Util.qs("#timeTotal"),
      nowTitle: Util.qs("#nowTitle"),
      nowMeta: Util.qs("#nowMeta"),
      volume: Util.qs("#volume"),
      speed: Util.qs("#speed"),
      miniCover: Util.qs("#miniCover"),
      btnMini: Util.qs("#btnMini"),
    };

    const state = {
      queue: [],
      index: -1,
      playing: false,
      shuffle: false,
      repeat: "off", // off|one|all
      sleepTimerId: null,
      mini: false
    };

    function setQueue(tracks, startIndex = 0) {
      state.queue = tracks.slice();
      state.index = Util.clamp(startIndex, 0, Math.max(0, state.queue.length - 1));
      loadCurrent(true);
    }

    function current() {
      return state.queue[state.index] || null;
    }

    function setPlayingUI(isPlaying) {
      ui.btnPlayPause.textContent = isPlaying ? "❚❚" : "▶";
    }

    function loadCurrent(autoplay = false) {
      const tr = current();
      if (!tr) return;

      audio.src = tr.url;
      ui.nowTitle.textContent = tr.title || tr.name || "—";
      ui.nowMeta.textContent = [tr.artist, tr.identifier].filter(Boolean).join(" • ") || "—";

      // pseudo cover gradient changes
      ui.miniCover.style.background = `linear-gradient(135deg, rgba(12,155,88,.35), rgba(201,168,76,.12)), radial-gradient(400px 200px at 30% 30%, rgba(12,155,88,.25), transparent 55%)`;

      setPlayingUI(false);

      if ("mediaSession" in navigator) {
        try {
          navigator.mediaSession.metadata = new MediaMetadata({
            title: tr.title || tr.name,
            artist: tr.artist || "Islamic Archive",
            album: tr.identifier || "Internet Archive",
          });
        } catch {}
      }

      if (autoplay) play();
      UI.highlightActiveTrack();
      History.addRecent(tr);
    }

    async function play() {
      try {
        await audio.play();
        state.playing = true;
        setPlayingUI(true);
      } catch (e) {
        state.playing = false;
        setPlayingUI(false);
        UI.toast("تعذر التشغيل", "قد يكون الملف غير متاح أو يتطلب تفاعلاً من المستخدم. جرّب الضغط على تشغيل مرة أخرى.");
      }
    }

    function pause() {
      audio.pause();
      state.playing = false;
      setPlayingUI(false);
    }

    function toggle() {
      state.playing ? pause() : play();
    }

    function next() {
      if (!state.queue.length) return;

      if (state.shuffle) {
        state.index = Math.floor(Math.random() * state.queue.length);
      } else {
        state.index++;
        if (state.index >= state.queue.length) {
          if (state.repeat === "all") state.index = 0;
          else {
            state.index = state.queue.length - 1;
            pause();
            return;
          }
        }
      }
      loadCurrent(true);
    }

    function prev() {
      if (!state.queue.length) return;
      // if progressed > 3 sec, restart
      if ((audio.currentTime || 0) > 3) {
        audio.currentTime = 0;
        return;
      }
      state.index--;
      if (state.index < 0) state.index = 0;
      loadCurrent(true);
    }

    function setRepeat() {
      state.repeat = state.repeat === "off" ? "all" : state.repeat === "all" ? "one" : "off";
      const label = state.repeat === "off" ? "تكرار: إيقاف" : state.repeat === "all" ? "تكرار: الكل" : "تكرار: مقطع";
      UI.toast("التكرار", label);
      ui.btnRepeat.style.borderColor = state.repeat === "off" ? "var(--line)" : "var(--gold)";
    }

    function setShuffle() {
      state.shuffle = !state.shuffle;
      UI.toast("الخلط", state.shuffle ? "مفعل" : "متوقف");
      ui.btnShuffle.style.borderColor = state.shuffle ? "var(--gold)" : "var(--line)";
    }

    function setSpeed(v) {
      const rate = Number(v) || 1;
      audio.playbackRate = rate;
    }

    function setVolume(v) {
      audio.volume = Util.clamp(Number(v), 0, 1);
      Cache.setLS("iaap:volume", audio.volume);
    }

    function seekTo(ratio0to1) {
      if (!Number.isFinite(audio.duration) || audio.duration <= 0) return;
      audio.currentTime = audio.duration * ratio0to1;
    }

    function setupMediaSessionActions() {
      if (!("mediaSession" in navigator)) return;
      try {
        navigator.mediaSession.setActionHandler("play", play);
        navigator.mediaSession.setActionHandler("pause", pause);
        navigator.mediaSession.setActionHandler("previoustrack", prev);
        navigator.mediaSession.setActionHandler("nexttrack", next);
        navigator.mediaSession.setActionHandler("seekto", (e) => {
          if (typeof e.seekTime === "number") audio.currentTime = e.seekTime;
        });
      } catch {}
    }

    function setSleepTimer(minutes) {
      clearSleepTimer();
      const ms = minutes * 60 * 1000;
      state.sleepTimerId = setTimeout(() => {
        pause();
        UI.toast("مؤقت النوم", "تم إيقاف التشغيل.");
      }, ms);
      UI.toast("مؤقت النوم", `سيتم إيقاف التشغيل بعد ${minutes} دقيقة.`);
    }

    function clearSleepTimer() {
      if (state.sleepTimerId) clearTimeout(state.sleepTimerId);
      state.sleepTimerId = null;
    }

    function toggleMini() {
      state.mini = !state.mini;
      document.body.classList.toggle("is-mini-player", state.mini);
      ui.btnMini.textContent = state.mini ? "عادي" : "مصغّر";
    }

    function bind() {
      ui.btnPlayPause.addEventListener("click", toggle);
      ui.btnNext.addEventListener("click", next);
      ui.btnPrev.addEventListener("click", prev);
      ui.btnShuffle.addEventListener("click", setShuffle);
      ui.btnRepeat.addEventListener("click", setRepeat);

      ui.volume.addEventListener("input", () => setVolume(ui.volume.value));
      ui.speed.addEventListener("change", () => setSpeed(ui.speed.value));

      ui.seek.addEventListener("input", () => {
        const ratio = Number(ui.seek.value) / 1000;
        seekTo(ratio);
      });

      audio.addEventListener("timeupdate", Util.throttle(() => {
        const cur = audio.currentTime || 0;
        const dur = audio.duration || 0;
        ui.timeCurrent.textContent = Util.formatTime(cur);
        ui.timeTotal.textContent = Number.isFinite(dur) ? Util.formatTime(dur) : "0:00";
        const ratio = dur > 0 ? (cur / dur) : 0;
        ui.seek.value = String(Math.floor(ratio * 1000));
      }, 200));

      audio.addEventListener("ended", () => {
        if (state.repeat === "one") {
          audio.currentTime = 0;
          play();
        } else {
          next();
        }
      });

      ui.btnMini.addEventListener("click", toggleMini);

      // Keyboard shortcuts
      window.addEventListener("keydown", (e) => {
        const tag = (e.target && e.target.tagName) ? e.target.tagName.toLowerCase() : "";
        const typing = tag === "input" || tag === "textarea" || e.target?.isContentEditable;
        if (typing) return;

        if (e.code === "Space") { e.preventDefault(); toggle(); }
        if (e.code === "ArrowRight" && e.shiftKey) audio.currentTime = (audio.currentTime || 0) + 10;
        if (e.code === "ArrowLeft" && e.shiftKey) audio.currentTime = Math.max(0, (audio.currentTime || 0) - 10);
        if (e.code === "KeyN") next();
        if (e.code === "KeyP") prev();
      });

      setupMediaSessionActions();

      // Restore volume
      const v = Cache.getLS("iaap:volume", 0.9);
      ui.volume.value = String(v);
      audio.volume = v;
      setSpeed(ui.speed.value);
    }

    return {
      bind,
      setQueue,
      current,
      loadCurrent,
      play,
      pause,
      toggle,
      next,
      prev,
      setSleepTimer,
      clearSleepTimer,
      state
    };
  })();

  /***********************
   * Favorites + History
   ***********************/
  const Favorites = (() => {
    const KEY = "iaap:favorites";
    function all() { return Cache.getLS(KEY, []); }
    function has(identifier) { return all().some(x => x.identifier === identifier); }
    function toggle(collectionObj) {
      const cur = all();
      const idx = cur.findIndex(x => x.identifier === collectionObj.identifier);
      if (idx >= 0) cur.splice(idx, 1);
      else cur.unshift({ ...collectionObj, ts: Date.now() });
      Cache.setLS(KEY, cur.slice(0, 200));
      return idx < 0;
    }
    return { all, has, toggle };
  })();

  const History = (() => {
    const KEY = "iaap:recent";
    function all() { return Cache.getLS(KEY, []); }
    function addRecent(track) {
      const cur = all();
      const item = {
        id: track.id,
        title: track.title,
        artist: track.artist,
        identifier: track.identifier,
        url: track.url,
        ts: Date.now()
      };
      const filtered = cur.filter(x => x.url !== item.url);
      filtered.unshift(item);
      Cache.setLS(KEY, filtered.slice(0, 120));
    }
    return { all, addRecent };
  })();

  /***********************
   * UI Renderer + Router
   ***********************/
  const UI = (() => {
    const el = {
      sidebar: Util.qs(".sidebar"),
      btnSidebar: Util.qs("#btnSidebar"),
      netStatus: Util.qs("#netStatus"),

      searchInput: Util.qs("#searchInput"),
      btnSearch: Util.qs("#btnSearch"),
      btnClear: Util.qs("#btnClear"),
      btnVoice: Util.qs("#btnVoice"),
      suggestions: Util.qs("#suggestions"),

      filterType: Util.qs("#filterType"),
      filterSort: Util.qs("#filterSort"),
      filterRows: Util.qs("#filterRows"),
      filterStrict: Util.qs("#filterStrict"),
      filterRTL: Util.qs("#filterRTL"),

      resultsTitle: Util.qs("#resultsTitle"),
      resultsMeta: Util.qs("#resultsMeta"),
      resultsGrid: Util.qs("#resultsGrid"),
      pager: Util.qs("#pager"),
      btnPrev: Util.qs("#btnPrev"),
      btnNext: Util.qs("#btnNext"),
      pageInfo: Util.qs("#pageInfo"),
      breadcrumbs: Util.qs("#breadcrumbs"),

      drawer: Util.qs("#drawer"),
      btnCloseDrawer: Util.qs("#btnCloseDrawer"),
      drawerTitle: Util.qs("#drawerTitle"),
      drawerSub: Util.qs("#drawerSub"),
      drawerCover: Util.qs("#drawerCover"),
      btnPlayAll: Util.qs("#btnPlayAll"),
      trackList: Util.qs("#trackList"),
      listStatus: Util.qs("#listStatus"),
      btnLoadMoreTracks: Util.qs("#btnLoadMoreTracks"),
      playlistSearch: Util.qs("#playlistSearch"),
      btnFavCollection: Util.qs("#btnFavCollection"),

      toast: Util.qs("#toast"),

      modal: Util.qs("#modal"),
      modalTitle: Util.qs("#modalTitle"),
      modalBody: Util.qs("#modalBody"),
      modalFoot: Util.qs("#modalFoot"),
      btnCloseModal: Util.qs("#btnCloseModal"),

      btnSleepTimer: Util.qs("#btnSleepTimer"),
      btnOfflineCache: Util.qs("#btnOfflineCache"),
      btnRandom: Util.qs("#btnRandom"),
      btnManual: Util.qs("#btnManual"),
    };

    const appState = {
      route: "home",
      page: 1,
      lastQuery: "",
      lastDocs: [],
      strict: true,
      rows: 50
    };

    function toast(title, msg, ms = 2600) {
      el.toast.innerHTML = `
        <div class="t-title">${Util.esc(title)}</div>
        <div class="t-msg">${Util.esc(msg)}</div>
      `;
      el.toast.classList.add("is-open");
      clearTimeout(toast._t);
      toast._t = setTimeout(() => el.toast.classList.remove("is-open"), ms);
    }

    function setBreadcrumbs(parts) {
      el.breadcrumbs.textContent = parts.join(" / ");
    }

    function skeletonCards(n = 10) {
      el.resultsGrid.innerHTML = Array.from({ length: n }).map(() => `<div class="skeleton" aria-hidden="true"></div>`).join("");
    }

    function renderCards(docs) {
      el.resultsGrid.innerHTML = docs.map(doc => {
        const title = Util.safeText(doc.title || doc.identifier, 90);
        const creator = Util.safeText(doc.creator || "—", 70);
        const desc = Util.safeText(doc.description || "", 120);
        const downloads = Util.formatNumber(doc.downloads);
        const id = Util.esc(doc.identifier);

        return `
          <article class="card" tabindex="0" role="button" aria-label="فتح مجموعة ${Util.esc(title)}" data-id="${id}">
            <div class="card__top">
              <div class="badge">صوتي</div>
              <div class="kpi">${downloads} تحميل</div>
            </div>
            <div class="card__title">${Util.esc(title)}</div>
            <div class="card__meta">${Util.esc(creator)}${desc ? ` — ${Util.esc(desc)}` : ""}</div>
            <div class="card__foot">
              <div class="card__cta">فتح القائمة</div>
              <div class="tiny muted">${Util.esc(id)}</div>
            </div>
          </article>
        `;
      }).join("");

      Util.qsa(".card", el.resultsGrid).forEach(card => {
        const open = async () => openCollection(card.dataset.id);
        card.addEventListener("click", open);
        card.addEventListener("keydown", (e) => {
          if (e.key === "Enter" || e.key === " ") { e.preventDefault(); open(); }
        });
      });
    }

    function openDrawer(open) {
      el.drawer.classList.toggle("is-open", open);
      el.drawer.setAttribute("aria-hidden", open ? "false" : "true");
    }

    function renderTrackSlice(tracks, append = true) {
      const html = tracks.map((tr, idx) => {
        const dur = tr.duration ? Util.formatTime(tr.duration) : "—";
        const isActive = Player.current()?.url === tr.url;
        return `
          <div class="track ${isActive ? "is-active" : ""}" role="listitem"
               tabindex="0" data-url="${Util.esc(tr.url)}" data-id="${Util.esc(tr.id)}">
            <div class="track__idx">${append ? (Playlist.state.rendered - tracks.length + idx + 1) : (idx + 1)}</div>
            <div>
              <div class="track__title">${Util.esc(tr.title)}</div>
              <div class="track__meta">${Util.esc(tr.artist || tr.identifier || "")}</div>
            </div>
            <div class="track__dur">${Util.esc(dur)}</div>
          </div>
        `;
      }).join("");

      if (!append) el.trackList.innerHTML = html;
      else el.trackList.insertAdjacentHTML("beforeend", html);

      // bind click
      Util.qsa(".track", el.trackList).forEach(node => {
        if (node.dataset.bound) return;
        node.dataset.bound = "1";
        const playThis = () => {
          const url = node.dataset.url;
          const idx = Playlist.state.filteredTracks.findIndex(t => t.url === url);
          if (idx >= 0) {
            Player.setQueue(Playlist.state.filteredTracks, idx);
          }
        };
        node.addEventListener("click", playThis);
        node.addEventListener("keydown", (e) => {
          if (e.key === "Enter" || e.key === " ") { e.preventDefault(); playThis(); }
        });
      });
    }

    function highlightActiveTrack() {
      const url = Player.current()?.url;
      if (!url) return;
      Util.qsa(".track", el.trackList).forEach(t => {
        t.classList.toggle("is-active", t.dataset.url === url);
      });
    }

    async function openCollection(identifier) {
      openDrawer(true);
      el.trackList.innerHTML = "";
      el.listStatus.textContent = "جاري جلب البيانات...";
      el.drawerTitle.textContent = identifier;
      el.drawerSub.textContent = "—";

      try {
        const meta = await API.metadata(identifier);
        const title = Util.safeText(meta?.metadata?.title || identifier, 120);
        const creator = Util.safeText(meta?.metadata?.creator || meta?.metadata?.uploader || "", 120);
        const desc = Util.safeText(meta?.metadata?.description || "", 160);

        Playlist.state.currentCollection = {
          identifier,
          title,
          creator,
          description: desc
        };

        el.drawerTitle.textContent = title;
        el.drawerSub.textContent = [creator, identifier].filter(Boolean).join(" • ");

        // cover gradient variance
        el.drawerCover.style.background = `linear-gradient(135deg, rgba(12,155,88,.35), rgba(201,168,76,.12)), radial-gradient(400px 200px at 30% 30%, rgba(12,155,88,.25), transparent 55%)`;

        const tracks = Playlist.extractMP3Tracks(meta);
        Playlist.state.tracks = tracks;
        Playlist.state.filteredTracks = tracks.slice();
        Playlist.resetRender();

        // fav button state
        const fav = Favorites.has(identifier);
        el.btnFavCollection.style.borderColor = fav ? "var(--gold)" : "var(--line)";

        if (!tracks.length) {
          el.listStatus.textContent = "لا توجد ملفات MP3 ظاهرة في هذه المجموعة.";
          el.btnLoadMoreTracks.style.display = "none";
          return;
        }

        // initial render
        Playlist.applySort(Playlist.state.sortMode);
        const slice = Playlist.nextSlice();
        renderTrackSlice(slice, true);
        el.listStatus.textContent = `عدد المقاطع: ${Util.formatNumber(Playlist.state.filteredTracks.length)}`;
        el.btnLoadMoreTracks.style.display = Playlist.hasMore() ? "inline-flex" : "none";
      } catch (e) {
        el.listStatus.textContent = "تعذر جلب قائمة التشغيل. حاول لاحقاً.";
        toast("خطأ شبكة", String(e?.message || e));
      }
    }

    async function runSearch({ query, page = 1 } = {}) {
      const userQuery = (query ?? el.searchInput.value).trim();
      const rows = Number(el.filterRows.value) || 50;
      const filterType = el.filterType.value;
      const sort = el.filterSort.value;
      const strict = !!el.filterStrict.checked;

      appState.page = page;
      appState.lastQuery = userQuery;
      appState.rows = rows;
      appState.strict = strict;

      setBreadcrumbs(["بحث", userQuery || "استكشاف"]);
      el.resultsTitle.textContent = userQuery ? `نتائج البحث: ${userQuery}` : "محتوى إسلامي صوتي (استكشاف)";
      el.resultsMeta.textContent = "جاري التحميل...";
      skeletonCards(12);

      try {
        const data = await API.search({ userQuery, filterType, rows, page, sort });
        const docs = data?.response?.docs || [];
        const numFound = data?.response?.numFound || 0;

        const filtered = Search.filterAndRank(docs, userQuery, strict);
        appState.lastDocs = filtered;

        renderCards(filtered);

        el.resultsMeta.textContent =
          `المعروض: ${Util.formatNumber(filtered.length)} من ${Util.formatNumber(docs.length)} (إجمالي: ${Util.formatNumber(numFound)})`;

        el.pageInfo.textContent = `صفحة ${page}`;
        el.pager.style.display = "flex";
      } catch (e) {
        el.resultsGrid.innerHTML = "";
        el.resultsMeta.textContent = "فشل التحميل.";
        toast("تعذر البحث", "تحقق من اتصال الإنترنت أو أعد المحاولة.");
      }
    }

    function renderRoute(route) {
      appState.route = route;
      Util.qsa(".nav__item").forEach(b => b.classList.toggle("is-active", b.dataset.route === route));

      if (route === "favorites") {
        setBreadcrumbs(["المفضلة"]);
        el.resultsTitle.textContent = "المفضلة";
        const favs = Favorites.all();
        el.resultsMeta.textContent = `${Util.formatNumber(favs.length)} قائمة`;
        el.pager.style.display = "none";
        renderCards(favs.map(f => ({
          identifier: f.identifier,
          title: f.title,
          creator: f.creator,
          description: f.description,
          downloads: f.downloads || 0,
          collection: f.collection || ""
        })));
        return;
      }

      if (route === "recent") {
        setBreadcrumbs(["تم تشغيله مؤخراً"]);
        el.resultsTitle.textContent = "تم تشغيله مؤخراً";
        const rec = History.all();
        el.resultsMeta.textContent = `${Util.formatNumber(rec.length)} عنصر`;
        el.pager.style.display = "none";

        // Render as pseudo collections cards (open identifier)
        const docs = rec
          .filter(x => x.identifier)
          .slice(0, 60)
          .map(x => ({
            identifier: x.identifier,
            title: x.title,
            creator: x.artist,
            description: "عنصر من سجل التشغيل",
            downloads: 0,
            collection: ""
          }));

        renderCards(docs);
        return;
      }

      if (route === "trending") {
        el.searchInput.value = "قرآن تلاوة";
        el.filterSort.value = "downloads_desc";
        runSearch({ query: "قرآن تلاوة", page: 1 });
        return;
      }

      if (route === "reciters") {
        setBreadcrumbs(["قراء/مشايخ"]);
        el.resultsTitle.textContent = "أسماء مقترحة (اضغط للبحث)";
        el.resultsMeta.textContent = "قائمة سريعة";

        el.pager.style.display = "none";
        const names = [
          "عبدالباسط عبدالصمد", "المنشاوي", "الحصري", "السديس", "الشريم",
          "ابن عثيمين", "ابن باز", "الألباني", "الطبري", "ابن كثير", "النووي"
        ];

        el.resultsGrid.innerHTML = names.map(n => `
          <article class="card" tabindex="0" role="button" aria-label="بحث عن ${Util.esc(n)}" data-q="${Util.esc(n)}">
            <div class="card__top">
              <div class="badge">بحث</div>
              <div class="kpi">اقتراح</div>
            </div>
            <div class="card__title">${Util.esc(n)}</div>
            <div class="card__meta">اضغط للبحث عن مجموعات صوتية مرتبطة</div>
            <div class="card__foot">
              <div class="card__cta">بحث</div>
              <div class="tiny muted">IA</div>
            </div>
          </article>
        `).join("");

        Util.qsa(".card", el.resultsGrid).forEach(c => {
          const q = c.dataset.q;
          const go = () => { el.searchInput.value = q; runSearch({ query: q, page: 1 }); };
          c.addEventListener("click", go);
          c.addEventListener("keydown", (e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); go(); } });
        });
        return;
      }

      // home default
      setBreadcrumbs(["الرئيسية"]);
      if (!appState.lastQuery) {
        el.searchInput.value = "";
        runSearch({ query: "", page: 1 });
      } else {
        runSearch({ query: appState.lastQuery, page: appState.page });
      }
    }

    function openModal({ title, bodyHTML, footHTML }) {
      el.modalTitle.textContent = title;
      el.modalBody.innerHTML = bodyHTML;
      el.modalFoot.innerHTML = footHTML || "";
      el.modal.classList.add("is-open");
      el.modal.setAttribute("aria-hidden", "false");
    }

    function closeModal() {
      el.modal.classList.remove("is-open");
      el.modal.setAttribute("aria-hidden", "true");
    }

    function setupVoiceSearch() {
      const SR = window.SpeechRecognition || window.webkitSpeechRecognition;
      if (!SR) {
        el.btnVoice.title = "غير مدعوم في هذا المتصفح";
        return null;
      }
      const rec = new SR();
      rec.lang = "ar";
      rec.interimResults = false;
      rec.maxAlternatives = 1;

      rec.addEventListener("result", (e) => {
        const text = e.results?.[0]?.[0]?.transcript || "";
        if (text) {
          el.searchInput.value = text;
          runSearch({ query: text, page: 1 });
        }
      });
      rec.addEventListener("error", () => toast("بحث صوتي", "حدث خطأ في التعرف على الصوت."));
      return rec;
    }

    function bind() {
      // Sidebar toggle (mobile)
      el.btnSidebar.addEventListener("click", () => el.sidebar.classList.toggle("is-open"));

      // Online/offline
      const setNet = () => {
        const ok = navigator.onLine;
        el.netStatus.textContent = ok ? "● متصل" : "● غير متصل";
        el.netStatus.style.color = ok ? "var(--muted)" : "var(--warning)";
      };
      window.addEventListener("online", setNet);
      window.addEventListener("offline", setNet);
      setNet();

      // RTL toggle
      el.filterRTL.addEventListener("change", () => {
        const rtl = !!el.filterRTL.checked;
        document.documentElement.dir = rtl ? "rtl" : "ltr";
        document.documentElement.lang = rtl ? "ar" : "en";
      });

      // Search
      el.btnSearch.addEventListener("click", () => runSearch({ page: 1 }));
      el.searchInput.addEventListener("keydown", (e) => {
        if (e.key === "Enter") runSearch({ page: 1 });
      });
      el.btnClear.addEventListener("click", () => {
        el.searchInput.value = "";
        el.suggestions.classList.remove("is-open");
        el.suggestions.innerHTML = "";
        runSearch({ query: "", page: 1 });
      });

      // Suggestions (debounced)
      const suggestDebounced = Util.debounce(() => {
        const q = el.searchInput.value.trim();
        const items = Search.suggest(q);
        if (!items.length) {
          el.suggestions.classList.remove("is-open");
          el.suggestions.innerHTML = "";
          return;
        }
        el.suggestions.innerHTML = items.map(x => `
          <div class="sugg-item" role="option" tabindex="0" data-q="${Util.esc(x.q)}">
            <div class="sugg-item__q">${Util.esc(x.q)}</div>
            <div class="sugg-item__tag">${Util.esc(x.tag)}</div>
          </div>
        `).join("");
        el.suggestions.classList.add("is-open");

        Util.qsa(".sugg-item", el.suggestions).forEach(node => {
          const go = () => {
            el.searchInput.value = node.dataset.q;
            el.suggestions.classList.remove("is-open");
            runSearch({ query: node.dataset.q, page: 1 });
          };
          node.addEventListener("click", go);
          node.addEventListener("keydown", (e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); go(); } });
        });
      }, 220);

      el.searchInput.addEventListener("input", suggestDebounced);
      document.addEventListener("click", (e) => {
        if (!el.suggestions.contains(e.target) && e.target !== el.searchInput) el.suggestions.classList.remove("is-open");
      });

      // Paging
      el.btnPrev.addEventListener("click", () => runSearch({ query: appState.lastQuery, page: Math.max(1, appState.page - 1) }));
      el.btnNext.addEventListener("click", () => runSearch({ query: appState.lastQuery, page: appState.page + 1 }));

      // Drawer
      el.btnCloseDrawer.addEventListener("click", () => openDrawer(false));

      // Playlist: load more
      el.btnLoadMoreTracks.addEventListener("click", () => {
        const slice = Playlist.nextSlice();
        renderTrackSlice(slice, true);
        el.btnLoadMoreTracks.style.display = Playlist.hasMore() ? "inline-flex" : "none";
      });

      // Playlist: search inside
      el.playlistSearch.addEventListener("input", Util.debounce(() => {
        Playlist.applyFilter(el.playlistSearch.value);
        Playlist.applySort(Playlist.state.sortMode);
        Playlist.resetRender();
        el.trackList.innerHTML = "";
        const slice = Playlist.nextSlice();
        renderTrackSlice(slice, true);
        el.listStatus.textContent = `عدد المقاطع: ${Util.formatNumber(Playlist.state.filteredTracks.length)}`;
        el.btnLoadMoreTracks.style.display = Playlist.hasMore() ? "inline-flex" : "none";
      }, 220));

      // Playlist sort buttons
      Util.qsa(".seg__btn").forEach(b => {
        b.addEventListener("click", () => {
          Util.qsa(".seg__btn").forEach(x => x.classList.toggle("is-active", x === b));
          Playlist.applySort(b.dataset.sort);
          Playlist.resetRender();
          el.trackList.innerHTML = "";
          renderTrackSlice(Playlist.nextSlice(), true);
          el.btnLoadMoreTracks.style.display = Playlist.hasMore() ? "inline-flex" : "none";
        });
      });

      // Play all
      el.btnPlayAll.addEventListener("click", () => {
        if (!Playlist.state.filteredTracks.length) return;
        Player.setQueue(Playlist.state.filteredTracks, 0);
      });

      // Favorite collection
      el.btnFavCollection.addEventListener("click", () => {
        const c = Playlist.state.currentCollection;
        if (!c) return;
        const added = Favorites.toggle(c);
        el.btnFavCollection.style.borderColor = added ? "var(--gold)" : "var(--line)";
        toast("المفضلة", added ? "تمت الإضافة إلى المفضلة" : "تمت الإزالة من المفضلة");
      });

      // Router
      Util.qsa(".nav__item").forEach(b => {
        b.addEventListener("click", () => renderRoute(b.dataset.route));
      });

      // Modal
      el.btnCloseModal.addEventListener("click", closeModal);
      el.modal.addEventListener("click", (e) => {
        if (e.target?.dataset?.close) closeModal();
      });

      // Sleep Timer
      el.btnSleepTimer.addEventListener("click", () => {
        openModal({
          title: "مؤقت النوم",
          bodyHTML: `
            <div class="tiny muted" style="line-height:1.7">
              اختر مدة لإيقاف التشغيل تلقائياً (مفيد عند الاستماع قبل النوم).
            </div>
            <div style="display:flex; gap:10px; flex-wrap:wrap; margin-top:12px">
              <button class="btn btn--ghost" data-min="10">10 دقائق</button>
              <button class="btn btn--ghost" data-min="20">20 دقيقة</button>
              <button class="btn btn--ghost" data-min="30">30 دقيقة</button>
              <button class="btn btn--ghost" data-min="60">60 دقيقة</button>
            </div>
          `,
          footHTML: `
            <button class="btn btn--ghost" id="btnCancelTimer">إلغاء المؤقت</button>
          `
        });

        Util.qsa('[data-min]', el.modalBody).forEach(btn => {
          btn.addEventListener("click", () => {
            const m = Number(btn.dataset.min);
            Player.setSleepTimer(m);
            closeModal();
          });
        });
        Util.qs("#btnCancelTimer", el.modalFoot).addEventListener("click", () => {
          Player.clearSleepTimer();
          toast("مؤقت النوم", "تم الإلغاء.");
          closeModal();
        });
      });

      // Offline caching (metadata of current collection)
      el.btnOfflineCache.addEventListener("click", async () => {
        const c = Playlist.state.currentCollection;
        if (!c?.identifier) return toast("الحفظ", "افتح مجموعة أولاً ثم اضغط حفظ.");

        try {
          const meta = await API.metadata(c.identifier);
          Cache.setLS(`iaap:offline:${c.identifier}`, {
            ts: Date.now(),
            identifier: c.identifier,
            metadata: meta?.metadata || {},
            files: meta?.files || []
          });
          toast("تم الحفظ", "تم حفظ بيانات القائمة محلياً.");
        } catch {
          toast("فشل الحفظ", "تعذر جلب البيانات للحفظ.");
        }
      });

      // Random suggestion
      el.btnRandom.addEventListener("click", () => {
        const ideas = ["تفسير ابن كثير", "صحيح البخاري", "دروس فقه", "سيرة نبوية", "أذكار", "تلاوة قرآن", "شرح العقيدة", "رياض الصالحين"];
        const q = ideas[Math.floor(Math.random() * ideas.length)];
        el.searchInput.value = q;
        runSearch({ query: q, page: 1 });
      });

      // User manual
      el.btnManual.addEventListener("click", () => {
        openModal({
          title: "📖 دليل المستخدم",
          bodyHTML: `
<style>
  .manual{ max-width:600px; margin:0 auto; }
  .manual h4{ margin:16px 0 6px; color:var(--gold); font-size:14px; font-weight:900; }
  .manual h4:first-child{ margin-top:0; }
  .manual p, .manual li{ font-size:13px; line-height:1.7; color:var(--muted); margin:4px 0; }
  .manual ul{ padding-${document.documentElement.dir === 'rtl' ? 'right' : 'left'}:18px; margin:4px 0; }
  .manual kbd{ background:rgba(255,255,255,.08); border:1px solid var(--line); border-radius:6px; padding:2px 7px; font-size:12px; font-family:inherit; color:var(--text); }
  .manual em{ color:var(--accent); font-style:normal; }
</style>
<div class="manual">
  <h4>🔍 البحث</h4>
  <p>اكتب كلمة أو عبارة في شريط البحث العلوي (يدعم العربية الفصحى، يتجاهل التشكيل والهمزات). تظهر الاقتراحات تلقائياً أثناء الكتابة.</p>

  <h4>🎯 الفلاتر</h4>
  <ul>
    <li><em>النوع</em> — اختر تصنيفاً: قرآن، تفسير، حديث، فقه، عقيدة، سيرة، محاضرات، أذكار، علوم لغة، تاريخ إسلامي.</li>
    <li><em>ترتيب النتائج</em> — الأكثر تحميلاً، الأكثر صلة، أو العنوان.</li>
    <li><em>فلترة إسلامية صارمة</em> — عند التفعيل، تُعرض فقط النتائج التي تحتوي على كلمات إسلامية واضحة.</li>
    <li><em>عرض RTL</em> — تبديل اتجاه الكتابة (يمين→يسار / يسار→يمين).</li>
  </ul>

  <h4>📂 التصفح والنتائج</h4>
  <p>اضغط على أي بطاقة لفتح قائمة التشغيل الخاصة بها. استخدم <kbd>←</kbd> و <kbd>→</kbd> أسفل النتائج للتنقل بين الصفحات.</p>

  <h4>▶️ مشغل الصوت</h4>
  <ul>
    <li><em>تشغيل/إيقاف</em> — ⏎ مسطرة المسافة أو زر ▶/❚❚.</li>
    <li><em>السابق/التالي</em> — ⟨⟨ / ⟩⟩ أو <kbd>P</kbd> / <kbd>N</kbd>.</li>
    <li><em>تقديم/ترجيع</em> — <kbd>⇧+→</kbd> / <kbd>⇧+←</kbd> (10 ثوانٍ).</li>
    <li><em>الخلط</em> — ⤮ تشغيل عشوائي للمقاطع.</li>
    <li><em>التكرار</em> — ⟲ إيقاف ← تكرار الكل ← تكرار مقطع واحد.</li>
    <li><em>السرعة</em> — اختر من 0.75× إلى 2×.</li>
  </ul>

  <h4>📋 قائمة التشغيل (Drawer)</h4>
  <p>تظهر عند فتح مجموعة. يمكنك:</p>
  <ul>
    <li>🔍 البحث داخل القائمة لتصفية المقاطع.</li>
    <li>📊 ترتيبها حسب: الترتيب الأصلي، العنوان، أو المدة.</li>
    <li>▶️ تشغيل الكل دفعة واحدة.</li>
    <li>❤️ إضافة المجموعة إلى المفضلة.</li>
    <li>⬇︎ حفظ بيانات القائمة محلياً (للوصول دون اتصال).</li>
  </ul>

  <h4>⭐ المفضلة والتاريخ</h4>
  <p>من القائمة الجانبية: <em>المفضلة</em> تعرض كل المجموعات التي أضفتها، <em>تم تشغيله مؤخراً</em> يعرض تاريخ استماعك.</p>

  <h4>⏾ مؤقت النوم</h4>
  <p>اضبط مؤقتاً لإيقاف التشغيل تلقائياً بعد 10, 20, 30, أو 60 دقيقة.</p>

  <h4>🎙 البحث الصوتي</h4>
  <p>اضغط على أيقونة الميكروفون 🎙 في شريط البحث وتحدث بالعربية. (يتطلب متصفحاً يدعم Web Speech API).</p>

  <h4>🎚️ المصغّر</h4>
  <p>زر <em>مصغّر</em> في شريط المشغل يقلّص حجم المشغل ليتناسب مع المساحات الصغيرة.</p>

  <h4>⌨️ اختصارات لوحة المفاتيح</h4>
  <ul>
    <li><kbd>Space</kbd> — تشغيل/إيقاف</li>
    <li><kbd>⇧+→</kbd> — تقديم 10 ثوانٍ</li>
    <li><kbd>⇧+←</kbd> — ترجيع 10 ثوانٍ</li>
    <li><kbd>N</kbd> — المقطع التالي</li>
    <li><kbd>P</kbd> — المقطع السابق</li>
  </ul>
</div>
          `,
          footHTML: `<button class="btn btn--ghost" data-close="1">إغلاق</button>`
        });
      });

      // Voice search
      const rec = setupVoiceSearch();
      if (rec) {
        el.btnVoice.addEventListener("click", () => {
          try {
            rec.start();
            toast("بحث صوتي", "تحدث الآن...");
          } catch {
            // some browsers throw if started twice
          }
        });
      } else {
        el.btnVoice.addEventListener("click", () => toast("بحث صوتي", "غير مدعوم في هذا المتصفح."));
      }
    }

    return {
      bind,
      runSearch,
      renderRoute,
      openCollection,
      toast,
      setBreadcrumbs,
      highlightActiveTrack
    };
  })();

  /***********************
   * Boot
   ***********************/
  function boot() {
    Player.bind();
    UI.bind();

    // Initial route
    UI.renderRoute("home");

    // Open from hash (#id=...)
    const m = location.hash.match(/id=([^&]+)/);
    if (m?.[1]) {
      const id = decodeURIComponent(m[1]);
      UI.openCollection(id);
    }
  }

  boot();
})();