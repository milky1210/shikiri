(() => {
  "use strict";

  const RANKS = ["3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A", "2"];
  const SUITS = [
    { key: "S", symbol: "♠", name: "スペード", red: false },
    { key: "H", symbol: "♥", name: "ハート", red: true },
    { key: "D", symbol: "♦", name: "ダイヤ", red: true },
    { key: "C", symbol: "♣", name: "クラブ", red: false },
  ];
  const DECK = [
    ...SUITS.flatMap((s) => RANKS.map((rank) => `${s.key}${rank}`)),
    "J1", "J2",
  ];
  const MAX_DEALS = 1800;
  const MAX_NODES = 65000;
  const PATTERNS = window.TSUMI_PATTERNS || [];
  const PROBLEMS = window.TSUMI_PROBLEMS || [];

  const el = (id) => document.getElementById(id);
  const els = (q) => [...document.querySelectorAll(q)];
  const clone = (value) => structuredClone(value);
  const sameCards = (a, b) => [...a].sort().join("|") === [...b].sort().join("|");
  const cardSort = (a, b) => {
    const ca = parseCard(a), cb = parseCard(b);
    if (ca.joker !== cb.joker) return ca.joker ? 1 : -1;
    if (ca.joker) return a.localeCompare(b);
    return ca.rank - cb.rank || ca.suit.localeCompare(cb.suit);
  };

  let draft = {
    mine: ["S4", "C4", "H8", "D8"],
    candidates: ["S5", "H5", "D6", "C6", "S7", "H7"],
    counts: [2, 2],
  };
  let puzzle = clone(draft);
  let pickerTarget = "mine";
  let selected = new Set();
  let initialBelief = [];
  let belief = [];
  let dealInfo = { count: 0, truncated: false };
  let solver = null;
  let safeActions = [];
  let history = [];
  let finished = false;
  let toastTimer;
  let libraryPattern = "all";
  let libraryDifficulty = "all";
  let libraryResults = new Map();
  let auditRunning = false;
  let activeProblemId = null;
  let challengeMode = false;
  let challengeHintLevel = 0;
  let challengeRevealed = false;
  const challengeAttempts = new Map();
  const CLEAR_STORAGE_KEY = "tsumi-daifugo-clears-v2";
  let clearedProblems = loadClearedProblems();

  function loadClearedProblems() {
    try {
      const saved = JSON.parse(localStorage.getItem(CLEAR_STORAGE_KEY) || "[]");
      return new Set(Array.isArray(saved) ? saved.filter((id) => PROBLEMS.some((problem) => problem.id === id)) : []);
    } catch (_) {
      return new Set();
    }
  }

  function saveClearedProblems() {
    try { localStorage.setItem(CLEAR_STORAGE_KEY, JSON.stringify([...clearedProblems])); } catch (_) { /* private preview */ }
  }

  function parseCard(id) {
    if (id[0] === "J") return { id, joker: true, rank: 99, rankLabel: "JK", suit: "J", symbol: "★", red: false };
    const suit = SUITS.find((s) => s.key === id[0]);
    const rankLabel = id.slice(1);
    return { id, joker: false, rank: RANKS.indexOf(rankLabel), rankLabel, suit: suit.key, symbol: suit.symbol, red: suit.red };
  }

  function cardLabel(id) {
    const c = parseCard(id);
    return c.joker ? "JOKER" : `${c.symbol}${c.rankLabel}`;
  }

  function formatAction(action) {
    if (action.kind === "pass") return "パス";
    const cards = action.cards.map(cardLabel).join(" ");
    if (action.type === "straight") return `${cards}（階段）`;
    return cards;
  }

  function rankPower(rank, revolution) {
    if (rank === 99) return 99;
    return revolution ? 12 - rank : rank;
  }

  function actionPower(action, revolution) {
    if (action.rank === 99) return 99;
    if (action.type === "straight") {
      const values = action.sequence.map((r) => rankPower(r, revolution));
      return Math.min(...values);
    }
    return rankPower(action.rank, revolution);
  }

  function combinations(items, count, start = 0, picked = [], output = []) {
    if (picked.length === count) {
      output.push([...picked]);
      return output;
    }
    for (let i = start; i <= items.length - (count - picked.length); i += 1) {
      picked.push(items[i]);
      combinations(items, count, i + 1, picked, output);
      picked.pop();
    }
    return output;
  }

  function makeAction(type, cards, extra = {}) {
    const sorted = [...cards].sort(cardSort);
    const natural = sorted.map(parseCard).filter((c) => !c.joker);
    const containsJoker = natural.length !== sorted.length;
    const action = {
      kind: "play",
      type,
      cards: sorted,
      count: sorted.length,
      containsJoker,
      naturalSuits: natural.map((c) => c.suit).sort(),
      ...extra,
    };
    action.key = [type, sorted.join(","), action.rank ?? "", (action.sequence || []).join("-")].join(":");
    return action;
  }

  function analyzeSubset(ids) {
    const cards = ids.map(parseCard);
    const naturals = cards.filter((c) => !c.joker);
    const jokers = cards.length - naturals.length;
    const out = [];

    if (ids.length === 1) {
      const card = cards[0];
      out.push(makeAction("group", ids, {
        rank: card.joker ? 99 : card.rank,
        isJokerSingle: card.joker,
        contains8: !card.joker && card.rankLabel === "8",
        isSpade3: !card.joker && card.id === "S3",
      }));
      return out;
    }

    const naturalRanks = [...new Set(naturals.map((c) => c.rank))];
    if ((naturalRanks.length === 1 && naturals.length + jokers === ids.length) || (naturals.length === 0 && ids.length === 2)) {
      const rank = naturals.length ? naturalRanks[0] : 99;
      out.push(makeAction("group", ids, {
        rank,
        isJokerSingle: false,
        contains8: rank === RANKS.indexOf("8"),
        isSpade3: false,
      }));
    }

    if (ids.length >= 3 && naturals.length) {
      const suits = [...new Set(naturals.map((c) => c.suit))];
      const ranks = [...new Set(naturals.map((c) => c.rank))];
      if (suits.length === 1 && ranks.length === naturals.length) {
        for (let start = 0; start <= RANKS.length - ids.length; start += 1) {
          const sequence = Array.from({ length: ids.length }, (_, i) => start + i);
          const fits = ranks.every((rank) => sequence.includes(rank));
          const missing = sequence.filter((rank) => !ranks.includes(rank)).length;
          if (fits && missing === jokers) {
            out.push(makeAction("straight", ids, {
              rank: start,
              sequence,
              straightSuit: suits[0],
              isJokerSingle: false,
              contains8: false,
              isSpade3: false,
            }));
          }
        }
      }
    }
    return out;
  }

  function allPlays(hand) {
    if (hand.length > 11) return [];
    const byKey = new Map();
    const total = 1 << hand.length;
    for (let mask = 1; mask < total; mask += 1) {
      const ids = hand.filter((_, index) => mask & (1 << index));
      for (const action of analyzeSubset(ids)) byKey.set(action.key, action);
    }
    return [...byKey.values()];
  }

  function matchesLock(action, lock) {
    if (!lock) return true;
    if (action.count !== lock.length) return false;
    const remaining = [...lock];
    for (const suit of action.naturalSuits) {
      const index = remaining.indexOf(suit);
      if (index < 0) return false;
      remaining.splice(index, 1);
    }
    return remaining.length === action.cards.filter((id) => parseCard(id).joker).length;
  }

  function legalPlay(world, player, action) {
    if (!world.active[player]) return false;
    if (!action.cards.every((id) => world.hands[player].includes(id))) return false;
    if (world.field && world.passed[player]) return false;
    if (!world.field) return true;

    const field = world.field;
    if (field.isJokerSingle && action.isSpade3 && action.count === 1) return true;
    if (field.type !== action.type || field.count !== action.count) return false;
    if (!matchesLock(action, world.lock)) return false;
    return actionPower(action, world.revolution) > actionPower(field, world.revolution);
  }

  function legalActions(world, player) {
    if (!world.active[player]) return [];
    if (world.field && world.passed[player]) return [{ kind: "pass", key: "PASS" }];
    const plays = allPlays(world.hands[player]).filter((action) => legalPlay(world, player, action));
    if (world.field) plays.push({ kind: "pass", key: "PASS" });
    return plays;
  }

  function identicalNaturalSuits(a, b) {
    if (a.containsJoker || b.containsJoker || a.count !== b.count) return null;
    const aa = [...a.naturalSuits].sort();
    const bb = [...b.naturalSuits].sort();
    return aa.join("") === bb.join("") ? aa : null;
  }

  function nextActive(world, from) {
    for (let step = 1; step <= world.active.length; step += 1) {
      const player = (from + step) % world.active.length;
      if (world.active[player]) return player;
    }
    return 0;
  }

  function clearField(world, starter) {
    world.field = null;
    world.lock = null;
    world.leader = null;
    world.passed = world.active.map(() => false);
    world.turn = world.active[starter] ? starter : nextActive(world, starter);
  }

  function isFoulFinish(action, revolutionAfter) {
    if (action.containsJoker) return true;
    if (action.type !== "straight" && action.rank === RANKS.indexOf("8")) return true;
    if (action.isSpade3 && action.count === 1) return true;
    const forbidden = revolutionAfter ? RANKS.indexOf("3") : RANKS.indexOf("2");
    if (action.type === "straight") return action.sequence.includes(forbidden);
    return action.rank === forbidden;
  }

  function applyAction(source, player, action) {
    const world = clone(source);
    if (action.kind === "pass") {
      if (!world.field) return { status: "invalid", world };
      world.passed[player] = true;
      const othersDone = world.active.every((active, index) => !active || index === world.leader || world.passed[index]);
      if (othersDone) clearField(world, world.leader);
      else world.turn = nextActive(world, player);
      return { status: null, world };
    }

    const previous = world.field;
    world.hands[player] = world.hands[player].filter((id) => !action.cards.includes(id));
    if (!world.lock && previous) world.lock = identicalNaturalSuits(previous, action);
    world.field = clone(action);
    world.leader = player;
    world.passed[player] = false;

    if (action.type === "group" && action.count >= 4) world.revolution = !world.revolution;
    const foul = world.hands[player].length === 0 && isFoulFinish(action, world.revolution);
    if (world.hands[player].length === 0) {
      if (player === 0) return { status: foul ? "lose" : "win", world, foul };
      if (!foul) return { status: "lose", world, foul: false };
      world.active[player] = false;
      world.passed[player] = true;
    }

    const spade3Clear = previous?.isJokerSingle && action.isSpade3;
    const jokerPairClear = action.count === 2 && action.cards.every((id) => parseCard(id).joker);
    const effectClear = action.contains8 || spade3Clear || jokerPairClear;
    if (effectClear) clearField(world, player);
    else world.turn = nextActive(world, player);
    return { status: null, world, foul };
  }

  function generateDeals(candidates, counts) {
    const worlds = [];
    let truncated = false;
    const allocate = (remaining, index, hands) => {
      if (worlds.length >= MAX_DEALS) { truncated = true; return; }
      if (index === counts.length) {
        worlds.push(hands.map((hand) => [...hand].sort(cardSort)));
        return;
      }
      for (const choice of combinations(remaining, counts[index])) {
        const chosen = new Set(choice);
        allocate(remaining.filter((id) => !chosen.has(id)), index + 1, [...hands, choice]);
        if (truncated) return;
      }
    };
    allocate([...candidates], 0, []);
    return { deals: worlds, truncated };
  }

  function makeWorld(opponentHands) {
    const hands = [[...puzzle.mine].sort(cardSort), ...opponentHands.map((h) => [...h].sort(cardSort))];
    const initial = puzzle.initial || {};
    const initialActions = initial.fieldCards ? analyzeSubset(initial.fieldCards) : [];
    const field = initialActions.find((action) => !initial.fieldType || action.type === initial.fieldType) || null;
    return {
      hands,
      turn: initial.turn ?? 0,
      field: field ? clone(field) : null,
      revolution: Boolean(initial.revolution),
      lock: initial.lock ? [...initial.lock] : null,
      leader: field ? (initial.leader ?? 1) : null,
      passed: hands.map(() => false),
      active: hands.map(() => true),
    };
  }

  function worldKey(world) {
    return [
      world.hands.map((hand) => [...hand].sort(cardSort).join(",")).join("/"),
      world.turn,
      world.field?.key || "EMPTY",
      world.revolution ? 1 : 0,
      (world.lock || []).join(""),
      world.passed.map(Number).join(""),
      world.active.map(Number).join(""),
    ].join(";");
  }

  function uniqueWorlds(worlds) {
    return [...new Map(worlds.map((world) => [worldKey(world), world])).values()];
  }

  function makeSolver() {
    const memo = new Map();
    const metrics = { nodes: 0, cacheHits: 0, limited: false };

    const keyFor = (worlds) => uniqueWorlds(worlds).map(worldKey).sort().join("||");

    function solve(inputWorlds) {
      const worlds = uniqueWorlds(inputWorlds);
      metrics.nodes += 1;
      if (metrics.nodes > MAX_NODES) {
        metrics.limited = true;
        return { win: false, limited: true, depth: 0 };
      }
      const memoKey = keyFor(worlds);
      if (memo.has(memoKey)) { metrics.cacheHits += 1; return memo.get(memoKey); }
      const turn = worlds[0].turn;

      if (turn === 0) {
        const actions = legalActions(worlds[0], 0);
        for (const action of actions) {
          const successors = [];
          let terminal = null;
          for (const world of worlds) {
            const matching = legalActions(world, 0).find((candidate) => candidate.key === action.key);
            if (!matching) { terminal = "lose"; break; }
            const next = applyAction(world, 0, matching);
            if (next.status) terminal = next.status;
            else successors.push(next.world);
          }
          if (terminal === "win") {
            const result = { win: true, depth: 1, choice: action.key };
            memo.set(memoKey, result);
            return result;
          }
          if (terminal || !successors.length) continue;
          const child = solve(successors);
          if (child.win) {
            const result = { win: true, depth: child.depth + 1, choice: action.key };
            memo.set(memoKey, result);
            return result;
          }
          if (child.limited) break;
        }
        const result = { win: false, limited: metrics.limited, depth: 0 };
        memo.set(memoKey, result);
        return result;
      }

      const branches = buildOpponentBranches(worlds, turn);
      let worstDepth = -1;
      let worstKey = null;
      for (const [actionKey, branch] of branches) {
        if (branch.terminalLose) {
          const result = { win: false, depth: 1, worst: actionKey };
          memo.set(memoKey, result);
          return result;
        }
        const child = solve(branch.worlds);
        if (!child.win) {
          const result = { win: false, limited: child.limited, depth: child.depth + 1, worst: actionKey };
          memo.set(memoKey, result);
          return result;
        }
        if (child.depth > worstDepth) { worstDepth = child.depth; worstKey = actionKey; }
      }
      const result = { win: true, depth: worstDepth + 1, worst: worstKey };
      memo.set(memoKey, result);
      return result;
    }

    function testFirstAction(worlds, action) {
      const successors = [];
      for (const world of worlds) {
        const matching = legalActions(world, 0).find((candidate) => candidate.key === action.key);
        if (!matching) return { win: false, depth: 0 };
        const next = applyAction(world, 0, matching);
        if (next.status === "win") continue;
        if (next.status === "lose") return { win: false, depth: 0 };
        successors.push(next.world);
      }
      if (!successors.length) return { win: true, depth: 1 };
      const child = solve(successors);
      return { ...child, depth: child.depth + 1 };
    }

    return { solve, testFirstAction, metrics, memo };
  }

  function buildOpponentBranches(worlds, turn) {
    const branches = new Map();
    for (const world of worlds) {
      for (const action of legalActions(world, turn)) {
        if (!branches.has(action.key)) branches.set(action.key, { worlds: [], actions: [], terminalLose: false, terminalWorld: null });
        const branch = branches.get(action.key);
        const next = applyAction(world, turn, action);
        branch.actions.push(action);
        if (next.status === "lose") {
          branch.terminalLose = true;
          branch.terminalWorld = branch.terminalWorld || next.world;
        }
        else if (!next.status) branch.worlds.push(next.world);
      }
    }
    for (const branch of branches.values()) branch.worlds = uniqueWorlds(branch.worlds);
    return branches;
  }

  function analyzeCurrentPuzzle({ quiet = false, conceal = false } = {}) {
    const validation = validateDraft(puzzle);
    if (!validation.valid) { toast(validation.message); return false; }
    if (!quiet) setAnalysisLoading();

    const generated = generateDeals(puzzle.candidates, puzzle.counts);
    dealInfo = { count: generated.deals.length, truncated: generated.truncated };
    initialBelief = generated.deals.map(makeWorld);
    belief = clone(initialBelief);
    solver = makeSolver();
    safeActions = [];
    const firstActions = legalActions(initialBelief[0], 0).filter((action) => action.kind === "play");
    for (const action of firstActions) {
      const result = solver.testFirstAction(initialBelief, action);
      if (result.win) safeActions.push({ action, depth: result.depth });
      if (solver.metrics.limited) break;
    }
    finished = false;
    history = [];
    selected.clear();
    if (challengeMode && conceal) updateChallengePanel();
    else updateAnalysis();
    renderGame();
    return !solver.metrics.limited;
  }

  function evaluatePuzzle(problem) {
    const previousPuzzle = puzzle;
    puzzle = clone(problem);
    try {
      const validation = validateDraft(puzzle);
      if (!validation.valid) return { exact: false, forcedWin: false, error: validation.message };
      const generated = generateDeals(puzzle.candidates, puzzle.counts);
      const worlds = generated.deals.map(makeWorld);
      const localSolver = makeSolver();
      const safe = [];
      const firstActions = legalActions(worlds[0], 0).filter((action) => action.kind === "play");
      for (const action of firstActions) {
        const outcome = localSolver.testFirstAction(worlds, action);
        if (outcome.win) safe.push({ action, depth: outcome.depth });
        if (localSolver.metrics.limited) break;
      }
      return {
        exact: !generated.truncated && !localSolver.metrics.limited,
        forcedWin: safe.length > 0,
        safeFirstMoves: safe.map(({ action }) => formatAction(action)),
        shortestDepth: safe.length ? Math.min(...safe.map((entry) => entry.depth)) : null,
        deals: generated.deals.length,
        nodes: localSolver.metrics.nodes,
      };
    } catch (error) {
      return { exact: false, forcedWin: false, error: error instanceof Error ? error.message : String(error) };
    } finally {
      puzzle = previousPuzzle;
    }
  }

  function setAnalysisLoading() {
    el("verdict").className = "verdict idle";
    el("verdict").textContent = "探索中";
    el("analysisMessage").innerHTML = `<span class="analysis-icon">…</span><div><strong>全配札を展開しています</strong><p>相手の出し札とパスを、観測履歴ごとに分岐しています。</p></div>`;
  }

  function updateAnalysis() {
    el("challengeTools").hidden = true;
    el("challengeNav").hidden = true;
    el("analyzeBtn").disabled = false;
    el("analyzeBtn").textContent = "最悪手を読む";
    el("restartBtn").textContent = "この問題を最初から";
    el("dealCount").textContent = dealInfo.truncated ? `${dealInfo.count.toLocaleString()}+` : dealInfo.count.toLocaleString();
    el("nodeCount").textContent = solver ? solver.metrics.nodes.toLocaleString() : "—";
    el("safeCount").textContent = solver?.metrics.limited ? "未確定" : `${safeActions.length}手`;
    const verdict = el("verdict");

    if (solver?.metrics.limited || dealInfo.truncated) {
      verdict.className = "verdict limit";
      verdict.textContent = "探索上限";
      el("analysisMessage").innerHTML = `<span class="analysis-icon">!</span><div><strong>この局面はまだ判定できません</strong><p>候補か手札を減らすと、厳密探索できます。途中結果は勝利保証には使いません。</p></div>`;
    } else if (safeActions.length) {
      verdict.className = "verdict win";
      verdict.textContent = "詰みあり";
      const labels = safeActions.map(({ action }) => formatAction(action)).join("／");
      el("analysisMessage").innerHTML = `<span class="analysis-icon">✓</span><div><strong>最悪でも先に上がれます</strong><p>安全な初手は <b>${escapeHtml(labels)}</b>。相手は常に最も嫌な応手を選びます。</p></div>`;
    } else {
      verdict.className = "verdict lose";
      verdict.textContent = "詰みなし";
      el("analysisMessage").innerHTML = `<span class="analysis-icon">×</span><div><strong>保証できる上がり筋がありません</strong><p>どの初手にも、阻止できる配札または応手が少なくとも1つあります。</p></div>`;
    }
    renderLog();
  }

  function currentProblem() {
    return PROBLEMS.find((problem) => problem.id === activeProblemId) || null;
  }

  function currentPattern() {
    const problem = currentProblem();
    return PATTERNS.find((pattern) => pattern.id === problem?.pattern) || null;
  }

  function updateChallengePanel() {
    const problem = currentProblem();
    const pattern = currentPattern();
    if (!problem) return;
    const attempt = challengeAttempts.get(problem.id) || 1;
    el("challengeTools").hidden = false;
    el("challengeNav").hidden = false;
    el("challengeProblem").textContent = `${problem.id} · ${problem.difficulty}`;
    el("challengeAttempt").textContent = `挑戦 ${attempt}回目`;
    el("dealCount").textContent = dealInfo.truncated ? `${dealInfo.count.toLocaleString()}+` : dealInfo.count.toLocaleString();
    el("nodeCount").textContent = solver ? solver.metrics.nodes.toLocaleString() : "—";
    el("safeCount").textContent = challengeHintLevel >= 2 || challengeRevealed ? `${safeActions.length}手` : "？";
    el("analyzeBtn").disabled = true;
    el("analyzeBtn").textContent = "解析済み・解答は非表示";
    el("restartBtn").textContent = finished ? "もう一度挑戦" : "最初からやり直す";
    el("hintBtn").disabled = challengeHintLevel >= 3 || finished;
    el("revealBtn").disabled = challengeRevealed || finished;

    const verdict = el("verdict");
    verdict.className = "verdict challenge";
    verdict.textContent = "挑戦中";
    el("analysisMessage").innerHTML = `<span class="analysis-icon">?</span><div><strong>${escapeHtml(problem.title)}</strong><p>安全な初手は伏せています。カードを選び、最悪応手を越えて先に上がってください。</p></div>`;

    let hintTitle = "ヒントは3段階";
    let hintText = "型 → 安全手の数 → 初手1つ、の順に開きます。";
    if (challengeHintLevel === 1) {
      hintTitle = `型：${pattern?.title || "詰み筋"}`;
      hintText = pattern?.short || "残り札の順番を考えてください。";
    } else if (challengeHintLevel === 2) {
      hintTitle = `安全な初手は ${safeActions.length}手`;
      hintText = pattern?.principle || "相手の最悪応手から逆算してください。";
    } else if (challengeHintLevel >= 3) {
      hintTitle = "初手ヒント";
      hintText = safeActions.length ? `${formatAction(safeActions[0].action)} から読みます。` : "安全な初手は見つかりませんでした。";
    }
    el("hintPanel").innerHTML = `<b>${escapeHtml(hintTitle)}</b><p>${escapeHtml(hintText)}</p>`;
    el("hintBtn").textContent = challengeHintLevel >= 3 ? "ヒントを全て表示" : `ヒント ${challengeHintLevel + 1}/3`;
    renderLog();
  }

  function advanceHint() {
    if (!challengeMode || finished || challengeHintLevel >= 3) return;
    challengeHintLevel += 1;
    updateChallengePanel();
  }

  function revealChallengeAnswer() {
    if (!challengeMode || finished || challengeRevealed) return;
    challengeRevealed = true;
    challengeHintLevel = 3;
    el("safeCount").textContent = `${safeActions.length}手`;
    el("verdict").className = "verdict limit";
    el("verdict").textContent = "練習モード";
    const labels = safeActions.map(({ action }) => formatAction(action)).join("／") || "なし";
    el("analysisMessage").innerHTML = `<span class="analysis-icon">!</span><div><strong>解答を表示しました</strong><p>安全な初手は <b>${escapeHtml(labels)}</b>。この挑戦はクリア記録に含めません。</p></div>`;
    el("hintPanel").innerHTML = `<b>読み筋の核</b><p>${escapeHtml(currentPattern()?.principle || "最悪応手から逆算します。")}</p>`;
    el("hintBtn").disabled = true;
    el("revealBtn").disabled = true;
    renderLog();
  }

  function escapeHtml(text) {
    return String(text).replace(/[&<>'"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", "'": "&#39;", '"': "&quot;" }[c]));
  }

  function renderGame() {
    const world = belief[0] || {
      hands: [[...puzzle.mine], ...puzzle.counts.map((count) => Array.from({ length: count }, () => "BACK"))],
      turn: 0,
      field: null,
      revolution: false,
      lock: null,
      passed: puzzle.counts.map(() => false),
      active: [true, ...puzzle.counts.map(() => true)],
    };
    const turn = world.turn;
    const opponents = el("opponents");
    opponents.innerHTML = puzzle.counts.map((_, index) => {
      const player = index + 1;
      const count = world.hands[player]?.length ?? puzzle.counts[index];
      const backs = Array.from({ length: Math.min(count, 7) }, () => `<span class="back-card"></span>`).join("");
      return `<div class="opponent ${turn === player ? "active" : ""}"><div class="name">相手 ${String.fromCharCode(65 + index)}</div><div class="back-cards">${backs}</div><span class="count-badge">残り ${count}枚</span></div>`;
    }).join("");

    const hand = world.hands[0] || puzzle.mine;
    el("myHand").innerHTML = hand.map((id, index) => cardHtml(id, index, hand.length, true)).join("");
    els(".playing-card[data-card]").forEach((button) => {
      button.addEventListener("click", () => toggleCard(button.dataset.card));
    });

    if (world.field) {
      el("fieldCards").innerHTML = world.field.cards.map((id, index) => cardHtml(id, index, world.field.cards.length, false)).join("");
      const state = [world.revolution ? "革命中" : "通常", world.lock ? `縛り ${world.lock.map(suitSymbol).join("")}` : null].filter(Boolean).join(" · ");
      el("fieldState").textContent = state;
      el("lastMove").textContent = `場：${formatAction(world.field)}`;
    } else {
      el("fieldCards").innerHTML = `<span class="empty-field">LEAD</span>`;
      el("fieldState").textContent = world.revolution ? "場は空です · 革命中" : "場は空です";
      el("lastMove").textContent = "好きな組み合わせから開始";
    }
    el("turnBadge").textContent = turn === 0 ? "あなたの番" : `相手 ${String.fromCharCode(64 + turn)} の番`;
    el("turnBadge").className = `turn-badge ${turn === 0 ? "" : "wait"}`;
    el("passBtn").disabled = finished || turn !== 0 || !world.field;
    updateSelectionState();
    renderCandidates();
  }

  function cardHtml(id, index, total, interactive) {
    const c = parseCard(id);
    const classes = ["playing-card", c.red ? "red" : "", c.joker ? "joker" : "", selected.has(id) ? "selected" : ""].filter(Boolean).join(" ");
    const attrs = interactive ? `type="button" data-card="${id}" aria-pressed="${selected.has(id)}" aria-label="${cardLabel(id)}"` : "aria-hidden=\"true\"";
    return `<button class="${classes}" ${attrs} style="--i:${index};--mid:${(total - 1) / 2}"><span class="corner"><span>${c.joker ? "J" : c.rankLabel}</span><span>${c.joker ? "★" : c.symbol}</span></span><span class="suit-big">${c.joker ? "JOKER" : c.symbol}</span></button>`;
  }

  function suitSymbol(key) { return SUITS.find((s) => s.key === key)?.symbol || "★"; }

  function toggleCard(id) {
    if (finished || belief[0]?.turn !== 0) return;
    if (selected.has(id)) selected.delete(id); else selected.add(id);
    renderGame();
  }

  function selectedAction() {
    if (!belief.length || !selected.size) return null;
    const candidates = legalActions(belief[0], 0).filter((action) => action.kind === "play" && sameCards(action.cards, [...selected]));
    return candidates.sort((a, b) => actionPower(b, belief[0].revolution) - actionPower(a, belief[0].revolution))[0] || null;
  }

  function updateSelectionState() {
    const action = selectedAction();
    el("playBtn").disabled = finished || belief[0]?.turn !== 0 || !action;
    if (!selected.size) el("selectionHint").textContent = "カードを選択";
    else if (action) el("selectionHint").textContent = formatAction(action);
    else el("selectionHint").textContent = "この組み合わせは出せません";
  }

  function commitPlayerAction(action) {
    if (!belief.length || finished) return;
    const successors = [];
    let terminal = null;
    let terminalWorld = null;
    for (const world of belief) {
      const matching = legalActions(world, 0).find((candidate) => candidate.key === action.key);
      if (!matching) { toast("この手はすべての局面で合法ではありません"); return; }
      const next = applyAction(world, 0, matching);
      terminal = terminal || next.status;
      if (next.status && !terminalWorld) terminalWorld = next.world;
      if (!next.status) successors.push(next.world);
    }
    history.push({ player: "あなた", action: formatAction(action), safe: safeActions.some(({ action: safe }) => safe.key === action.key) });
    selected.clear();
    if (terminal === "win") {
      if (terminalWorld) belief = [terminalWorld];
      return finishGame(true, "読み切り成功。反則なしで最初に上がりました。");
    }
    if (terminal === "lose") {
      if (terminalWorld) belief = [terminalWorld];
      return finishGame(false, "その上がり方は反則です。");
    }
    belief = uniqueWorlds(successors);
    renderGame();
    renderLog();
    window.setTimeout(runWorstOpponents, 360);
  }

  function commitPass() {
    const action = { kind: "pass", key: "PASS" };
    if (!legalActions(belief[0], 0).some((candidate) => candidate.key === "PASS")) return;
    const successors = belief.map((world) => applyAction(world, 0, action).world);
    history.push({ player: "あなた", action: "パス", safe: false });
    belief = uniqueWorlds(successors);
    selected.clear();
    renderGame();
    renderLog();
    window.setTimeout(runWorstOpponents, 360);
  }

  function runWorstOpponents() {
    if (finished || !belief.length) return;
    const turn = belief[0].turn;
    if (turn === 0) { renderGame(); return; }
    const branches = buildOpponentBranches(belief, turn);
    let chosen = null;
    for (const [key, branch] of branches) {
      if (branch.terminalLose) { chosen = { key, branch, score: Infinity }; break; }
      const outcome = solver ? solver.solve(branch.worlds) : { win: false, depth: 0 };
      const score = outcome.win ? outcome.depth : 1_000_000 + outcome.depth;
      if (!chosen || score > chosen.score) chosen = { key, branch, score };
    }
    if (!chosen) return;
    const representative = chosen.branch.actions[0];
    history.push({ player: `相手 ${String.fromCharCode(64 + turn)}`, action: formatAction(representative), worst: true });
    if (chosen.branch.terminalLose) {
      if (chosen.branch.terminalWorld) belief = [chosen.branch.terminalWorld];
      return finishGame(false, `相手 ${String.fromCharCode(64 + turn)} が先に上がりました。`);
    }
    belief = chosen.branch.worlds;
    renderGame();
    renderLog();
    window.setTimeout(runWorstOpponents, 360);
  }

  function finishGame(win, message) {
    finished = true;
    const verdict = el("verdict");
    verdict.className = `verdict ${win ? "win" : "lose"}`;
    const countsAsClear = win && challengeMode && !challengeRevealed && activeProblemId;
    if (countsAsClear) {
      clearedProblems.add(activeProblemId);
      saveClearedProblems();
    }
    verdict.textContent = win ? challengeRevealed && challengeMode ? "練習完了" : "クリア" : "失敗";
    const title = win
      ? challengeRevealed && challengeMode ? "解答をなぞり切りました" : "読み切りました"
      : "最悪手に阻まれました";
    const suffix = countsAsClear ? ` ${currentProblem()?.id || "この問題"}をクリア記録に保存しました。` : "";
    el("analysisMessage").innerHTML = `<span class="analysis-icon">${win ? "✓" : "×"}</span><div><strong>${escapeHtml(title)}</strong><p>${escapeHtml(message + suffix)}</p></div>`;
    if (challengeMode) {
      el("safeCount").textContent = `${safeActions.length}手`;
      el("restartBtn").textContent = win ? "もう一度解く" : "もう一度挑戦";
      el("hintBtn").disabled = true;
      el("revealBtn").disabled = true;
      updateClearProgress();
    }
    renderGame();
    renderLog();
  }

  function renderLog() {
    const log = el("lineLog");
    if (!history.length) {
      if (challengeMode && !challengeRevealed) {
        log.innerHTML = `<li data-step="01"><span><b>あなたの番</b><br>初手を選んで「この手を出す」</span></li>`;
      } else {
        log.innerHTML = safeActions.length ? `<li data-step="01"><span><b>推奨</b><br>${escapeHtml(formatAction(safeActions[0].action))} から読む</span></li>` : "";
      }
      return;
    }
    log.innerHTML = history.map((item, index) => `<li data-step="${String(index + 1).padStart(2, "0")}"><span><b>${escapeHtml(item.player)}</b><br>${escapeHtml(item.action)}${item.worst ? " · 最悪応手" : item.safe && (!challengeMode || finished || challengeRevealed) ? " · 安全手" : ""}</span></li>`).join("");
    log.scrollTop = log.scrollHeight;
  }

  function renderCandidates() {
    el("candidateCards").innerHTML = puzzle.candidates.map(miniCardHtml).join("");
    el("candidateMeta").textContent = `${puzzle.candidates.length}候補 / ${puzzle.counts.reduce((a, b) => a + b, 0)}枚配布`;
  }

  function miniCardHtml(id) {
    const c = parseCard(id);
    return `<span class="mini-card ${c.red ? "red" : ""}" title="${c.joker ? "ジョーカー" : c.rankLabel + " " + SUITS.find((s) => s.key === c.suit).name}">${c.joker ? "JK" : `${c.symbol}${c.rankLabel}`}</span>`;
  }

  function restartPuzzle() {
    if (!initialBelief.length) return analyzeCurrentPuzzle({ conceal: challengeMode });
    if (challengeMode && activeProblemId) {
      challengeAttempts.set(activeProblemId, (challengeAttempts.get(activeProblemId) || 0) + 1);
      challengeHintLevel = 0;
      challengeRevealed = false;
    }
    belief = clone(initialBelief);
    selected.clear();
    history = [];
    finished = false;
    if (challengeMode) updateChallengePanel();
    else updateAnalysis();
    renderGame();
  }

  function validateDraft(value) {
    const total = value.counts.reduce((sum, count) => sum + Number(count), 0);
    if (!value.mine.length) return { valid: false, message: "自分の手札を1枚以上選んでください。" };
    if (value.mine.length > 9) return { valid: false, message: "デモでは自分の手札は9枚までです。" };
    if (value.counts.some((count) => count < 1)) return { valid: false, message: "相手の残り枚数は1枚以上にしてください。" };
    if (total > 8) return { valid: false, message: "デモでは相手の合計枚数は8枚までです。" };
    if (value.candidates.length < total) return { valid: false, message: `相手札候補が${total - value.candidates.length}枚足りません。` };
    if (value.candidates.length > 11) return { valid: false, message: "厳密探索のため、相手札候補は11枚までにしてください。" };
    const fieldCards = value.initial?.fieldCards || [];
    const allKnownCards = [...value.mine, ...value.candidates, ...fieldCards];
    if (new Set(allKnownCards).size !== allKnownCards.length) return { valid: false, message: "手札・候補・場に同じカードを重複して指定できません。" };
    return { valid: true, message: `相手${value.counts.length}人・合計${total}枚を、${value.candidates.length}候補から探索します。` };
  }

  function renderLibrary() {
    el("patternFilters").innerHTML = [
      `<button class="filter-chip ${libraryPattern === "all" ? "active" : ""}" data-pattern-filter="all">すべて</button>`,
      ...PATTERNS.map((pattern) => `<button class="filter-chip ${libraryPattern === pattern.id ? "active" : ""}" data-pattern-filter="${pattern.id}">${pattern.number} ${pattern.title}</button>`),
    ].join("");
    els("[data-pattern-filter]").forEach((button) => button.addEventListener("click", () => {
      libraryPattern = button.dataset.patternFilter;
      renderLibrary();
    }));
    el("difficultyFilter").value = libraryDifficulty;

    const shownPatterns = libraryPattern === "all" ? PATTERNS : PATTERNS.filter((pattern) => pattern.id === libraryPattern);
    el("patternStudy").innerHTML = shownPatterns.map((pattern) => {
      const count = PROBLEMS.filter((problem) => problem.pattern === pattern.id).length;
      return `<article class="pattern-card" style="--pattern-accent:${pattern.accent}">
        <div class="pattern-card-top"><span>${pattern.number}</span><small>${count} PROBLEMS</small></div>
        <h3>${escapeHtml(pattern.title)}</h3><p class="pattern-short">${escapeHtml(pattern.short)}</p>
        <dl><div><dt>成立する理由</dt><dd>${escapeHtml(pattern.principle)}</dd></div><div><dt>崩れる条件</dt><dd>${escapeHtml(pattern.breaks)}</dd></div></dl>
      </article>`;
    }).join("");
    renderPuzzleGrid();
    updateAuditUI();
    updateClearProgress();
  }

  function filteredProblems() {
    return PROBLEMS.filter((problem) => (libraryPattern === "all" || problem.pattern === libraryPattern)
      && (libraryDifficulty === "all" || problem.difficulty === libraryDifficulty));
  }

  function renderPuzzleGrid() {
    const visible = filteredProblems();
    el("libraryTitle").textContent = libraryPattern === "all" ? `全${PROBLEMS.length}問` : PATTERNS.find((pattern) => pattern.id === libraryPattern)?.title || "問題集";
    el("visibleProblemCount").textContent = `${visible.length}問を表示`;
    el("puzzleGrid").innerHTML = visible.map((problem) => {
      const pattern = PATTERNS.find((entry) => entry.id === problem.pattern);
      const result = libraryResults.get(problem.id);
      const cleared = clearedProblems.has(problem.id);
      const status = cleared ? "CLEAR" : !result ? "未検証" : result.exact && result.forcedWin ? "挑戦可能" : result.error ? "エラー" : "要修正";
      const statusClass = cleared ? "clear" : !result ? "idle" : result.exact && result.forcedWin ? "pass" : "fail";
      const initialText = problem.initial?.fieldCards?.length ? `場 ${problem.initial.fieldCards.map(cardLabel).join(" ")}` : problem.initial?.revolution ? "革命中・場は空" : "場は空";
      return `<article class="puzzle-card" style="--pattern-accent:${pattern?.accent || "#e8c86e"}">
        <div class="puzzle-card-head"><span>${problem.id}</span><span class="audit-badge ${statusClass}">${status}</span></div>
        <div class="puzzle-tags"><span>${escapeHtml(pattern?.title || "")}</span><span>${problem.difficulty}</span></div>
        <h4>${escapeHtml(problem.title)}</h4>
        <div class="puzzle-hand">${problem.mine.map(miniCardHtml).join("")}</div>
        <div class="puzzle-meta"><span>${escapeHtml(initialText)}</span><span>相手 ${problem.counts.map((count) => `${count}枚`).join("・")}</span><span>候補 ${problem.candidates.length}枚</span></div>
        ${result ? `<div class="puzzle-result"><b>${cleared ? "クリア済み" : "厳密検証済み"}</b><span>${result.deals?.toLocaleString() || 0}配札 / ${result.nodes?.toLocaleString() || 0}局面</span></div>` : `<div class="puzzle-result muted"><span>挑戦時に最悪応手を先読み</span></div>`}
        <button class="solve-puzzle-btn" data-load-problem="${problem.id}">${cleared ? "もう一度解く" : "挑戦する"}</button>
      </article>`;
    }).join("");
    els("[data-load-problem]").forEach((button) => button.addEventListener("click", () => loadLibraryProblem(button.dataset.loadProblem)));
  }

  function updateAuditUI() {
    const passed = [...libraryResults.values()].filter((result) => result.exact && result.forcedWin).length;
    const done = libraryResults.size;
    el("auditPassed").textContent = String(passed);
    el("auditMeter").style.width = `${PROBLEMS.length ? (done / PROBLEMS.length) * 100 : 0}%`;
    el("auditStatus").textContent = auditRunning ? `${done}/${PROBLEMS.length}問を探索中` : done === PROBLEMS.length ? `${passed}問で詰み筋を確認` : "未検証";
    el("auditBtn").disabled = auditRunning;
    el("auditBtn").textContent = auditRunning ? "探索中…" : done === PROBLEMS.length ? "もう一度検証" : `${PROBLEMS.length}問を一括検証`;
  }

  function updateClearProgress() {
    const count = [...clearedProblems].filter((id) => PROBLEMS.some((problem) => problem.id === id)).length;
    el("clearCount").textContent = `${count} / ${PROBLEMS.length}`;
    el("randomChallengeBtn").textContent = count === PROBLEMS.length ? "全問クリア・ランダム復習" : `未クリアから1問（残り${PROBLEMS.length - count}）`;
  }

  async function auditLibrary() {
    if (auditRunning) return;
    auditRunning = true;
    libraryResults = new Map();
    updateAuditUI();
    for (let index = 0; index < PROBLEMS.length; index += 1) {
      const problem = PROBLEMS[index];
      libraryResults.set(problem.id, evaluatePuzzle(problem));
      if (index % 2 === 1 || index === PROBLEMS.length - 1) {
        updateAuditUI();
        renderPuzzleGrid();
        await new Promise((resolve) => requestAnimationFrame(resolve));
      }
    }
    auditRunning = false;
    updateAuditUI();
    const passed = [...libraryResults.values()].filter((result) => result.exact && result.forcedWin).length;
    toast(`${passed}/${PROBLEMS.length}問の詰み筋を確認しました`);
  }

  function loadLibraryProblem(id) {
    const problem = PROBLEMS.find((entry) => entry.id === id);
    if (!problem) return;
    challengeMode = true;
    activeProblemId = problem.id;
    challengeHintLevel = 0;
    challengeRevealed = false;
    challengeAttempts.set(problem.id, (challengeAttempts.get(problem.id) || 0) + 1);
    puzzle = clone(problem);
    draft = clone(problem);
    el("puzzleEyebrow").textContent = `${problem.id} · ${PATTERNS.find((pattern) => pattern.id === problem.pattern)?.title || "問題集"}`;
    switchView("play");
    window.setTimeout(() => analyzeCurrentPuzzle({ quiet: true, conceal: true }), 40);
  }

  function loadAdjacentProblem(direction) {
    const currentIndex = Math.max(0, PROBLEMS.findIndex((problem) => problem.id === activeProblemId));
    const nextIndex = (currentIndex + direction + PROBLEMS.length) % PROBLEMS.length;
    loadLibraryProblem(PROBLEMS[nextIndex].id);
  }

  function loadRandomChallenge() {
    const uncleared = PROBLEMS.filter((problem) => !clearedProblems.has(problem.id));
    const pool = uncleared.length ? uncleared : PROBLEMS;
    const problem = pool[Math.floor(Math.random() * pool.length)];
    if (problem) loadLibraryProblem(problem.id);
  }

  function leaveChallengeMode() {
    challengeMode = false;
    activeProblemId = null;
    challengeHintLevel = 0;
    challengeRevealed = false;
    el("challengeTools").hidden = true;
    el("challengeNav").hidden = true;
  }

  function renderEditor() {
    el("opponentCount").value = String(draft.counts.length);
    el("opponentInputs").innerHTML = draft.counts.map((count, index) => `<div class="count-row"><label for="opp${index}">相手 ${String.fromCharCode(65 + index)}</label><input id="opp${index}" data-count-index="${index}" type="number" min="1" max="8" value="${count}"></div>`).join("");
    els("[data-count-index]").forEach((input) => input.addEventListener("input", () => {
      draft.counts[Number(input.dataset.countIndex)] = Math.max(1, Number(input.value) || 1);
      renderEditorSummary();
    }));
    el("deckPicker").innerHTML = DECK.map((id) => {
      const c = parseCard(id);
      const owner = draft.mine.includes(id) ? "mine" : draft.candidates.includes(id) ? "candidates" : null;
      return `<button class="deck-pick ${c.red ? "red" : ""} ${owner ? "taken" : ""} ${owner === pickerTarget ? "in-target" : ""}" data-pick="${id}" title="${owner === "mine" ? "自分の手札" : owner === "candidates" ? "相手札候補" : "追加"}"><span>${c.joker ? "JK" : c.rankLabel}</span><span>${c.joker ? "★" : c.symbol}</span></button>`;
    }).join("");
    els("[data-pick]").forEach((button) => button.addEventListener("click", () => pickCard(button.dataset.pick)));
    renderEditorSummary();
  }

  function renderEditorSummary() {
    el("editMine").innerHTML = [...draft.mine].sort(cardSort).map(miniCardHtml).join("");
    el("editCandidates").innerHTML = [...draft.candidates].sort(cardSort).map(miniCardHtml).join("");
    const validation = validateDraft(draft);
    el("validationMessage").className = `validation-message ${validation.valid ? "" : "error"}`;
    el("validationMessage").textContent = validation.message;
    el("applyPuzzleBtn").disabled = !validation.valid;
  }

  function pickCard(id) {
    const mineIndex = draft.mine.indexOf(id);
    const candidateIndex = draft.candidates.indexOf(id);
    if (pickerTarget === "mine") {
      if (mineIndex >= 0) draft.mine.splice(mineIndex, 1);
      else {
        if (candidateIndex >= 0) draft.candidates.splice(candidateIndex, 1);
        draft.mine.push(id);
      }
    } else {
      if (candidateIndex >= 0) draft.candidates.splice(candidateIndex, 1);
      else {
        if (mineIndex >= 0) draft.mine.splice(mineIndex, 1);
        draft.candidates.push(id);
      }
    }
    draft.mine.sort(cardSort);
    draft.candidates.sort(cardSort);
    renderEditor();
  }

  function switchView(name) {
    els(".view").forEach((view) => view.classList.toggle("active", view.id === `${name}View`));
    els(".nav-btn").forEach((button) => button.classList.toggle("active", button.dataset.view === name));
    if (name === "edit") renderEditor();
    if (name === "library") {
      renderLibrary();
      if (!libraryResults.size && !auditRunning) window.setTimeout(auditLibrary, 60);
    }
  }

  function applyDraft() {
    const validation = validateDraft(draft);
    if (!validation.valid) return toast(validation.message);
    leaveChallengeMode();
    puzzle = clone(draft);
    el("puzzleEyebrow").textContent = "CUSTOM · 終盤";
    switchView("play");
    window.setTimeout(() => analyzeCurrentPuzzle(), 40);
  }

  function shuffled(items) {
    const copy = [...items];
    for (let i = copy.length - 1; i > 0; i -= 1) {
      const j = Math.floor(Math.random() * (i + 1));
      [copy[i], copy[j]] = [copy[j], copy[i]];
    }
    return copy;
  }

  function generatePuzzle() {
    const pool = DECK.filter((id) => !parseCard(id).joker && parseCard(id).rank <= RANKS.indexOf("10"));
    const eightCards = pool.filter((id) => parseCard(id).rankLabel === "8");
    const eightPair = shuffled(eightCards).slice(0, 2);
    const finishRank = shuffled(["3", "4", "5", "6", "7"])[0];
    const finishPair = shuffled(pool.filter((id) => parseCard(id).rankLabel === finishRank && !eightPair.includes(id))).slice(0, 2);
    const mine = [...finishPair, ...eightPair].sort(cardSort);
    const candidates = shuffled(pool.filter((id) => !mine.includes(id))).slice(0, 6).sort(cardSort);
    leaveChallengeMode();
    draft = { mine, candidates, counts: [2, 2] };
    puzzle = clone(draft);
    el("puzzleEyebrow").textContent = "GENERATED · 8切り";
    switchView("play");
    toast("8切りを核にした新しい終盤を生成しました");
    window.setTimeout(() => analyzeCurrentPuzzle(), 40);
  }

  function toast(message) {
    clearTimeout(toastTimer);
    el("toast").textContent = message;
    el("toast").classList.add("show");
    toastTimer = window.setTimeout(() => el("toast").classList.remove("show"), 2500);
  }

  function registerWebMCP() {
    const context = document.modelContext;
    if (!context?.registerTool) return;
    const tools = [
      {
        name: "configure_puzzle",
        title: "詰み大富豪の問題を設定",
        description: "自分の手札、相手ごとの残り枚数、相手札候補を設定して画面を更新します。",
        inputSchema: {
          type: "object",
          properties: {
            mine: { type: "array", items: { type: "string", enum: DECK }, minItems: 1, maxItems: 9 },
            opponentCounts: { type: "array", items: { type: "integer", minimum: 1, maximum: 8 }, minItems: 1, maxItems: 3 },
            candidates: { type: "array", items: { type: "string", enum: DECK }, minItems: 1, maxItems: 11 },
          },
          required: ["mine", "opponentCounts", "candidates"],
          additionalProperties: false,
        },
        annotations: { readOnlyHint: false, untrustedContentHint: false },
        execute(input) {
          const next = { mine: input.mine, counts: input.opponentCounts, candidates: input.candidates };
          const validation = validateDraft(next);
          if (!validation.valid) throw new Error(validation.message);
          leaveChallengeMode();
          draft = clone(next); puzzle = clone(next); switchView("play"); analyzeCurrentPuzzle({ quiet: true });
          return { configured: true, deals: dealInfo.count, verdict: safeActions.length ? "forced_win" : "no_forced_win" };
        },
      },
      {
        name: "analyze_puzzle",
        title: "詰み筋を解析",
        description: "現在の問題を最悪配札・最悪応手で解析し、安全な初手を返します。",
        inputSchema: { type: "object", properties: {}, additionalProperties: false },
        annotations: { readOnlyHint: true, untrustedContentHint: false },
        execute() {
          analyzeCurrentPuzzle({ quiet: true });
          return {
            exact: !solver.metrics.limited && !dealInfo.truncated,
            deals: dealInfo.count,
            states: solver.metrics.nodes,
            forcedWin: safeActions.length > 0,
            safeFirstMoves: safeActions.map(({ action }) => formatAction(action)),
          };
        },
      },
      {
        name: "start_puzzle_challenge",
        title: "問題集の1問に挑戦",
        description: "問題IDを指定し、安全な初手を伏せた挑戦モードを画面で開始します。",
        inputSchema: {
          type: "object",
          properties: { problemId: { type: "string", enum: PROBLEMS.map((problem) => problem.id) } },
          required: ["problemId"],
          additionalProperties: false,
        },
        annotations: { readOnlyHint: false, untrustedContentHint: false },
        execute(input) {
          loadLibraryProblem(input.problemId);
          return { started: true, problemId: input.problemId, answerConcealed: true };
        },
      },
      {
        name: "list_puzzle_patterns",
        title: "詰み筋パターンを一覧",
        description: "問題集に収録した詰み筋の型と、それぞれの成立条件・崩れる条件を返します。",
        inputSchema: { type: "object", properties: {}, additionalProperties: false },
        annotations: { readOnlyHint: true, untrustedContentHint: false },
        execute() {
          return {
            totalProblems: PROBLEMS.length,
            patterns: PATTERNS.map((pattern) => ({
              id: pattern.id,
              title: pattern.title,
              principle: pattern.principle,
              breaks: pattern.breaks,
              problemCount: PROBLEMS.filter((problem) => problem.pattern === pattern.id).length,
            })),
          };
        },
      },
    ];
    for (const tool of tools) {
      try { Promise.resolve(context.registerTool(tool)).catch(() => {}); } catch (_) { /* unsupported preview */ }
    }
  }

  function bindEvents() {
    els(".nav-btn").forEach((button) => button.addEventListener("click", () => switchView(button.dataset.view)));
    els(".target-btn").forEach((button) => button.addEventListener("click", () => {
      pickerTarget = button.dataset.target;
      els(".target-btn").forEach((target) => target.classList.toggle("active", target === button));
      renderEditor();
    }));
    el("opponentCount").addEventListener("change", (event) => {
      const count = Number(event.target.value);
      draft.counts = Array.from({ length: count }, (_, index) => draft.counts[index] || 2);
      renderEditor();
    });
    el("applyPuzzleBtn").addEventListener("click", applyDraft);
    el("analyzeBtn").addEventListener("click", () => analyzeCurrentPuzzle());
    el("playBtn").addEventListener("click", () => {
      const action = selectedAction();
      if (action) commitPlayerAction(action);
    });
    el("passBtn").addEventListener("click", commitPass);
    el("resetSelectBtn").addEventListener("click", () => { selected.clear(); renderGame(); });
    el("restartBtn").addEventListener("click", restartPuzzle);
    el("hintBtn").addEventListener("click", advanceHint);
    el("revealBtn").addEventListener("click", revealChallengeAnswer);
    el("backLibraryBtn").addEventListener("click", () => switchView("library"));
    el("prevProblemBtn").addEventListener("click", () => loadAdjacentProblem(-1));
    el("nextProblemBtn").addEventListener("click", () => loadAdjacentProblem(1));
    el("newPuzzleBtn").addEventListener("click", generatePuzzle);
    el("auditBtn").addEventListener("click", auditLibrary);
    el("randomChallengeBtn").addEventListener("click", loadRandomChallenge);
    el("difficultyFilter").addEventListener("change", (event) => {
      libraryDifficulty = event.target.value;
      renderLibrary();
    });
  }

  bindEvents();
  renderEditor();
  renderCandidates();
  renderGame();
  renderLibrary();
  registerWebMCP();
})();

