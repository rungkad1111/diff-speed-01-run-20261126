// Fast drop-in for makefun-diff 1.0.0.
//
// Same answers as makefun-diff 1.0.0 on every input, faster:
//  - lines are interned to integer ids once (Map<string, int>), so the search
//    compares ints instead of strings;
//  - Myers's greedy search runs on Int32Array frontiers, one allocation per
//    depth, with a per-depth snapshot kept for backtracking (no per-step
//    objects, no linked component lists);
//  - the patch is formatted exactly like the reference (same header, hunks,
//    context, deletion-before-insertion runs, '%' lines).
//
// The search reproduces the reference's rule exactly: common prefix, then
// common suffix, then greedy forward Myers over the middle, furthest-reaching
// path per diagonal, deletion preferred when a deletion and an insertion reach
// the same point, never past either text's end, no edge pruning, snakes follow
// every run of equal lines. The first path to reach both ends is the script.

const FORMAT = 'makefun-diff/1';
const CONTEXT = 3;
const KEEP = 0;
const DELETE = 1;
const INSERT = 2;

/** A text's lines, each with its "\n" (the last one without, when the text does not end in one). */
function tokenize(text) {
  const parts = text.split('\n');
  const lines = new Array(parts.length);
  const last = parts.length - 1;
  for (let i = 0; i < last; i++) lines[i] = `${parts[i]}\n`;
  if (parts[last] !== '') lines[last] = parts[last];
  else lines.length = last;
  return lines;
}

/**
 * The edit script of id arrays a[0..n), b[0..m) as runs [{kind, count}], by
 * the reference's rule. Returns the runs of the middle section only (the
 * caller adds the stripped prefix/suffix keeps).
 *
 * The frontier is one Int32Array per depth ("trace"): trace[d] holds the V
 * frontier after depth d, diagonal k at index k+d, values X+1 (0 = dead
 * diagonal, X the old lines consumed after the depth's snake). A fresh
 * Int32Array is zero-filled, so no row ever needs filling; the X+1 encoding
 * is what makes that sound.
 */
function editRuns(a, b, n, m) {
  // d = 0: snake from (0, 0).
  if (n === 0 && m === 0) return [];
  let x = 0;
  let y = 0;
  while (x < n && y < m && a[x] === b[y]) { x++; y++; }
  if (x >= n && y >= m) return [{ kind: KEEP, count: x }];
  const trace = [];
  const v0 = new Int32Array(1);
  v0[0] = x + 1;
  trace.push(v0);
  let vPrev = v0;
  let dFound = -1;
  let kFound = 0;
  for (let d = 1; d <= n + m; d++) {
    const vCur = new Int32Array(2 * d + 1);
    let done = false;
    // Edge diagonal k = -d: only the insertion predecessor can exist.
    {
      const k = -d;
      const iUp = k + 1 + (d - 1);
      const xUpPlus = iUp >= 0 && iUp < vPrev.length ? vPrev[iUp] : 0;
      const xUp = xUpPlus - 1;
      const xIns = xUpPlus !== 0 && xUp - (k + 1) < m ? xUp : -1;
      if (xIns >= 0) {
        let xx = xIns;
        let yy = xx - k;
        while (xx < n && yy < m && a[xx] === b[yy]) { xx++; yy++; }
        vCur[k + d] = xx + 1;
        if (xx >= n && yy >= m) { dFound = d; kFound = k; done = true; }
      }
    }
    if (!done) {
      // Interior diagonals: both predecessor indices are in range, so no
      // bounds checks in the hot loop. Deletion wins ties, exactly the
      // reference's rule.
      for (let k = -d + 2; k <= d - 2; k += 2) {
        const xDownPlus = vPrev[k + d - 2];
        const xUpPlus = vPrev[k + d];
        const xDown = xDownPlus - 1;
        const xUp = xUpPlus - 1;
        const xDel = xDownPlus !== 0 && xDown < n ? xDown + 1 : -1;
        const xIns = xUpPlus !== 0 && xUp - (k + 1) < m ? xUp : -1;
        if (xDel < 0 && xIns < 0) continue;
        let xx = xDel >= 0 && (xIns < 0 || xDel >= xIns) ? xDel : xIns;
        let yy = xx - k;
        while (xx < n && yy < m && a[xx] === b[yy]) { xx++; yy++; }
        vCur[k + d] = xx + 1;
        if (xx >= n && yy >= m) { dFound = d; kFound = k; done = true; break; }
      }
    }
    if (!done) {
      // Edge diagonal k = d: only the deletion predecessor can exist.
      const k = d;
      const iDown = k - 1 + (d - 1);
      const xDownPlus = iDown >= 0 && iDown < vPrev.length ? vPrev[iDown] : 0;
      const xDown = xDownPlus - 1;
      const xDel = xDownPlus !== 0 && xDown < n ? xDown + 1 : -1;
      if (xDel >= 0) {
        let xx = xDel;
        let yy = xx - k;
        while (xx < n && yy < m && a[xx] === b[yy]) { xx++; yy++; }
        vCur[k + d] = xx + 1;
        if (xx >= n && yy >= m) { dFound = d; kFound = k; done = true; }
      }
    }
    trace.push(vCur);
    if (done) break;
    vPrev = vCur;
  }
  if (dFound < 0) throw new Error('makefun-diff: the search ended without reaching both ends');

  // Backtrack the single-line edits, from the end to the start. The pre-snake
  // position at each depth is recomputed from the previous frontier (the
  // tie-break rule picks it); the snake itself is never walked back over,
  // because the lines before a snake's start can match too (repeated lines),
  // which would move an edit to the wrong line.
  const edits = []; // {kind, idx} in reverse order: DELETE idx = old index, INSERT idx = new index
  let k = kFound;
  for (let d = dFound; d >= 1; d--) {
    const vPrevD = trace[d - 1];
    const iDown = k - 1 + (d - 1);
    const iUp = k + 1 + (d - 1);
    const xDownPlus = iDown >= 0 && iDown < vPrevD.length ? vPrevD[iDown] : 0;
    const xUpPlus = iUp >= 0 && iUp < vPrevD.length ? vPrevD[iUp] : 0;
    const xDown = xDownPlus - 1;
    const xUp = xUpPlus - 1;
    const xDel = xDownPlus !== 0 && xDown < n ? xDown + 1 : -1;
    const xIns = xUpPlus !== 0 && xUp - (k + 1) < m ? xUp : -1;
    if (xDel >= 0 && (xIns < 0 || xDel >= xIns)) {
      // Deletion: the line a[xDel - 1] (xDel is the pre-snake consumed count).
      edits.push({ kind: DELETE, idx: xDel - 1 });
      k -= 1;
    } else {
      // Insertion: the line b[xIns - k - 1] (pre-snake Y is xIns - k).
      edits.push({ kind: INSERT, idx: xIns - k - 1 });
      k += 1;
    }
  }
  edits.reverse();

  // Turn the edits into runs: kept lines are everything between edits. A
  // kept run consumes old and new lines together, so both pointers advance.
  const runs = [];
  let i = 0; // old consumed
  let j = 0; // new consumed
  const push = (kind, count) => {
    if (count <= 0) return;
    const last = runs[runs.length - 1];
    if (last !== undefined && last.kind === kind) last.count += count;
    else runs.push({ kind, count });
  };
  for (const e of edits) {
    if (e.kind === DELETE) {
      const keep = e.idx - i;
      push(KEEP, keep);
      i += keep;
      j += keep;
      push(DELETE, 1);
      i += 1;
    } else {
      const keep = e.idx - j;
      push(KEEP, keep);
      i += keep;
      j += keep;
      push(INSERT, 1);
      j += 1;
    }
  }
  push(KEEP, n - i); // i === n and j === m agree here (same diagonal end)
  return runs;
}

/** A line as the patch writes it: its op, the line, a newline, and "%" on a line of its own when it had none. */
function written(op, line) {
  return line.endsWith('\n') ? `${op}${line}` : `${op}${line}\n%\n`;
}

/** makefun-diff 1.0.0's answer for one case's input. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const aStr = tokenize(input.old);
  const bStr = tokenize(input.new);
  const n = aStr.length;
  const m = bStr.length;

  // Intern lines to ids (one Map pass over both texts).
  const ids = new Map();
  const a = new Int32Array(n);
  const b = new Int32Array(m);
  let nextId = 0;
  for (let i = 0; i < n; i++) {
    const s = aStr[i];
    let id = ids.get(s);
    if (id === undefined) { id = nextId++; ids.set(s, id); }
    a[i] = id;
  }
  for (let j = 0; j < m; j++) {
    const s = bStr[j];
    let id = ids.get(s);
    if (id === undefined) { id = nextId++; ids.set(s, id); }
    b[j] = id;
  }

  // The common prefix, then the common suffix of what is left.
  let prefix = 0;
  while (prefix < n && prefix < m && a[prefix] === b[prefix]) prefix++;
  let suffix = 0;
  while (suffix < n - prefix && suffix < m - prefix && a[n - 1 - suffix] === b[m - 1 - suffix]) suffix++;
  const runs = [];
  if (prefix > 0) runs.push({ kind: KEEP, count: prefix });
  runs.push(...editRuns(a.subarray(prefix, n - suffix), b.subarray(prefix, m - suffix), n - prefix - suffix, m - prefix - suffix));
  if (suffix > 0) runs.push({ kind: KEEP, count: suffix });

  // The change runs: each a stretch of deletions and insertions between two kept lines, at old line o and new line p.
  const changes = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  for (const r of runs) {
    if (r.kind === KEEP) {
      o += r.count;
      p += r.count;
      continue;
    }
    let c = changes[changes.length - 1];
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (r.kind === DELETE) {
      c.dels += r.count;
      o += r.count;
      deleted += r.count;
    } else {
      c.ins += r.count;
      p += r.count;
      inserted += r.count;
    }
  }

  // The hunks: change runs at most 2 * CONTEXT kept lines apart share one.
  const hunks = [];
  for (const c of changes) {
    const h = hunks[hunks.length - 1];
    const prev = h !== undefined ? h[h.length - 1] : undefined;
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 2 * CONTEXT) h.push(c);
    else hunks.push([c]);
  }
  const out = [`${FORMAT} old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  for (const h of hunks) {
    const first = h[0];
    const last = h[h.length - 1];
    const oldStart = Math.max(0, first.o - CONTEXT);
    const newStart = first.p - (first.o - oldStart);
    const after = Math.min(CONTEXT, n - (last.o + last.dels));
    const oldEnd = last.o + last.dels + after;
    const newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) out.push(written('=', aStr[at]));
      for (let t = 0; t < c.dels; t++) out.push(written('-', aStr[c.o + t]));
      for (let t = 0; t < c.ins; t++) out.push(written('+', bStr[c.p + t]));
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) out.push(written('=', aStr[at]));
  }
  return out.join('');
}
