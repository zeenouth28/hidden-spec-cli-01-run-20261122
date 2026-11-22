// mend: one patch tool for every AI edit format, as SPEC.md (version 1) specifies.
//
//   node main.ts [--format=NAME] [--check] [--strict] [PATCH]
//
// It reads a patch in one of four shapes (unified diff, SEARCH/REPLACE blocks,
// V4A patches, JSON tool calls), finds the lines each edit names at the first
// of three matching tiers, and changes every file or none. Node 22, standard
// library only.
//
// When MAKEFUN_ENV_URL is set, this file hands the run over to runner.ts,
// which the grader uses to run the checks; keep that hand-over and runner.ts
// as the kit has them.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** Thrown to answer exit 2 with one line. */
class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

/** Thrown by one edit to report its failure; the edit changes nothing. */
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

/** A patch's lines: split at \n, one trailing \r removed, no empty tail piece. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

const byteOrder = (a: string, b: string): number => Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));

/** A file's lines, its line break, and whether it ends with one. */
interface FileState {
  lines: string[];
  br: string;
  finalBreak: boolean;
}

function parseFile(text: string): FileState {
  if (text === '') return { lines: [], br: '\n', finalBreak: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const finalBreak = text.endsWith(br);
  if (finalBreak) parts.pop();
  return { lines: parts, br, finalBreak };
}

function serializeFile(f: FileState): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.finalBreak ? f.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted). */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  moves: Array<{ old: string; nw: string }> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

// ---------------------------------------------------------------- matching

const trail = (s: string): string => s.replace(/[ \t]+$/, '');
const both = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const lead = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
};

function lineMatches(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trail(a) === trail(b);
  return both(a) === both(b);
}

/** Every position where the pattern occurs in the file at one tier. */
function tierPositions(lines: string[], pat: string[], tier: number): number[] {
  const out: number[] = [];
  if (pat.length === 0 || pat.length > lines.length) return out;
  for (let i = 0; i + pat.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < pat.length; j++) {
      if (!lineMatches(lines[i + j]!, pat[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier at which the pattern occurs, with its positions, or null. */
function findTier(lines: string[], pat: string[], strict: boolean, from = 0): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const positions = tierPositions(lines, pat, t).filter((p) => p >= from);
    if (positions.length > 0) return { tier: t, positions };
  }
  return null;
}

/** The first line at or after `from` equal to the anchor, first tier with one. */
function findAnchor(lines: string[], anchor: string, from: number, strict: boolean): number {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    for (let i = from; i < lines.length; i++) {
      if (lineMatches(lines[i]!, anchor, t)) return i;
    }
  }
  return -1;
}

/** Re-indent one new line at tier 2: the pattern's leading whitespace becomes the file's. */
function reindent(line: string, pfx: string, f: string): string {
  if (line === '' || line.trim() === '') return line;
  if (!line.startsWith(pfx)) return line;
  return f + line.slice(pfx.length);
}

/** One body line, tagged: ' ' context, '-' old, '+' new, '\\' a backslash line. */
interface BodyLine {
  tag: ' ' | '-' | '+' | '\\';
  text: string;
}

function tagOf(line: string): BodyLine | null {
  if (line === '') return { tag: ' ', text: '' };
  if (line.startsWith(' ')) return { tag: ' ', text: line.slice(1) };
  if (line.startsWith('-')) return { tag: '-', text: line.slice(1) };
  if (line.startsWith('+')) return { tag: '+', text: line.slice(1) };
  if (line.startsWith('\\')) return { tag: '\\', text: line };
  return null;
}

/** Split body lines into old lines O and new lines N; ctx maps each N line to its O line, or -1. */
function splitBody(body: BodyLine[]): { o: string[]; n: string[]; ctx: number[] } {
  const o: string[] = [];
  const n: string[] = [];
  const ctx: number[] = [];
  for (const b of body) {
    if (b.tag === ' ') {
      const oi = o.length;
      o.push(b.text);
      const ni = n.length;
      n.push(b.text);
      ctx[ni] = oi;
    } else if (b.tag === '-') {
      o.push(b.text);
    } else if (b.tag === '+') {
      const ni = n.length;
      n.push(b.text);
      ctx[ni] = -1;
    }
  }
  return { o, n, ctx };
}

/** Build the replacement lines: context lines come from the file, the rest are re-indented at tier 2. */
function replacement(n: string[], ctx: number[], fileLines: string[], pos: number, tier: number, o: string[]): string[] {
  const f = lead(fileLines[pos]!);
  const pfx = lead(o[0]!);
  return n.map((line, ni) => {
    const oi = ctx[ni]!;
    if (oi >= 0) return fileLines[pos + oi]!;
    return tier === 2 ? reindent(line, pfx, f) : line;
  });
}

/** Whether a backslash line follows the hunk's last context or '+' line. */
function noNewlineAfter(body: BodyLine[]): boolean {
  let last = -1;
  for (let k = 0; k < body.length; k++) {
    if (body[k]!.tag === ' ' || body[k]!.tag === '+') last = k;
  }
  if (last < 0) return false;
  return body[last + 1]?.tag === '\\';
}

// ---------------------------------------------------------------- detection

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  for (let i = 0; i < lines.length; i++) {
    if (lines[i]!.startsWith('diff --git ')) return 'unified';
    if (lines[i]!.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) return 'unified';
  }
  return null;
}

// ---------------------------------------------------------------- unified

interface UniHunk {
  a: number;
  body: BodyLine[];
}

interface UniSection {
  pairOld: string | null;
  pairNew: string | null;
  renameFrom: string | null;
  renameTo: string | null;
  diffOld: string;
  diffNew: string;
  createMode: boolean;
  deleteMode: boolean;
  hunks: UniHunk[];
}

function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: UniSection[] = [];
  let sec: UniSection | null = null;
  let hunk: UniHunk | null = null;
  let secHasPair = false;
  let secHasHunk = false;

  const finishHunk = (): void => {
    if (!hunk || !sec) return;
    while (hunk.body.length > 0) {
      const b = hunk.body[hunk.body.length - 1]!;
      if (b.tag === ' ' && b.text === '') hunk.body.pop();
      else break;
    }
    sec.hunks.push(hunk);
    hunk = null;
  };
  const startSection = (diffOld: string, diffNew: string): void => {
    finishHunk();
    sec = {
      pairOld: null,
      pairNew: null,
      renameFrom: null,
      renameTo: null,
      diffOld,
      diffNew,
      createMode: false,
      deleteMode: false,
      hunks: [],
    };
    sections.push(sec);
    secHasPair = false;
    secHasHunk = false;
  };
  const diffGitPaths = (line: string): [string, string] | null => {
    const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(line);
    return m ? [m[1]!, m[2]!] : null;
  };
  const hunkStart = (line: string): number | null => {
    const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
    return m ? Number(m[1]) : null;
  };
  const markerPath = (line: string): string => {
    let p = line.slice(4);
    const tab = p.indexOf('\t');
    if (tab >= 0) p = p.slice(0, tab);
    p = p.trim();
    if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
    return p;
  };

  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    const no = i + 1;
    if (hunk) {
      if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
        finishHunk();
      } else if (line === '' || line.startsWith(' ') || line.startsWith('-') || line.startsWith('+') || line.startsWith('\\')) {
        hunk.body.push(tagOf(line)!);
        i++;
        continue;
      } else {
        finishHunk();
      }
    }
    if (line.startsWith('diff --git ')) {
      const dg = diffGitPaths(line);
      if (!dg) throw new Exit2(`error: parse ${no}`);
      startSection(dg[0], dg[1]);
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      if (!sec) throw new Exit2(`error: parse ${no}`);
      const a = hunkStart(line);
      if (a === null) throw new Exit2(`error: parse ${no}`);
      hunk = { a, body: [] };
      secHasHunk = true;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const o = markerPath(line);
      const n = markerPath(lines[i + 1]!);
      if (sec && !secHasHunk && !secHasPair) {
        sec.pairOld = o;
        sec.pairNew = n;
        secHasPair = true;
      } else {
        startSection(o, n);
        sec!.pairOld = o;
        sec!.pairNew = n;
        secHasPair = true;
      }
      i += 2;
      continue;
    }
    if (line.startsWith('--- ')) {
      if (sec && !secHasHunk) throw new Exit2(`error: parse ${no + 1}`);
      i++;
      continue;
    }
    if (sec && !secHasHunk) {
      if (line.startsWith('rename from ')) {
        if (sec.renameFrom === null) sec.renameFrom = line.slice(12).trim();
      } else if (line.startsWith('rename to ')) {
        if (sec.renameTo === null) sec.renameTo = line.slice(10).trim();
      } else if (line.startsWith('new file mode')) {
        sec.createMode = true;
      } else if (line.startsWith('deleted file mode')) {
        sec.deleteMode = true;
      }
      i++;
      continue;
    }
    i++;
  }
  finishHunk();
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((s) => unifiedEdit(s, strict));
}

/** Apply one section's hunks in order to a file's state. */
function applyUniHunks(state: FileState, hunks: UniHunk[], strict: boolean, path: string): void {
  let d = 0;
  for (const h of hunks) {
    const { o, n, ctx } = splitBody(h.body);
    if (o.length === 0) {
      let idx = h.a + d;
      if (idx < 0) idx = 0;
      if (idx > state.lines.length) idx = state.lines.length;
      const atEnd = idx === state.lines.length;
      state.lines.splice(idx, 0, ...n);
      if (atEnd) state.finalBreak = !noNewlineAfter(h.body);
      d += n.length;
      continue;
    }
    const found = findTier(state.lines, o, strict);
    if (!found) throw new Fail('no-match', path);
    const target = h.a - 1 + d;
    let best = found.positions[0]!;
    for (const p of found.positions) {
      if (Math.abs(p - target) < Math.abs(best - target)) best = p;
    }
    const pos = best;
    const atEnd = pos + o.length === state.lines.length;
    const repl = replacement(n, ctx, state.lines, pos, found.tier, o);
    state.lines.splice(pos, o.length, ...repl);
    if (atEnd) state.finalBreak = !noNewlineAfter(h.body);
    d += n.length - o.length;
  }
}

function unifiedEdit(sec: UniSection, strict: boolean): Edit {
  const oldPath = sec.pairOld ?? sec.renameFrom ?? sec.diffOld;
  const newPath = sec.pairNew ?? sec.renameTo ?? sec.diffNew;
  const isCreate = oldPath === '/dev/null' || sec.createMode;
  const isDelete = newPath === '/dev/null' || sec.deleteMode;
  return (tree) => {
    if (isCreate) {
      if (!safe(newPath)) throw new Fail('unsafe', newPath);
      if (tree.get(newPath) !== null) throw new Fail('exists', newPath);
      const plus: string[] = [];
      let noNl = false;
      for (const h of sec.hunks) {
        for (let k = 0; k < h.body.length; k++) {
          if (h.body[k]!.tag === '+') {
            plus.push(h.body[k]!.text);
            noNl = h.body[k + 1]?.tag === '\\';
          }
        }
      }
      const state: FileState = { lines: plus, br: '\n', finalBreak: plus.length > 0 ? !noNl : false };
      tree.now.set(newPath, serializeFile(state));
      return;
    }
    if (isDelete) {
      if (!safe(oldPath)) throw new Fail('unsafe', oldPath);
      if (tree.get(oldPath) === null) throw new Fail('missing', oldPath);
      tree.now.set(oldPath, null);
      return;
    }
    if (oldPath !== newPath) {
      if (!safe(oldPath)) throw new Fail('unsafe', oldPath);
      if (!safe(newPath)) throw new Fail('unsafe', newPath);
      const text = tree.get(oldPath);
      if (text === null) throw new Fail('missing', oldPath);
      if (tree.get(newPath) !== null) throw new Fail('exists', newPath);
      const state = parseFile(text);
      applyUniHunks(state, sec.hunks, strict, oldPath);
      tree.now.set(newPath, serializeFile(state));
      tree.now.set(oldPath, null);
      tree.moves.push({ old: oldPath, nw: newPath });
      return;
    }
    if (!safe(oldPath)) throw new Fail('unsafe', oldPath);
    const text = tree.get(oldPath);
    if (text === null) throw new Fail('missing', oldPath);
    const state = parseFile(text);
    applyUniHunks(state, sec.hunks, strict, oldPath);
    tree.now.set(oldPath, serializeFile(state));
  };
}

// ---------------------------------------------------------------- search/replace

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevReplaceEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchNo = i + 1;
    let path: string | null = null;
    for (let j = i - 1; j > prevReplaceEnd; j--) {
      const t = lines[j]!;
      if (blank(t)) continue;
      const tr = t.trim();
      if (tr.startsWith('```')) continue;
      path = tr;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchNo}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = i + 1; j < lines.length; j++) {
      const t = lines[j]!.trimEnd();
      if (t === '=======') {
        eq = j;
        break;
      }
      if (t === '<<<<<<< SEARCH' || t === '>>>>>>> REPLACE') break;
    }
    if (eq === -1) throw new Exit2(`error: parse ${searchNo}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      const t = lines[j]!.trimEnd();
      if (t === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
      if (t === '<<<<<<< SEARCH') break;
    }
    if (rep === -1) throw new Exit2(`error: parse ${searchNo}`);
    const oldLines = lines.slice(i + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    edits.push(searchReplaceEdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevReplaceEnd = rep;
    i = rep + 1;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function searchReplaceEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      const state: FileState = { lines: [...newLines], br: '\n', finalBreak: newLines.length > 0 };
      tree.now.set(path, serializeFile(state));
      return;
    }
    const text = tree.get(path);
    if (text === null) throw new Fail('missing', path);
    const state = parseFile(text);
    const found = findTier(state.lines, oldLines, strict);
    if (!found) throw new Fail('no-match', path);
    if (found.positions.length > 1) throw new Fail('ambiguous', path);
    const pos = found.positions[0]!;
    const repl = replacement(newLines, newLines.map(() => -1), state.lines, pos, found.tier, oldLines);
    state.lines.splice(pos, oldLines.length, ...repl);
    tree.now.set(path, serializeFile(state));
  };
}

// ---------------------------------------------------------------- v4a

interface V4aChunk {
  anchor: string | null;
  body: BodyLine[];
  eof: boolean;
}

function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i]!)) {
      last = i;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const isStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    let kind: 'add' | 'delete' | 'update';
    let path: string;
    if (line.startsWith('*** Add File: ')) {
      kind = 'add';
      path = line.slice(14).trim();
    } else if (line.startsWith('*** Delete File: ')) {
      kind = 'delete';
      path = line.slice(17).trim();
    } else if (line.startsWith('*** Update File: ')) {
      kind = 'update';
      path = line.slice(17).trim();
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    let j = i + 1;
    while (j < last && !isStart(lines[j]!)) j++;
    let end = j;
    while (end > i + 1 && blank(lines[end - 1]!)) end--;
    const content: Array<{ text: string; no: number }> = [];
    for (let k = i + 1; k < end; k++) content.push({ text: lines[k]!, no: k + 1 });
    edits.push(v4aEdit(kind, path, content, i + 1, strict));
    i = j;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function v4aEdit(
  kind: 'add' | 'delete' | 'update',
  path: string,
  content: Array<{ text: string; no: number }>,
  headerNo: number,
  strict: boolean,
): Edit {
  if (kind === 'add') {
    const fileLines: string[] = [];
    for (const { text, no } of content) {
      if (text === '') fileLines.push('');
      else if (text.startsWith('+')) fileLines.push(text.slice(1));
      else throw new Exit2(`error: parse ${no}`);
    }
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) !== null) throw new Fail('exists', path);
      const state: FileState = { lines: fileLines, br: '\n', finalBreak: fileLines.length > 0 };
      tree.now.set(path, serializeFile(state));
    };
  }
  if (kind === 'delete') {
    if (content.length > 0) throw new Exit2(`error: parse ${content[0]!.no}`);
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) === null) throw new Fail('missing', path);
      tree.now.set(path, null);
    };
  }
  let moveTo: string | null = null;
  let idx = 0;
  if (content.length > 0 && content[0]!.text.startsWith('*** Move to: ')) {
    moveTo = content[0]!.text.slice(13).trim();
    idx = 1;
  }
  const chunks: V4aChunk[] = [];
  let cur: V4aChunk | null = null;
  while (idx < content.length) {
    const { text, no } = content[idx]!;
    if (text.startsWith('@@')) {
      if (cur) chunks.push(cur);
      const anchor = text.slice(2).trim();
      cur = { anchor: anchor === '' ? null : anchor, body: [], eof: false };
      idx++;
    } else if (text === '*** End of File') {
      if (cur) {
        cur.eof = true;
        chunks.push(cur);
        cur = null;
      }
      idx++;
    } else if (tagOf(text) !== null) {
      if (!cur) {
        if (chunks.length > 0) throw new Exit2(`error: parse ${no}`);
        cur = { anchor: null, body: [], eof: false };
      }
      cur.body.push(tagOf(text)!);
      idx++;
    } else {
      throw new Exit2(`error: parse ${no}`);
    }
  }
  if (cur) chunks.push(cur);
  if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${headerNo}`);
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    const text = tree.get(path);
    if (text === null) throw new Fail('missing', path);
    if (moveTo !== null) {
      if (!safe(moveTo)) throw new Fail('unsafe', moveTo);
      if (tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    }
    const state = parseFile(text);
    let cursor = 0;
    for (const chunk of chunks) {
      if (chunk.anchor !== null) {
        const aPos = findAnchor(state.lines, chunk.anchor, cursor, strict);
        if (aPos < 0) throw new Fail('no-match', path);
        cursor = aPos + 1;
      }
      const { o, n, ctx } = splitBody(chunk.body);
      if (o.length === 0) {
        const at = chunk.eof ? state.lines.length : cursor;
        state.lines.splice(at, 0, ...n);
        cursor = at + n.length;
        continue;
      }
      const found = findTier(state.lines, o, strict, cursor);
      if (!found) throw new Fail('no-match', path);
      let positions = found.positions;
      if (chunk.eof) positions = positions.filter((p) => p + o.length === state.lines.length);
      if (positions.length === 0) throw new Fail('no-match', path);
      const pos = positions[0]!;
      const repl = replacement(n, ctx, state.lines, pos, found.tier, o);
      state.lines.splice(pos, o.length, ...repl);
      cursor = pos + repl.length;
    }
    if (moveTo !== null) {
      tree.now.set(moveTo, serializeFile(state));
      tree.now.set(path, null);
      tree.moves.push({ old: path, nw: moveTo });
    } else {
      tree.now.set(path, serializeFile(state));
    }
  };
}

// ---------------------------------------------------------------- json

function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  if (typeof o.path !== 'string') return null;
  const p = o.path;
  const need = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create') {
    if (typeof o.file_text !== 'string') return null;
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace') {
    if (typeof o.old_str !== 'string' || o.old_str === '') return null;
    if (o.new_str !== undefined && typeof o.new_str !== 'string') return null;
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = need(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const norm = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = norm(before);
      const old = norm(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + norm(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert') {
    if (typeof o.insert_line !== 'number' || !Number.isInteger(o.insert_line)) return null;
    if (typeof o.new_str !== 'string') return null;
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = need(tree);
      const state = parseFile(before);
      if (line < 0 || line > state.lines.length) throw new Fail('no-match', p);
      state.lines.splice(line, 0, ...add);
      tree.now.set(p, serializeFile(state));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------------------------------------------------------------- run

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') {
      ended = true;
      continue;
    }
    if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) {
        format = a.slice(9);
        continue;
      }
      if (a === '--check' && !check) {
        check = true;
        continue;
      }
      if (a === '--strict' && !strict) {
        strict = true;
        continue;
      }
      return { code: 2, out: ['error: usage'] };
    }
    pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const patchArg = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(patchArg ?? 0, 'utf8');
  } catch {
    if (patchArg !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const snap = new Map(tree.now);
    const snapMoves = [...tree.moves];
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of snap) tree.now.set(k, v);
      tree.moves = snapMoves;
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }
  const rows: Array<{ key: string; line: string }> = [];
  const covered = new Set<string>();
  for (const m of tree.moves) {
    const wasOld = tree.original(m.old);
    const nowOld = tree.get(m.old);
    const wasNew = tree.original(m.nw);
    const nowNew = tree.get(m.nw);
    if (wasOld !== null && nowOld === null && wasNew === null && nowNew !== null) {
      rows.push({ key: m.nw, line: `R ${m.old} -> ${m.nw}` });
      covered.add(m.old);
      covered.add(m.nw);
    }
  }
  for (const p of tree.now.keys()) {
    if (covered.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: was === null ? `A ${p}` : now === null ? `D ${p}` : `M ${p}` });
  }
  rows.sort((a, b) => byteOrder(a.key, b.key));
  const out = rows.map((r) => r.line);
  if (!check) {
    for (const p of [...tree.now.keys()]) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...out, `ok: ${out.length} ${out.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
