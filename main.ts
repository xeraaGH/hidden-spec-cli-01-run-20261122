// mend: one patch tool for every AI edit format.
//
// Reads a patch in one of four formats (unified diff, SEARCH/REPLACE blocks,
// V4A patches, JSON edits) and applies it to the tree of text files in the
// working directory, all or nothing. See SPEC.md for the contract.
// Node 22, the standard library alone; run as `node main.ts [options] [PATCH]`.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
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

/** A file split into lines: its line break, its lines, and whether it ends with a break. */
interface FileParts {
  lines: string[];
  br: string;
  ends: boolean;
}

function fileParts(text: string): FileParts {
  if (text === '') return { lines: [], br: '\n', ends: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text.split(br);
  const ends = text.endsWith(br);
  if (ends) lines.pop();
  return { lines, br, ends };
}

function joinParts(lines: string[], br: string, ends: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (ends ? br : '');
}

function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
}

function stripTrail(s: string): string {
  return s.replace(/[ \t]+$/, '');
}

function stripBoth(s: string): string {
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** One body line of a unified hunk or a V4A chunk. */
interface BodyItem {
  kind: 'ctx' | 'old' | 'new';
  text: string;
  noNL: boolean;
}

/** One line of N: `ctx` is its index in O when it is a context line, else -1. */
interface NLine {
  text: string;
  ctx: number;
}

function lineMatches(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return stripTrail(a) === stripTrail(b);
  return stripBoth(a) === stripBoth(b);
}

function occurrences(lines: string[], o: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  for (let i = from; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!lineMatches(lines[i + j]!, o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

interface Found {
  tier: number;
  positions: number[];
}

/** First tier at which O occurs at or after `from`, with every occurrence there. */
function findTier(lines: string[], o: string[], strict: boolean, from: number): Found | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const pos = occurrences(lines, o, t, from);
    if (pos.length > 0) return { tier: t, positions: pos };
  }
  return null;
}

/** O and N of a body, from its items. */
function itemsToON(items: BodyItem[]): { o: string[]; n: NLine[] } {
  const o: string[] = [];
  const ctxIdx: number[] = [];
  for (const it of items) {
    if (it.kind === 'ctx') {
      ctxIdx.push(o.length);
      o.push(it.text);
    } else if (it.kind === 'old') {
      o.push(it.text);
    }
  }
  const n: NLine[] = [];
  let k = 0;
  for (const it of items) {
    if (it.kind === 'ctx') {
      n.push({ text: it.text, ctx: ctxIdx[k]! });
      k++;
    } else if (it.kind === 'new') {
      n.push({ text: it.text, ctx: -1 });
    }
  }
  return { o, n };
}

/** Whether a `\` line follows the body's last context or `+` line (null: there is none). */
function lastNoNL(items: BodyItem[]): boolean | null {
  for (let i = items.length - 1; i >= 0; i--) {
    const it = items[i]!;
    if (it.kind === 'ctx' || it.kind === 'new') return it.noNL;
  }
  return null;
}

/** Build the replacement lines for an occurrence of O at `pos` in `fileLines`. */
function buildN(o: string[], n: NLine[], fileLines: string[], pos: number, tier: number): string[] {
  const f = o.length > 0 ? leadingWs(fileLines[pos]!) : '';
  const p = o.length > 0 ? leadingWs(o[0]!) : '';
  const out: string[] = [];
  for (const nl of n) {
    if (nl.ctx >= 0) {
      out.push(fileLines[pos + nl.ctx]!);
    } else if (tier === 2) {
      const t = nl.text;
      out.push(t !== '' && t.trim() !== '' && t.startsWith(p) ? f + t.slice(p.length) : t);
    } else {
      out.push(nl.text);
    }
  }
  return out;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
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

/* ------------------------------------------------------------------ */
/* Section 6: unified diffs                                            */
/* ------------------------------------------------------------------ */

interface Hunk {
  a: number;
  items: BodyItem[];
  o: string[];
  n: NLine[];
  last: boolean | null;
}

function bodyItems(raw: string[]): BodyItem[] {
  const items: BodyItem[] = [];
  for (const r of raw) {
    if (r.startsWith('\\')) {
      const prev = items[items.length - 1];
      if (prev !== undefined) prev.noNL = true;
      continue;
    }
    if (r.startsWith(' ')) items.push({ kind: 'ctx', text: r.slice(1), noNL: false });
    else if (r.startsWith('-')) items.push({ kind: 'old', text: r.slice(1), noNL: false });
    else if (r.startsWith('+')) items.push({ kind: 'new', text: r.slice(1), noNL: false });
    else items.push({ kind: 'ctx', text: '', noNL: false });
  }
  return items;
}

function makeHunk(a: number, raw: string[]): Hunk {
  const items = bodyItems(raw);
  const { o, n } = itemsToON(items);
  return { a, items, o, n, last: lastNoNL(items) };
}

/** Apply a section's hunks in order to a file's parts; throws Fail on a bad hunk. */
function applyHunks(parts: FileParts, hunks: Hunk[], strict: boolean, path: string): FileParts {
  let lines = [...parts.lines];
  let ends = parts.ends;
  let d = 0;
  for (const h of hunks) {
    if (h.o.length > 0) {
      const found = findTier(lines, h.o, strict, 0);
      if (found === null) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let best = found.positions[0]!;
      for (const p of found.positions) {
        if (Math.abs(p - target) < Math.abs(best - target)) best = p;
      }
      const repl = buildN(h.o, h.n, lines, best, found.tier);
      if (best + h.o.length === lines.length) ends = h.last === true ? false : true;
      lines.splice(best, h.o.length, ...repl);
    } else {
      // Insert after the first A + d lines; A + d can go below zero when an
      // earlier hunk shrank the file, which means the top of the file.
      const at = Math.max(0, Math.min(h.a + d, lines.length));
      const repl = buildN(h.o, h.n, lines, at, 0);
      if (at === lines.length && h.n.length > 0) ends = h.last === true ? false : true;
      lines.splice(at, 0, ...repl);
    }
    d += h.n.length - h.o.length;
  }
  return { lines, br: parts.br, ends };
}

function headerPath(line: string): string {
  const rest = line.slice(4);
  const tab = rest.indexOf('\t');
  return (tab >= 0 ? rest.slice(0, tab) : rest).trim();
}

function stripAB(p: string): string {
  if (p.startsWith('a/') || p.startsWith('b/')) return p.slice(2);
  return p;
}

interface UniHead {
  diffOld?: string;
  diffNew?: string;
}

/** Parse one unified section starting at `start`; append its edit; return the next index. */
function parseUniSection(
  lines: string[],
  start: number,
  head: UniHead,
  edits: Edit[],
  strict: boolean,
  registerMove: (oldP: string, newP: string) => void,
): number {
  let i = start;
  const n = lines.length;
  let headOld: string | undefined;
  let headNew: string | undefined;
  let renFrom: string | undefined;
  let renTo: string | undefined;
  let newFile = false;
  let deletedFile = false;
  const hunks: Hunk[] = [];
  let inHeader = true;
  while (i < n) {
    const line = lines[i]!;
    if (line.startsWith('@@')) {
      const hm = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
      if (hm === null) throw new Exit2(`error: parse ${i + 1}`);
      const a = parseInt(hm[1]!, 10);
      i++;
      const raw: string[] = [];
      while (i < n) {
        const bl = lines[i]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (bl === '' || bl[0] === ' ' || bl[0] === '-' || bl[0] === '+' || bl[0] === '\\') {
          raw.push(bl);
          i++;
        } else break;
      }
      while (raw.length > 0 && raw[raw.length - 1] === '') raw.pop();
      hunks.push(makeHunk(a, raw));
      inHeader = false;
      continue;
    }
    if (inHeader) {
      if (line.startsWith('--- ')) {
        if ((lines[i + 1] ?? '').startsWith('+++ ')) {
          headOld = stripAB(headerPath(line));
          headNew = stripAB(headerPath(lines[i + 1]!));
          i += 2;
          continue;
        }
        throw new Exit2(`error: parse ${i + 2}`);
      }
      if (line.startsWith('+++ ')) {
        headNew = stripAB(headerPath(line));
        i++;
        continue;
      }
      if (line.startsWith('rename from ')) {
        renFrom = line.slice(12).trim();
        i++;
        continue;
      }
      if (line.startsWith('rename to ')) {
        renTo = line.slice(10).trim();
        i++;
        continue;
      }
      if (line.startsWith('new file mode')) {
        newFile = true;
        i++;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        deletedFile = true;
        i++;
        continue;
      }
      if (line.startsWith('diff --git ')) break;
      i++;
      continue;
    }
    if (line.startsWith('diff --git ')) break;
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
    i++;
  }

  const oldRaw = headOld ?? renFrom ?? head.diffOld;
  const newRaw = headNew ?? renTo ?? head.diffNew;
  const oldIsNull = oldRaw === '/dev/null';
  const newIsNull = newRaw === '/dev/null';
  const oldEff = oldRaw !== undefined && !oldIsNull ? oldRaw : undefined;
  const newEff = newRaw !== undefined && !newIsNull ? newRaw : undefined;
  const checkPaths = (tree: Tree): void => {
    if (oldEff !== undefined && !safe(oldEff)) throw new Fail('unsafe', oldEff);
    if (newEff !== undefined && !safe(newEff)) throw new Fail('unsafe', newEff);
  };

  if (newFile || oldIsNull) {
    const np = newEff ?? oldEff ?? '';
    edits.push((tree) => {
      checkPaths(tree);
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const plus: string[] = [];
      let last: boolean | null = null;
      for (const h of hunks) {
        for (const it of h.items) {
          if (it.kind === 'new') {
            plus.push(it.text);
            last = it.noNL;
          }
        }
      }
      tree.now.set(np, plus.length === 0 ? '' : plus.join('\n') + (last === true ? '' : '\n'));
    });
  } else if (deletedFile || newIsNull) {
    const op = oldEff ?? newEff ?? '';
    edits.push((tree) => {
      checkPaths(tree);
      if (tree.get(op) === null) throw new Fail('missing', op);
      tree.now.set(op, null);
    });
  } else if (oldEff !== undefined && newEff !== undefined && oldEff !== newEff) {
    const op = oldEff;
    const np = newEff;
    edits.push((tree) => {
      checkPaths(tree);
      const before = tree.get(op);
      if (before === null) throw new Fail('missing', op);
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const out = applyHunks(fileParts(before), hunks, strict, op);
      tree.now.set(np, joinParts(out.lines, out.br, out.ends));
      tree.now.set(op, null);
      registerMove(op, np);
    });
  } else {
    const p = oldEff ?? newEff ?? '';
    edits.push((tree) => {
      checkPaths(tree);
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const out = applyHunks(fileParts(before), hunks, strict, p);
      tree.now.set(p, joinParts(out.lines, out.br, out.ends));
    });
  }
  return i;
}

function unifiedEdits(
  lines: string[],
  strict: boolean,
  registerMove: (oldP: string, newP: string) => void,
): Edit[] {
  const edits: Edit[] = [];
  const n = lines.length;
  let i = 0;
  while (i < n) {
    const line = lines[i]!;
    if (line.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/([^ ]+) b\/([^ ]+)[ \t]*$/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      i = parseUniSection(lines, i + 1, { diffOld: m[1]!, diffNew: m[2]! }, edits, strict, registerMove);
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      i = parseUniSection(lines, i, {}, edits, strict, registerMove);
      continue;
    }
    i++;
  }
  return edits;
}

/* ------------------------------------------------------------------ */
/* Section 7: SEARCH/REPLACE blocks                                    */
/* ------------------------------------------------------------------ */

function searchEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const parts = fileParts(before);
    const found = findTier(parts.lines, oldLines, strict, 0);
    if (found === null) throw new Fail('no-match', path);
    if (found.positions.length > 1) throw new Fail('ambiguous', path);
    const pos = found.positions[0]!;
    const nlines: NLine[] = newLines.map((t) => ({ text: t, ctx: -1 }));
    const repl = buildN(oldLines, nlines, parts.lines, pos, found.tier);
    const out = [...parts.lines];
    out.splice(pos, oldLines.length, ...repl);
    tree.now.set(path, joinParts(out, parts.br, parts.ends));
  };
}

function searchEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  const n = lines.length;
  let prevEnd = -1;
  let prevPath: string | undefined;
  let i = 0;
  while (i < n) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const s = i;
    let path: string | undefined;
    for (let j = s - 1; j > prevEnd; j--) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === undefined) path = prevPath;
    if (path === undefined) throw new Exit2(`error: parse ${s + 1}`);
    let eq = -1;
    let rep = -1;
    for (let j = s + 1; j < n; j++) {
      const t = lines[j]!.trimEnd();
      if (t === '<<<<<<< SEARCH') break;
      if (eq < 0) {
        if (t === '=======') eq = j;
      } else if (t === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (eq < 0 || rep < 0) throw new Exit2(`error: parse ${s + 1}`);
    edits.push(searchEdit(path, lines.slice(s + 1, eq), lines.slice(eq + 1, rep), strict));
    prevPath = path;
    prevEnd = rep;
    i = rep + 1;
  }
  return edits;
}

/* ------------------------------------------------------------------ */
/* Section 8: V4A patches                                              */
/* ------------------------------------------------------------------ */

interface VChunk {
  anchor: string | null;
  eof: boolean;
  items: BodyItem[];
}

function v4aAddEdit(path: string, flines: string[]): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) !== null) throw new Fail('exists', path);
    tree.now.set(path, flines.length === 0 ? '' : flines.join('\n') + '\n');
  };
}

function v4aDeleteEdit(path: string): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) === null) throw new Fail('missing', path);
    tree.now.set(path, null);
  };
}

function v4aUpdateEdit(
  path: string,
  moveTo: string | undefined,
  chunks: VChunk[],
  strict: boolean,
  registerMove: (oldP: string, newP: string) => void,
): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== undefined && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    if (moveTo !== undefined && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const parts = fileParts(before);
    const lines = [...parts.lines];
    let cursor = 0;
    for (const ch of chunks) {
      const { o, n } = itemsToON(ch.items);
      if (ch.anchor !== null && ch.anchor !== '') {
        const found = findTier(lines, [ch.anchor], strict, cursor);
        if (found === null) throw new Fail('no-match', path);
        cursor = found.positions[0]! + 1;
      }
      if (o.length > 0) {
        const found = findTier(lines, o, strict, cursor);
        if (found === null) throw new Fail('no-match', path);
        let pos: number | undefined;
        for (const p of found.positions) {
          if (ch.eof && p + o.length !== lines.length) continue;
          pos = p;
          break;
        }
        if (pos === undefined) throw new Fail('no-match', path);
        const repl = buildN(o, n, lines, pos, found.tier);
        lines.splice(pos, o.length, ...repl);
        cursor = pos + repl.length;
      } else {
        const at = ch.eof ? lines.length : cursor;
        const repl = buildN(o, n, lines, at, 0);
        lines.splice(at, 0, ...repl);
        cursor = at + repl.length;
      }
    }
    const text = joinParts(lines, parts.br, parts.ends);
    if (moveTo !== undefined) {
      tree.now.set(moveTo, text);
      tree.now.set(path, null);
      registerMove(path, moveTo);
    } else {
      tree.now.set(path, text);
    }
  };
}

function v4aEdits(
  lines: string[],
  strict: boolean,
  registerMove: (oldP: string, newP: string) => void,
): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const secStart = (l: string): 'add' | 'delete' | 'update' | null => {
    if (l.startsWith('*** Add File: ')) return 'add';
    if (l.startsWith('*** Delete File: ')) return 'delete';
    if (l.startsWith('*** Update File: ')) return 'update';
    return null;
  };
  const edits: Edit[] = [];
  const n = last;
  let i = first + 1;
  while (i < n) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    const kind = secStart(line);
    if (kind === null) throw new Exit2(`error: parse ${i + 1}`);
    if (kind === 'add') {
      const path = line.slice('*** Add File: '.length).trim();
      i++;
      const flines: string[] = [];
      while (i < n) {
        const l = lines[i]!;
        if (secStart(l) !== null) break;
        if (blank(l)) {
          flines.push('');
          i++;
          continue;
        }
        if (l.startsWith('+')) {
          flines.push(l.slice(1));
          i++;
          continue;
        }
        throw new Exit2(`error: parse ${i + 1}`);
      }
      while (flines.length > 0 && flines[flines.length - 1] === '') flines.pop();
      edits.push(v4aAddEdit(path, flines));
      continue;
    }
    if (kind === 'delete') {
      const path = line.slice('*** Delete File: '.length).trim();
      i++;
      while (i < n) {
        const l = lines[i]!;
        if (secStart(l) !== null) break;
        if (blank(l)) {
          i++;
          continue;
        }
        throw new Exit2(`error: parse ${i + 1}`);
      }
      edits.push(v4aDeleteEdit(path));
      continue;
    }
    const path = line.slice('*** Update File: '.length).trim();
    const updateLine = i + 1;
    i++;
    let moveTo: string | undefined;
    if (i < n && lines[i]!.startsWith('*** Move to: ')) {
      moveTo = lines[i]!.slice('*** Move to: '.length).trim();
      i++;
    }
    const chunks: VChunk[] = [];
    let cur: VChunk | null = null;
    let firstChunk = true;
    while (i < n) {
      const l = lines[i]!;
      if (secStart(l) !== null) break;
      if (l.startsWith('@@')) {
        if (cur !== null) chunks.push(cur);
        cur = { anchor: l.slice(2).trim(), eof: false, items: [] };
        firstChunk = false;
        i++;
        continue;
      }
      if (l.trim() === '*** End of File') {
        if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
        cur.eof = true;
        chunks.push(cur);
        cur = null;
        i++;
        continue;
      }
      if (blank(l)) {
        if (cur !== null) cur.items.push({ kind: 'ctx', text: '', noNL: false });
        i++;
        continue;
      }
      if (l[0] === ' ' || l[0] === '-' || l[0] === '+') {
        if (cur === null) {
          if (!firstChunk) throw new Exit2(`error: parse ${i + 1}`);
          cur = { anchor: null, eof: false, items: [] };
          firstChunk = false;
        }
        if (l[0] === ' ') cur.items.push({ kind: 'ctx', text: l.slice(1), noNL: false });
        else if (l[0] === '-') cur.items.push({ kind: 'old', text: l.slice(1), noNL: false });
        else cur.items.push({ kind: 'new', text: l.slice(1), noNL: false });
        i++;
        continue;
      }
      throw new Exit2(`error: parse ${i + 1}`);
    }
    if (cur !== null) chunks.push(cur);
    if (chunks.length > 0) {
      // Blank lines at the end of a section are not part of it, but blank
      // lines before a `*** End of File` line are the chunk's own content:
      // that chunk is already closed, so only strip an open-ended last chunk.
      const lastc = chunks[chunks.length - 1]!;
      if (!lastc.eof) {
        while (lastc.items.length > 0) {
          const it = lastc.items[lastc.items.length - 1]!;
          if (it.kind === 'ctx' && it.text === '') lastc.items.pop();
          else break;
        }
        if (lastc.items.length === 0 && lastc.anchor === null) chunks.pop();
      }
    }
    if (chunks.length === 0 && moveTo === undefined) throw new Exit2(`error: parse ${updateLine}`);
    edits.push(v4aUpdateEdit(path, moveTo, chunks, strict, registerMove));
  }
  return edits;
}

/* ------------------------------------------------------------------ */
/* Section 1, 2, 10: invocation, output, order and atomicity           */
/* ------------------------------------------------------------------ */

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  const moves: [string, string][] = [];
  const registerMove = (oldP: string, newP: string): void => {
    moves.push([oldP, newP]);
  };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict, registerMove);
    else if (kind === 'search-replace') edits = searchEdits(lines, strict);
    else edits = v4aEdits(lines, strict, registerMove);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const byKey = new Map<string, string>();
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    byKey.set(p, `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`);
  }
  for (const [oldP, newP] of moves) {
    if (tree.original(oldP) !== null && tree.get(oldP) === null && tree.original(newP) === null && tree.get(newP) !== null) {
      byKey.delete(oldP);
      byKey.delete(newP);
      byKey.set(newP, `R ${oldP} -> ${newP}`);
    }
  }
  const rows = [...byKey.entries()]
    .sort((a, b) => Buffer.compare(Buffer.from(a[0]), Buffer.from(b[0])))
    .map(([, r]) => r);
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (check) continue;
    if (now === null) rmSync(p, { force: true });
    else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
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
