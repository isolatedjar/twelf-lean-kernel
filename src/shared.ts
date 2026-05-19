// shared.ts — IR types shared between parse.ts and lean2lf.ts.
//
// parse.ts reads lean4export's NDJSON and emits an array of these
// resolved declarations as JSON.  lean2lf.ts reads that JSON on stdin
// and emits Twelf LF on stdout.
//
// Notes:
//   - All cross-references are by-value:  Name, Expr, Level, etc. are
//     fully resolved trees, not indices into a shared table.  This
//     is what makes the parsed output human-readable.
//   - lean2lf.ts trusts that its input matches these types (it's only
//     ever called on parse.ts's stdout), so we don't need runtime
//     validation here.  Replace with Zod if defensive parsing is
//     wanted later.

export type Name =
  | { kind: "anon" }
  | { kind: "str"; pre: Name; str: string }
  | { kind: "num"; pre: Name; i: number };

export type Level =
  | { kind: "zero" }
  | { kind: "succ"; arg: Level }
  | { kind: "max"; l: Level; r: Level }
  | { kind: "imax"; l: Level; r: Level }
  | { kind: "param"; name: Name };

export type BinderInfo = "default" | "implicit" | "strictImplicit" | "instImplicit";

export type Expr =
  | { kind: "bvar"; deBruijn: number }
  | { kind: "sort"; level: Level }
  | { kind: "const"; name: Name; us: Level[] }
  | { kind: "app"; fn: Expr; arg: Expr }
  | { kind: "lam"; name: Name; type: Expr; body: Expr }
  | { kind: "forallE"; name: Name; type: Expr; body: Expr }
  | { kind: "letE"; name: Name; type: Expr; value: Expr; body: Expr }
  | { kind: "proj"; typeName: Name; idx: number; struct: Expr }
  | { kind: "natLit"; value: string }
  | { kind: "strLit"; value: string };

// --- Inductive blocks ---------------------------------------------------
// An #IND record in NDJSON declares a mutual-inductive *block*: one or
// more inductive type formers, all their constructors, and all their
// recursors.  We package them together so lean2lf.ts has the full block
// available when emitting any individual piece.

export type IndType = {
  name: Name;
  levelParams: Name[];
  type: Expr;
  numParams: number;
  numIndices: number;
};

export type IndCtor = {
  name: Name;
  levelParams: Name[];
  type: Expr;
  numParams: number;
  numFields: number;
  induct: Name; // which IndType in the block this ctor belongs to
};

export type IndRecRule = {
  ctor: Name;
  nfields: number;
  rhs: Expr;
};

export type IndRecursor = {
  name: Name;
  levelParams: Name[];
  type: Expr;
  numParams: number;
  numIndices: number;
  numMotives: number;
  numMinors: number;
  rules: IndRecRule[];
  k: boolean;
};

export type Inductive = {
  kind: "inductive";
  types: IndType[];
  ctors: IndCtor[];
  recursors: IndRecursor[];
};

// --- Top-level declarations ---------------------------------------------

export type Decl =
  | { kind: "def"; name: Name; levelParams: Name[]; type: Expr; value: Expr }
  | { kind: "thm"; name: Name; levelParams: Name[]; type: Expr; value: Expr }
  | { kind: "axiom"; name: Name; levelParams: Name[]; type: Expr }
  | { kind: "opaque"; name: Name; levelParams: Name[]; type: Expr; value: Expr }
  | { kind: "quot" }
  | Inductive;

// The parsed environment, as emitted by parse.ts:
//   { decls: Decl[] }
// declared in the order the NDJSON declared them.
export type ParsedEnv = {
  decls: Decl[];
};

// --- Helpers ------------------------------------------------------------

export function nameToString(n: Name): string {
  switch (n.kind) {
    case "anon":
      return "";
    case "str": {
      const p = nameToString(n.pre);
      return p === "" ? n.str : `${p}.${n.str}`;
    }
    case "num": {
      const p = nameToString(n.pre);
      return p === "" ? `${n.i}` : `${p}.${n.i}`;
    }
  }
}

// --- JSON wire compaction for human-readable parse.ts output -------------
// In TypeScript the Name type is a left-recursive struct, which prints to
// JSON as a deeply nested object that's hard to skim.  For wire transport
// we compact a Name to a `(string | number)[]` (innermost-to-outermost
// path components, or the empty array for `anon`) and tag it so lean2lf.ts
// can find and re-inflate it.
//
// Tag shape: `{ "_n": ["Foo", "bar", 0] }`.  The `_n` key is unambiguous
// against the IR (no field is named `_n`).

export type NameJSON = { _n: (string | number)[] };

export function nameToJSON(n: Name): NameJSON {
  const parts: (string | number)[] = [];
  let cur: Name = n;
  while (cur.kind !== "anon") {
    parts.unshift(cur.kind === "str" ? cur.str : cur.i);
    cur = cur.pre;
  }
  return { _n: parts };
}

export function nameFromJSON(j: NameJSON): Name {
  let n: Name = { kind: "anon" };
  for (const p of j._n) {
    n = typeof p === "string" ? { kind: "str", pre: n, str: p } : { kind: "num", pre: n, i: p };
  }
  return n;
}

// Walk an arbitrary value, applying `tx` to anything that "looks like"
// a Name (recursive struct with kind="anon"/"str"/"num").  Used by
// parse.ts to compact Names before serialization, and by lean2lf.ts
// to re-inflate compacted Names after JSON.parse.
export function transformNamesToJSON(v: any): any {
  if (v === null || typeof v !== "object") return v;
  if (Array.isArray(v)) return v.map(transformNamesToJSON);
  if (v.kind === "anon" || v.kind === "str" || v.kind === "num") {
    return nameToJSON(v as Name);
  }
  const out: any = {};
  for (const k in v) out[k] = transformNamesToJSON(v[k]);
  return out;
}

export function transformNamesFromJSON(v: any): any {
  if (v === null || typeof v !== "object") return v;
  if (Array.isArray(v)) return v.map(transformNamesFromJSON);
  if ("_n" in v && Array.isArray(v._n)) return nameFromJSON(v as NameJSON);
  const out: any = {};
  for (const k in v) out[k] = transformNamesFromJSON(v[k]);
  return out;
}
