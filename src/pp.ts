// pp.ts — minimal Wadler-style pretty printer.
//
// Provides a `Doc` algebra and a `render(width, doc)` function that lays it
// out trying to keep each `group` on one line, breaking + indenting otherwise.
//
// Algebra (Wadler, "A Prettier Printer", 1997):
//   nil               — empty
//   text(s)           — atomic text (must not contain newlines)
//   line              — a soft break: " " if the enclosing group fits, else
//                        "\n" + current indent
//   nest(n, d)        — increase the current indent by n inside d
//   concat(...ds)     — concatenation
//   group(d)          — render d on one line if possible, breaking only when
//                       its first-line layout would exceed width
//
// Renderer is iterative (no recursion stack growth on deep terms) and uses
// a greedy `fits` lookahead at each group: if the document up to the next
// real newline fits in the remaining columns when flattened, use the flat
// layout; otherwise use the broken layout.  Inherited mode propagates —
// when a group is entered in flat mode, every nested group inside it is
// also flat (because flat means all lines are spaces, so inner choices are
// moot).
//
// Not implemented (yet, intentionally):
//   - flatAlt / alignment / column-relative layouts.  Adding them later is
//     mechanical; we don't need them for proof terms or LF expressions.
//   - efficient sharing of subdocs — `Doc` is a tree, not a DAG.  Fine for
//     our scale (~hundreds of nodes per term).

export type Doc =
  | { kind: "nil" }
  | { kind: "text"; s: string }
  | { kind: "line" }
  | { kind: "nest"; n: number; d: Doc }
  | { kind: "concat"; ds: Doc[] }
  | { kind: "group"; d: Doc };

export const nil: Doc = { kind: "nil" };
export const line: Doc = { kind: "line" };

export function text(s: string): Doc {
  if (s.includes("\n")) {
    throw new Error(`pp.text: argument may not contain a newline: ${JSON.stringify(s)}`);
  }
  return { kind: "text", s };
}

export function nest(n: number, d: Doc): Doc {
  return { kind: "nest", n, d };
}

export function concat(...ds: Doc[]): Doc {
  return { kind: "concat", ds };
}

export function group(d: Doc): Doc {
  return { kind: "group", d };
}

// Convenience: like `concat`, but interleave a `sep` between each doc.  No
// effect on a singleton list.  Equivalent to (d1, sep, d2, sep, d3, ...).
export function sepBy(sep: Doc, ds: Doc[]): Doc {
  const acc: Doc[] = [];
  let first = true;
  for (const d of ds) {
    if (!first) acc.push(sep);
    acc.push(d);
    first = false;
  }
  return concat(...acc);
}

type Mode = "flat" | "break";
type Frame = { indent: number; mode: Mode; doc: Doc };

// Greedy fits-check: walk a stack of frames as if at the current column,
// counting flat-mode text/lines against `remaining`.  Return true if the
// first real newline (a `line` in break mode) is reached before remaining
// goes negative, or the stack drains.  Inner groups during the lookahead
// are assumed flat (the standard Wadler heuristic — checking every nested
// group's actual decision would be O(2^n)).
function fits(remaining: number, frames: readonly Frame[]): boolean {
  // Local stack so we don't mutate the caller's.
  const stack: Frame[] = [...frames];
  while (stack.length > 0 && remaining >= 0) {
    const f = stack.pop()!;
    switch (f.doc.kind) {
      case "nil":
        break;
      case "text":
        remaining -= f.doc.s.length;
        break;
      case "line":
        if (f.mode === "flat") {
          remaining -= 1;
        } else {
          // Reached an actual break — the first line ends here.
          return true;
        }
        break;
      case "nest":
        stack.push({ indent: f.indent + f.doc.n, mode: f.mode, doc: f.doc.d });
        break;
      case "concat":
        // Push in reverse so the first child is on top of the stack.
        // (!: noUncheckedIndexedAccess — within bounds k is always defined.)
        for (let k = f.doc.ds.length - 1; k >= 0; k--) {
          stack.push({ indent: f.indent, mode: f.mode, doc: f.doc.ds[k]! });
        }
        break;
      case "group":
        // Greedy: assume inner groups go flat during the lookahead.
        stack.push({ indent: f.indent, mode: "flat", doc: f.doc.d });
        break;
    }
  }
  return remaining >= 0;
}

export function render(width: number, doc: Doc): string {
  const stack: Frame[] = [{ indent: 0, mode: "break", doc }];
  let col = 0;
  let out = "";
  while (stack.length > 0) {
    const f = stack.pop()!;
    switch (f.doc.kind) {
      case "nil":
        break;
      case "text":
        out += f.doc.s;
        col += f.doc.s.length;
        break;
      case "line":
        if (f.mode === "flat") {
          out += " ";
          col += 1;
        } else {
          out += "\n" + " ".repeat(f.indent);
          col = f.indent;
        }
        break;
      case "nest":
        stack.push({ indent: f.indent + f.doc.n, mode: f.mode, doc: f.doc.d });
        break;
      case "concat":
        for (let k = f.doc.ds.length - 1; k >= 0; k--) {
          stack.push({ indent: f.indent, mode: f.mode, doc: f.doc.ds[k]! });
        }
        break;
      case "group": {
        if (f.mode === "flat") {
          // Inherited flat — inner stays flat too; no decision.
          stack.push({ indent: f.indent, mode: "flat", doc: f.doc.d });
        } else {
          // Look ahead: does the flat layout fit through the next real
          // newline?  If so, commit to flat; else, render broken and let
          // inner groups make their own decisions.
          const flatFrame: Frame = { indent: f.indent, mode: "flat", doc: f.doc.d };
          if (fits(width - col, [...stack, flatFrame])) {
            stack.push(flatFrame);
          } else {
            stack.push({ indent: f.indent, mode: "break", doc: f.doc.d });
          }
        }
        break;
      }
    }
  }
  return out;
}
