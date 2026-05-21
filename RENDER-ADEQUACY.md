# Render Adequacy

**Status:** design rule. Current implementation does **not** fully comply — see "Gap" below.

## The rule

The `.render.elf` view of a Lean environment is the canonical "moral Twelf"
representation. It must be **informationally adequate**: every fact in the
input NDJSON that is needed to reconstruct the `.full.elf` proof obligations
must appear in `.render.elf` as Twelf-LF data (declarations, constants,
sub-terms), not solely in comments.

Concretely:

> A reader who strips every comment from `foo.render.elf` and parses the
> remaining Twelf-LF text must be able to recover the exact `ParsedEnv` that
> `parse.ts` produced from `foo.ndjson`. Equivalently: `lean2lf.ts` could in
> principle take `foo.render.elf` (comments stripped) as its input and emit
> a byte-equivalent `foo.full.elf` — with no recourse to the NDJSON or to
> the intermediate JSON IR.

Comments may add diagnostic context (kind banners, counts, descriptions) but
are **not load-bearing**. The Twelf-LF declarations alone must carry every
load-bearing piece of information.

## Why this matters

1. **Audit story.** The "moral Twelf" pitch is that a reviewer can verify
   the encoding by reading `render.ts` plus a `.render.elf` file. If
   `.render.elf` is missing the declaration's kind, parent inductive,
   `numParams`, etc., that audit is incomplete: the reviewer is implicitly
   trusting the JSON IR and the comments.

2. **Round-trip as a regression test.** Once adequacy holds, we can write a
   round-trip test: NDJSON → `.render.elf` → reconstructed IR → `.full.elf`
   that compares byte-for-byte against the direct pipeline. Any drift fails
   the test immediately.

3. **Versioning.** When the TCB or the translator changes, `.render.elf`
   becomes the durable source of truth for what was encoded; `.full.elf` is
   regenerated from it. Without adequacy, the NDJSON remains a hidden
   dependency.

## Required content per declaration

For each declaration the renderer emits, the following data must be
LF-visible (not just commented):

| Declaration kind  | Required LF-visible fields                                                                            |
| ----------------- | ----------------------------------------------------------------------------------------------------- |
| `def` / `thm` / `opaque` | name, level-param names (with their original Lean names), type, value, kind                    |
| `axiom`           | name, level-param names, type                                                                         |
| `quot`            | the marker (so the consumer knows a quot block was declared)                                          |
| inductive type    | name, level-param names, type, `numParams`, `numIndices`                                              |
| inductive ctor    | name, parent inductive name, level-param names, type, `numParams`, `numFields`                        |
| inductive recursor| name, level-param names, type, `numParams`, `numIndices`, `numMotives`, `numMinors`, `k`, rec-rules   |
| inductive rec-rule| ctor name, `nfields`, rhs                                                                             |

Comments may *also* mention any of these (for skimmability), but the LF text
must carry them independently.

## Recommended encoding

A clean way to satisfy the rule is a "raw declaration record" family in a
new `lf/render-meta.elf` that `.render.elf` files load alongside `tcb.elf`:

```twelf
%% Sketch (not the final API):
raw-decl : type.

raw-def     : name -> name-list -> expr -> expr -> raw-decl.
raw-thm     : name -> name-list -> expr -> expr -> raw-decl.
raw-opaque  : name -> name-list -> expr -> expr -> raw-decl.
raw-axiom   : name -> name-list -> expr             -> raw-decl.
raw-quot    :                                          raw-decl.
raw-indt    : name -> name-list -> expr -> integer -> integer -> raw-decl.
raw-ctor    : name -> name -> name-list -> expr -> integer -> integer -> raw-decl.
raw-irec    : name -> name-list -> expr -> rec-meta -> rec-rules -> raw-decl.
```

Then `render-cli.ts` emits one such constant per declaration, e.g.:

```twelf
foo/raw : raw-decl =
  raw-def "foo" (nlcons "u" nlnil) <T-with-u-bound> <V-with-u-bound>.
```

The level-param names list (`name-list`) preserves the original Lean param
names, so the reconstructor can reconstitute the `levelParams: Name[]` field
of `Decl`. The type/value expressions still HOAS-bind those params via
`{u : lvl} ... [u] ...`.

## Gap (today)

`render-cli.ts` emits only `foo/render-type` and `foo/render-value` bindings
keyed by mangled identifiers. The declaration's **kind**, **parent
inductive**, **numParams / numIndices / numFields / numMotives / numMinors
/ k**, and the **identity of each rec-rule's ctor** live only in
`%% ...` comments. As an example, see
`lf/tests/124_dup_rec_def2.render.elf`: it shows that a `dup_rec_def2.rec`
binding exists at level zero and that a `dup_rec_def2.original_rec`
recursor exists, but Twelf-LF data alone cannot tell you which is the
recursor and which is the conflicting `def`. Without that, downstream
checks (e.g. duplicate-name detection across kinds) cannot run from the
`.render.elf` alone.

## Effort to enforce end-to-end

Two pieces:

1. **Make `.render.elf` complete** — implement the encoding above.
   - `lf/render-meta.elf`: ~50 lines of LF declarations (raw-decl family +
     supporting list types).
   - `src/render-cli.ts`: emit one `<name>/raw : raw-decl = ...` constant
     per declaration; keep existing `/render-type` and `/render-value`
     bindings for backward-compatible auditability (or drop them).
   - **~0.5–1 day of focused work**.

2. **Reverse path: `.render.elf` → IR → `.full.elf`** — needed to *prove*
   adequacy by running `lean2lf.ts` on the reconstructed input.
   - Write a Twelf-LF subset parser in TypeScript (constants, declarations,
     Π / λ binders, applications, the string/integer constraint domains).
     ~500–1000 lines of TS. **3–5 days**.
   - Reverse-mapping from raw-decl LF terms back to `Decl` IR
     (re-inflating Names, levelParams, the HOAS lambda layer). **1–2 days**.
   - Integration: a new entry point that reads `.render.elf` and calls into
     `lean2lf.ts`'s existing emit pipeline; plus a round-trip check in
     `scripts/check-tests.sh` (byte-compare against the direct pipeline).
     **1–2 days**.
   - Testing, edge cases (unusual Lean names, escape sequences, very deep
     binders), Twelf-comment handling. **2–3 days**.
   - **Total: roughly 1.5–2 weeks of focused work**.

The cheap part (1) closes the adequacy gap as a property of the artifacts;
the expensive part (2) turns adequacy from a property we trust into a
property we test.

## Maintaining the rule

When adding or changing any code that emits to `.render.elf`:

- [ ] Every load-bearing field listed under "Required content per
      declaration" must appear in the emitted LF text — not only in a
      `%% ...` comment.
- [ ] If a new declaration kind or IR field is added, extend
      `lf/render-meta.elf` and update this document's table accordingly.
- [ ] If you must add a comment that carries semantic information (rather
      than just diagnostics), reconsider: that's evidence the LF schema is
      incomplete.
- [ ] Spot-check a representative output (e.g. `124_dup_rec_def2.render.elf`,
      which has duplicate names across kinds) and confirm a comment-blind
      reader could distinguish each declaration's kind.
