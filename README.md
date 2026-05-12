# Lean-to-LF Kernel Checker — Summary Report

A prototype that translates Lean 4 declarations (via lean4export NDJSON)
into Twelf LF signatures and checks them. The goal is faithfulness to
Lean's kernel, not performance; the test corpus is the
[arena.lean-lang.org tutorial](https://arena.lean-lang.org) — 86
declarations Lean's kernel accepts and 40 it rejects.

## Approach

Three layers, with explicit trust boundaries between them:

1. **Trusted core** (`lean-core-v2.elf`, ~620 lines). The LF signature
   for Lean's kernel — universe levels with an extrinsic `leq` judgement,
   the typing relation `of : exp -> exp -> type`, the definitional
   equality relation `defeq`, plus a small set of canonical bindings
   for `Nat` and `String` literal typing. This is the trust base.

2. **Translator** (`lean2lf-v2.ts`, ~1900 lines). Reads NDJSON, emits
   LF. Per Lean declaration it emits a `name` atom, a `decl` env-fact,
   and (for definitions/theorems/opaques) a deferred `check/n_X`
   derivation that discharges the typing obligation. When the
   translator's derivation engine can't build a check, it falls back
   to an axiom and records the fact in a per-file trust ledger.

3. **Trust ledger** — emitted as a comment block at the end of every
   translated file (`% TRUST_FIELD axioms_added: N`, `axiom_names: ...`).
   The harness reads this to classify each test as one of
   `verified` / `partial` / `twelf_fail` / `translator_fail`.

## Current numbers

```
                  GOOD (86)   BAD (40)
  verified           11           1   (← soundness violations)
  partial            42          30
  twelf_fail         33           9
  translator_fail     0           0
```

**`verified`** = Twelf OK, zero axioms emitted, zero translation errors.
The of-claim for every Lean declaration in the file is discharged by a
Twelf-checkable proof term against the trusted core.

**`partial`** = Twelf OK, but the file emits at least one new axiom
(or the translator hit a recoverable error). "Partially verified" —
some claims discharged, some asserted.

**`twelf_fail`** = Twelf rejected the file (typing mismatch or other
LF-level error).

**`translator_fail`** = translator never reached end of input.

## The 11 fully-verified good cases

These exercise the kernel's pure-level-arithmetic and pure-dependent-type
machinery without touching any user inductive. Every claim is discharged
by a Twelf proof term against the trusted core:

- `001_basicDef` — `Prop : Type`
- `003_arrowType` — `Type → Type : Type 1`
- `004_dependentType` — `(α : Type) → α → α : Type 1`
- `005_constType` — `Prop : Type`
- `012_levelComp1`, `013_levelComp2`, `014_levelComp3` — `imax`/`max` arithmetic
- `017_levelComp4`, `018_levelComp5` — polymorphic universe parameters
- `021_inferVar` — `(α : Type) → α → α` (variant)
- `026_letType` — `let` bindings on sorts

This is the honest core. Every other passing case relies on at least
one axiom the translator emitted (typically: a Lean inductive's
declaration, a recursor's ι-rule, or a punted body check).

## What's in the trust ledger

For each translated file, we count axioms emitted in these categories:

| Category | Example | When added |
|---|---|---|
| `decl/n_X:ax` | `decl/n_1_Bool : decl ... ax` | One per Lean axiom, inductive type, constructor, recursor, or `Quot.ind` |
| `deq/<rec>__<ctor>` | `deq/n_4_Bool_rec__n_2_Bool_false` | One per Lean ι-reduction rule (recursor on constructor) |
| `c_proj_X_Y` | `c_proj_1_0` | One per distinct projection stub introduced |
| `check/n_X` | `check/n_12_And_left` | Body-typing fell back to axiom (engine punted) |
| `prop/n_X` | `prop/n_12_And_left` | Theorem's `T : Prop` premise fell back to axiom |

Not counted (treated as hypothesis-input or trusted-core):

- `n_X : name` — pure atom introduction
- `decl/n_X` with `defn`/`thm`/`opq` payload — env-fact hypothesis from Lean
- `of/lit/Nat`, `of/lit/Str` in the trusted core
- Canonical `n_Nat`, `n_String` in the trusted core

## What's in the trusted core

The trusted core is `lean-core-v2.elf`. It encodes:

- **Universe levels** (`level`, `lz`, `ls`, `lmax`, `limax`) with an
  extrinsic equivalence-shaped `leq` judgement and ~20 axioms for
  universe-arithmetic laws (Sort hierarchy, max/imax monotonicity,
  successor-collapse rules).
- **Expression syntax** (`exp` with `univ`, `pi`, `lam`, `app`, `letx`,
  `natLit`, `strLit`).
- **Declaration names** (`name`, `lvls`, `const`) — mirroring Lean's
  `Expr.const : Name → List Level → Expr`.
- **Environment facts** — a single family `decl : name → lvls → exp → dkind → type`
  with four payload kinds (`defn`, `thm`, `opq`, `ax`).
- **Typing rules** (`of/univ`, `of/pi`, `of/lam`, `of/app`, `of/let`,
  `of/conv`) plus four `of/<kind>` rules dispatching on `decl` payload.
  Notably `of/thm` requires `of T (univ lz)` as an additional premise —
  the Lean kernel obligation that theorems have propositional types.
- **Definitional equality** (`defeq`) with reflexivity, symmetry,
  transitivity, β, η, congruence rules, plus `deq/delta` (δ-unfolding,
  restricted by signature to `defn` payloads only).
- **Kernel primitives** for `False`, `Eq`, `PSigma`, `Iff`, `Nonempty`,
  `Acc`, `Quot`, `propext`, `Classical.choice`, with their ι-rules
  in the core.
- **Canonical names and literal typing rules** for `Nat` and `String`.

## Successes

- **Soundness violations reduced from 23 to 1.** The starting state
  (before introducing the trust ledger) had every bad test silently
  classified as "OK" by Twelf. The current state distinguishes
  *which* bad tests are honestly rejected vs. honestly axiomatized
  vs. silently mistranslated. Only one bad test (`120_dup_defs`)
  remains a silent verification, and it's a known-problem case
  requiring Twelf-level capabilities (functional dependency on
  type families).

- **The Lean kernel's theorem-Prop side-condition is encoded structurally.**
  Splitting `decl` into kind-specific payloads (`defn`/`thm`/`opq`/`ax`)
  and requiring `of T (univ lz)` as a premise of `of/thm` means the
  obligation lives in the signature, not as a translator convention.
  The first bad test (`011_nonPropThm`) moved from silent verification
  to honest axiom-fallback on a kernel obligation we can't yet discharge.

- **Honest counting of axioms per file.** The trust ledger gives a
  concrete per-file picture: e.g., `093_aNatLit` partial because it
  introduces `Nat`'s three members and two ι-rules as axioms.
  `074_And.right` partial because it introduces `And`'s three members,
  one ι-rule, two projection stubs, two body-checks, and two prop-checks
  as axioms. The picture is honest about exactly what we're trusting.

- **Surgical Phase A level-normalization engine** lifts ~5 cases to
  `verified` that would otherwise fail Twelf on inferred-vs-declared
  universe mismatches. Outermost-only, with `of/conv` wrapping
  scoped tightly to the declaration body. No Twelf-side loop risk.

- **`%solve` as a constraint-discharge pattern.** The `of/lit/Nat`
  rule carries an `N >= 0` premise, discharged at each use site by
  a per-literal `%solve nat_geq_N : N >= 0.` declaration. Twelf's
  integer constraint domain certifies non-negative literals
  authoritatively (and rejects negative ones with "No solution to
  %solve found" — a semantic, not lexical, rejection). This is the
  template for any future side condition we want to encode: signature
  carries the premise, translator emits a per-use `%solve` witness,
  Twelf's solver decides.

- **Unified `decl`/`dkind` env-fact representation** with a documented
  functional-dependency invariant (which Twelf can't enforce).
  Each Lean declaration emits exactly one `decl/n_X` entry; per-kind
  obligations are routed via per-kind `of/<kind>` rules.

- **`Nat` and `String` literal rules pinned to canonical names in the
  trusted core**, instead of emitted per-file. Removes one axiom per
  Nat- or String-touching file.

## Shortcomings

### Soundness

- **`120_dup_defs` slips through silently.** Two `def dup_defs`
  declarations both translate to `n_1_dup_defs : name` plus `decl/n_1_dup_defs : ...`,
  and Twelf accepts both because LF has no functional-dependency
  constraint on type families. The signature comment documents this as
  a known limitation; the cluster of 7 `dup_*` bad tests are blocked
  on the same gap.

- **Inductive validity is unchecked.** 14 bad tests cover non-sort
  inductives, wrong constructor parameters, non-strict positivity,
  level-correctness violations, etc. We translate every inductive
  member to `decl/n_X` with an `ax` payload — but `ax` admits any
  type, so we accept all of them. These cases currently land in
  `partial` (because the inductive's members count as axioms), so
  they're not soundness violations under the current taxonomy, but
  the trust ledger could be tightened: a `decl/n_X:ax` whose
  *declared type* doesn't pass an inductive-validity check is worse
  than one that does.

- **Out-of-bounds projection indices** emit fresh untyped `c_proj_X_999`
  stubs without bounds-checking. Currently classified `partial`
  because the body-check punts on the bad stub, but the honesty is
  contingent on the engine being incomplete — once we add proj
  derivation, this becomes a potential silent-verification path.
  Translator should reject.

### Engine reach

33 good tests fail at the Twelf level. Loosely:

- **Inner-level conversion** (~6 cases): the level-normalization engine
  fires only at the outermost `of/conv` site. Inner conversions
  (e.g. inside a `pi` body) need a generalization.
- **Recursor reduction** (~8 cases): the engine doesn't build
  derivations that reduce recursor applications. The ι-rules are
  present in the signature but unused at the proof-term level.
- **Projection reduction** (~4 cases): same shape — emitted as axioms,
  not used in derivations.
- **Eta/proof-irrelevance** (~8 cases): not implemented.
- **Other** (~7): peano arithmetic specifically, `propext` reasoning,
  RBTree.id_spec, etc.

The pattern is the same in all these: the *signature* has the rule,
but the *engine* doesn't construct proofs that use it. Each category
is a distinct project of comparable size to the Phase A level engine.

### Architecture

- **Trust counting is binary per file.** A file with 1 axiom and a
  file with 30 are both `partial`. The summary tells us nothing about
  the size of the trust footprint. A weighted classification (counting
  axiom *categories*, e.g. "5 ι-rules, 2 inductive members") would
  give a more granular progress metric.

- **The translator's derivation engine is monolithic.** `deriveOf`
  handles every Lean Expr kind in one function. Adding new derivation
  modes (recursor reduction, projection reduction, eta) means extending
  one function; a cleaner separation by reduction mode would scale
  better.

- **No validation pass.** Translator-side checks (duplicate level
  params, bvar-in-range, etc.) are scattered through `trExpr`,
  `buildLvlCtx`, etc. A separate `validateLeanInput()` running per
  NDJSON line, before any translation, would centralize them. We're
  not there yet; checks are added ad-hoc as cases surface.

## Next steps

### Cheap (an afternoon each)

1. **Validate projection indices against inductive field count.**
   Requires tracking inductive structure (number of fields) per
   `nameIdx`. Small but new bookkeeping.
2. **Extend `levelOfType` to handle `App` heads.** Would let the
   prop-check engine fire for cases like `And.right` (currently
   axiomatized because the engine can't infer the level of an
   `App` head). Likely moves a handful of partial → verified.

### Structural refactor candidates

These don't fall neatly into size buckets because their cost is mostly
the migration itself rather than new logic, but each one would tighten
the architecture in a way that pays dividends downstream.

#### Replace `leq` with Mario's algorithmic `aleq`

The current `leq` family on universe levels is equivalence-shaped:
`leq/refl`, `leq/sym`, `leq/trans`, plus a dozen named lemmas. Because
`sym` and `trans` are obvious loop sources for backwards search, we
deliberately don't let Twelf search over `leq` — instead we built
`proveLeq` in TypeScript (Phase A, ~150 lines spanning a `Lvl`
discriminated union, `simplifyMax`, `lvlNorm`, and a witness-threading
walker). The signature has the rules; the engine that uses them lives
in the translator.

Mario Carneiro's algorithmic ≤ on Lean universe levels is a
structural-recursive relation: each rule fires on a distinct LHS
pattern, no `sym` or `trans`, and search is decidable via Twelf's
backwards chaining alone. The migration would move the level-leq
engine out of TypeScript and into Twelf's `%solve`, in the same
discharge pattern we use for the `N >= 0` premise on `of/lit/Nat`.

##### The proposed signature

```
aleq : level -> level -> type.

% Reflexivity.
aleq/refl     : aleq L L.

% Bottom.
aleq/lz       : aleq lz L.

% Successor.
aleq/sR       : aleq L1 L2 -> aleq L1 (ls L2).
aleq/ss       : aleq L1 L2 -> aleq (ls L1) (ls L2).

% Max splits / lifts.
aleq/maxL     : aleq L1a L2 -> aleq L1b L2 -> aleq (lmax L1a L1b) L2.
aleq/maxR_l   : aleq L1 L2a -> aleq L1 (lmax L2a L2b).
aleq/maxR_r   : aleq L1 L2b -> aleq L1 (lmax L2a L2b).

% imax reductions on the right: each rule matches a specific shape
% for the inner level.
aleq/imax_lz  : aleq L1 lz                        -> aleq L1 (limax L lz).
aleq/imax_ls  : aleq L1 (lmax L (ls L'))          -> aleq L1 (limax L (ls L')).
aleq/imax_mx  : aleq L1 (lmax (limax L A) (limax L B))
                -> aleq L1 (limax L (lmax A B)).
aleq/imax_im  : aleq L1 (lmax (limax L B) (limax A B))
                -> aleq L1 (limax L (limax A B)).

% imax reductions on the left: mirror.
aleq/imax_lzL : aleq lz L2                       -> aleq (limax L lz) L2.
aleq/imax_lsL : aleq (lmax L (ls L')) L2         -> aleq (limax L (ls L')) L2.
aleq/imax_mxL : aleq (lmax (limax L A) (limax L B)) L2
                -> aleq (limax L (lmax A B)) L2.
aleq/imax_imL : aleq (lmax (limax L B) (limax A B)) L2
                -> aleq (limax L (limax A B)) L2.

% Variable-position case on the left: a free var V in `limax L V`
% could be 0 (so imax = 0) or non-zero (so imax = max).  Either way,
% imax(L,V) ≤ max(L,V), so reducing the upper-bound goal to max is
% sound.  No analogous safe rule for the right-position variable case.
aleq/imax_vL  : aleq (lmax L V) L2 -> aleq (limax L V) L2.
```

Then `deq/univ : aleq L L' -> defeq (univ L) (univ L')`. Same change
to `of/ulift`. The translator stops calling `proveLeq` and instead
emits, per conversion site, a `%solve leq_<N> : aleq <inferred> <declared>.`
and references the resulting witness in the `of/conv` wrapping.

##### Empirical results

Probed all the cases Phase A currently handles, plus a stress set of
boundary patterns:

| Goal | Time | Witness |
|---|---|---|
| `aleq (limax (ls lz) (ls lz)) (ls lz)` | <10 ms | `aleq/imax_lsL (aleq/maxL aleq/refl aleq/refl)` |
| `{U} aleq (limax U U) U` | <10 ms | `[U] aleq/imax_vL (aleq/maxL aleq/refl aleq/refl)` |
| `{U}{V} aleq (lmax U V) (lmax V U)` | <10 ms | proves commutativity via the maxL/maxR rules |
| `{U}{V} aleq (limax U (lmax V (ls V))) (lmax U (lmax V (ls V)))` | <10 ms | proves the harder nested case |
| Negative: `aleq (ls lz) lz` | <10 ms | `No solution to %solve found` |
| Negative: `{U} aleq (limax U U) lz` | <10 ms | `No solution to %solve found` |

Total stress test of 8 polymorphic cases: 43 ms. Per-witness overhead
is well below the per-file Twelf invocation cost.

##### Soundness check on `aleq/imax_vL`

The rule overconstrains in the direction that's safe. `limax L V ≤ X`
is the goal; the rule reduces it to `lmax L V ≤ X`. Lean's semantics
say `limax(L, V) = if V = 0 then 0 else max(L, V)`. So `limax L V ≤ max L V`
holds always (when `V = 0`, LHS is 0; when `V ≠ 0`, both sides equal
`max L V`). Reducing the goal from "≤ X for `limax L V`" to "≤ X for
`max L V`" therefore demands a strictly stronger property. We use
`aleq` only to construct positive witnesses for conversion, never to
*disprove* a level inequality, so the conservative direction is what
we want.

The dual rule on the right would be unsound (`L1 ≤ max(L,V)` doesn't
imply `L1 ≤ limax(L, V)` when `V = 0`), and is correctly absent from
the proposed signature.

##### Cost of migration

- Signature: ~30 lines added (`aleq` family + var-case rule), ~14
  lines removed (`leq/refl`, `leq/sym`, `leq/trans`, the named lemmas).
- Translator: ~150 lines deleted. The discriminated union `Lvl`, the
  walkers `lvlAst`/`lvlEq`/`simplifyMax`/`lvlNorm`, and `proveLeq`
  itself all go. `levelOfType` / `levelOfBinder` stay (we still need
  to compute the inferred level to pass to `%solve`).
- Two trusted-core sites updated: `deq/univ` and `of/ulift`.

##### Open questions before committing

1. **Does `aleq/refl` interact safely with the full harness?** Tested
   cases don't loop, but the absence of `sym` and `trans` is what
   keeps refl safe. Any future rule of the shape `aleq A B → aleq A B'`
   with `B ≠ B'` would need re-auditing.
2. **Migration approach.** Cleanest path is to add `aleq` alongside
   `leq` as a parallel signature, prove out the new translator path
   under it, and switch over once stable. Avoids a single big-bang
   change.

##### Why this fits the "%solve template"

The earlier `of/lit/Nat` change established a pattern: kernel-side
side condition encoded in the signature, translator emits a `%solve`
witness per use site, Twelf's search decides. The `aleq` migration
applies the same template at much larger scale — every level
conversion in every Lean declaration becomes a `%solve` invocation,
replacing the entire TS-side proof-construction engine. If it holds,
the architectural reading is "Twelf is now responsible for level
reasoning, the translator is responsible for declaration-shape
translation," with a clean trust seam between them.

### Medium (a week each)

3. **Inner-level conversion.** Generalize Phase A to apply at every
   `of/conv` site, not just outermost. Could lift ~6 twelf_fail to
   verified or partial-with-fewer-axioms.
4. **Recursor reduction engine.** Build derivations that use the
   emitted ι-rules. Likely the highest-impact single addition —
   would also unblock several other categories indirectly.
5. **Inductive validity layer 1+2.** Encode "stated type is a sort"
   and "constructor result type matches parameters" as signature-side
   premises. Moves ~5 of the 14 inductive-validity bad tests from
   `partial` to `twelf_fail`, tightening the trust statement on
   well-formed inductives.

### Large

6. **Strict positivity check.** ~6 bad tests test pathological
   inductives (negative occurrences, occurrences in indices, reducible
   ctors). A real positivity algorithm walks every constructor's
   argument types — substantial engineering, comparable in size to
   the Phase A engine.

### Out of scope (Twelf-side)

7. **Functional dependency on type families.** Would let us catch
   `120_dup_defs` and the `dup_*` cluster soundly at the LF level.
   Requires changes to Twelf itself — checking that a type family
   with declared functional-dependency annotations has no duplicate
   instances.
8. **Selective `%freeze`.** Lock `exp` and `of` while leaving `name`
   open for extension. Appel and Felty's `proving` development hit
   the same wall; same fix would help here.

## Project artifacts

- `lean-core-v2.elf.txt` — trusted core LF signature (~620 lines)
- `lean2lf-v2.ts` — translator (~1900 lines)
- `run-tut4-trust.sh` — classifying harness
- `tut4-good-trust.txt`, `tut4-bad-trust.txt` — current per-test results
- `v2-toolchain-bundle.tgz`, `v2-setup.sh` — reproducer for the toolchain
  (libgmp + tut4 test bundle + zod stub for the offline environment)
- `twelf-server` — prebuilt Twelf binary used by the harness