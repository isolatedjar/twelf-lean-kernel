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

#### Replace Phase A with Mario Carneiro's algorithmic level inequality

The current `leq` family on universe levels is equivalence-shaped:
`leq/refl`, `leq/sym`, `leq/trans`, plus a dozen named lemmas. Because
`sym` and `trans` are obvious loop sources for backwards search, we
deliberately don't let Twelf search over `leq` — instead we built
`proveLeq` in TypeScript (Phase A, ~150 lines spanning a `Lvl`
discriminated union, `simplifyMax`, `lvlNorm`, and a witness-threading
walker). Phase A is incomplete: it handles outermost-only conversions
and the level shapes that came up in the first batch of tutorial cases.

Mario Carneiro's "The Type Theory of Lean" (2019) gives an algorithmic
inference-rule system for level inequality on page 7. The relation is
`ℓ ≤ ℓ' + n` where `n ∈ ℤ` is an integer offset, with `ℓ ≤ ℓ'`
abbreviating `ℓ ≤ ℓ' + 0`. The rules are structural, with each rule
firing on a distinct LHS pattern — well-suited for Twelf's backwards
chaining via `%solve`. (Note: this is the *thesis* algorithm, which is
inference-rule shaped. Lean4Lean's `VLevel.LE` in
`Lean4Lean/Theory/VLevel.lean` is a different, semantic definition
based on universal quantification over valuations, which isn't
directly searchable by Twelf.)

##### Mario's algorithmic relation (page 7 of the thesis)

```
ℓ ≡ ℓ'             n ≥ 0          n ≥ 0
─────  ───────     ────────       ────────
ℓ ≤ ℓ' ℓ' ≤ ℓ      0 ≤ ℓ + n      ℓ ≤ ℓ + n

ℓ ≤ ℓ' + (n-1)     ℓ ≤ ℓ' + (n+1)
──────────         ──────────────
Sℓ ≤ ℓ' + n        ℓ ≤ Sℓ' + n

ℓ ≤ ℓ₁ + n            ℓ ≤ ℓ₂ + n           ℓ₁ ≤ ℓ + n  ℓ₂ ≤ ℓ + n
───────────────       ───────────────      ──────────────────────
ℓ ≤ max(ℓ₁,ℓ₂) + n    ℓ ≤ max(ℓ₁,ℓ₂) + n   max(ℓ₁,ℓ₂) ≤ ℓ + n

0 ≤ ℓ + n              max(ℓ₁, Sℓ₂) ≤ ℓ + n
──────────────────     ─────────────────────
imax(ℓ₁, 0) ≤ ℓ + n    imax(ℓ₁, Sℓ₂) ≤ ℓ + n

max(imax(ℓ₁,ℓ₃), imax(ℓ₂,ℓ₃)) ≤ ℓ + n
─────────────────────────────────────
imax(ℓ₁, imax(ℓ₂,ℓ₃)) ≤ ℓ + n

ℓ ≤ max(imax(ℓ₁,ℓ₃), imax(ℓ₂,ℓ₃)) + n
─────────────────────────────────────
ℓ ≤ imax(ℓ₁, imax(ℓ₂,ℓ₃)) + n

max(imax(ℓ₁,ℓ₂), imax(ℓ₁,ℓ₃)) ≤ ℓ + n
─────────────────────────────────────
imax(ℓ₁, max(ℓ₂,ℓ₃)) ≤ ℓ + n

ℓ ≤ max(imax(ℓ₁,ℓ₂), imax(ℓ₁,ℓ₃)) + n
─────────────────────────────────────
ℓ ≤ imax(ℓ₁, max(ℓ₂,ℓ₃)) + n

ℓ[0/u] ≤ ℓ'[0/u] + n    ℓ[Su/u] ≤ ℓ'[Su/u] + n
─────────────────────────────────────────────
ℓ ≤ ℓ' + n                            (variable elimination)
```

##### Empirical results: transcription of the non-variable-elim rules

Transcribing the first thirteen rules into Twelf using the integer
constraint domain for the offset:

```
mleq : level -> level -> integer -> type.

mleq/lz       : N >= 0 -> mleq lz L N.
mleq/self     : N >= 0 -> mleq L L N.
mleq/sL       : mleq L L' (N - 1) -> mleq (ls L) L' N.
mleq/sR       : mleq L L' (N + 1) -> mleq L (ls L') N.
mleq/maxR_l   : mleq L L1 N -> mleq L (lmax L1 L2) N.
mleq/maxR_r   : mleq L L2 N -> mleq L (lmax L1 L2) N.
mleq/maxL     : mleq L1 L N -> mleq L2 L N -> mleq (lmax L1 L2) L N.
mleq/imax_lzL : mleq lz L N -> mleq (limax L1 lz) L N.
mleq/imax_lsL : mleq (lmax L1 (ls L2)) L N -> mleq (limax L1 (ls L2)) L N.
mleq/imax_imL : mleq (lmax (limax L1 L3) (limax L2 L3)) L N
                  -> mleq (limax L1 (limax L2 L3)) L N.
mleq/imax_imR : mleq L (lmax (limax L1 L3) (limax L2 L3)) N
                  -> mleq L (limax L1 (limax L2 L3)) N.
mleq/imax_mxL : mleq (lmax (limax L1 L2) (limax L1 L3)) L N
                  -> mleq (limax L1 (lmax L2 L3)) L N.
mleq/imax_mxR : mleq L (lmax (limax L1 L2) (limax L1 L3)) N
                  -> mleq L (limax L1 (lmax L2 L3)) N.
```

Probed `%solve` results:

| Goal | Time | Result |
|---|---|---|
| `mleq (lz (ls (ls (ls lz)))) (ls (ls (ls (ls (ls lz))))) 0` (3 ≤ 5) | <10 ms | witness |
| `mleq (lis^5 lz) (ls^3 lz) 2` (5 ≤ 3+2) | <10 ms | witness |
| `mleq (limax (ls lz) (ls lz)) (ls lz) 0` (003-style) | <10 ms | witness |
| `mleq (limax (limax ..) (limax ..)) (ls lz) 0` (014-style nested) | <10 ms | witness |
| `mleq (ls lz) lz 0` (1 ≤ 0, false) | <10 ms | `No solution to %solve found` |

All five queries together: 29 ms. Polymorphic queries that don't need
variable elimination (commutativity, idempotency, max-zero collapse,
mixed imax/lmax/ls) also work via the structural rules alone:

| Goal | Time | Result |
|---|---|---|
| `{U} mleq U U 0` | <10 ms | via mleq/self |
| `{U} mleq lz U 0` | <10 ms | via mleq/lz |
| `{U} mleq U (ls U) 0` | <10 ms | via mleq/sR |
| `{U}{V} mleq U (lmax U V) 0` | <10 ms | via mleq/maxR_l |
| `{U}{V} mleq (lmax U V) (lmax V U) 0` (commutativity) | <10 ms | witness |

Negative direction `{U} mleq (limax U U) lz 0` correctly fails.

##### The variable-elimination rule is the sticking point

Mario's fourteenth rule case-splits on a universe parameter:

```
ℓ[0/u] ≤ ℓ'[0/u] + n    ℓ[Su/u] ≤ ℓ'[Su/u] + n
─────────────────────────────────────────────
ℓ ≤ ℓ' + n
```

This is what makes the algorithm complete for cases like
`{U} mleq (limax U U) U 0` — where `imax`'s second argument is a
free universe variable, no structural rule applies, but the
substitution-and-recurse pattern resolves it (when `U = 0`,
`imax U 0 = 0 ≤ 0`; when `U = Su'`, `imax U (Su') = max U (Su') ≤ U`
which the structural rules can handle).

Direct transcription using higher-order Twelf abstraction:

```
mleq/var : mleq (L lz) (L' lz) N
        -> ({u:level} mleq (L (ls u)) (L' (ls u)) N)
        -> mleq (L U) (L' U) N.
```

Loops in Twelf's search (30-second timeout). The pattern variables
`L, L' : level -> level` unify with any goal by setting
`L := λ_. <current goal>`, recursing forever. This is a known issue
with higher-order Twelf patterns whose hole isn't constrained to be
used in the body.

##### Three architectural options going forward

**A. Mario's algorithm minus variable-elim, used directly via %solve.**
Decides closed levels and polymorphic levels that don't need
variable elimination. The empirical evidence from the current test
suite suggests most level reasoning falls in the latter category —
the cases Phase A currently handles, plus many more (commutativity,
non-trivially-nested max/imax). Cases that *do* need variable
elimination correctly fail to find a witness. Conservative; the trust
seam is "Twelf for the relation, search for the proof."

**B. Hybrid: Twelf for structural cases, TypeScript for variable
elimination.** The translator detects when a goal contains an `imax`
whose RHS is a free universe variable, performs the case-split in
TypeScript (substituting `lz` and `(ls u')`), and invokes `%solve`
on both branches separately. Recombines the witnesses via a meta-rule
in the signature (one new `mleq/var-discharge` axiom). This is the
"%solve template" applied at scale, with the one structurally
hard rule lifted into TS. Larger TS surface than Option A, but
materially complete relative to Mario's algorithm.

**C. Explicit level-variable substitution in the signature.**
Introduce a separate sort `lvar` for level variables, with a
`lsubst : level -> lvar -> level -> level` operation that's a
first-class part of the level algebra. Then the variable-elimination
rule can be written without higher-order patterns. Substantial
restructuring of the level encoding throughout the signature —
`deq/univ`, `of/ulift`, all the `of/pi`/`of/lam` level uses would
need to thread through level variables explicitly. Most invasive.

##### Recommendation

**Option B (hybrid).** Mario's thirteen structural rules in Twelf
handle the algorithmic backbone, with a TypeScript hook for the
variable-elimination case. The TS hook is small — it detects
"goal has `imax _ U` for free `U`", substitutes both branches, and
emits two `%solve` directives. The variable-elimination case is
rare in practice (most universe arithmetic doesn't actually need it,
as the empirical results show), so the hook firing is the exception
rather than the rule.

Cost estimate:
- Signature: ~30 lines (the thirteen `mleq` rules) plus a
  `mleq/var-discharge` axiom for recombining the TS-handled cases.
  Update `deq/univ` and `of/ulift` to use `mleq L L' 0` instead
  of `leq L L'`.
- Translator: ~80 lines for the variable-elim detector and case-split
  emitter, plus retirement of Phase A's `proveLeq`/`simplifyMax`/
  `lvlNorm` (~150 lines).
- Net: ~70 lines deleted, plus an architectural simplification.

##### Open questions

1. **Does Mario's algorithm with the variable rule strictly subsume
   Phase A on the current test suite?** Empirically yes for the closed
   and most polymorphic cases; the variable rule fires only on
   `imax _ U` patterns for free `U`, which we should grep the tutorial
   corpus to find.
2. **What's the right shape for the `mleq/var-discharge` axiom?**
   Something like
   `mleq L0 L'0 N -> ({u} mleq L1 L'1 N) -> mleq L L' N`
   where `L, L', L0, L'0, L1, L'1` are concrete (not higher-order)
   levels passed in from TS, with the relationship between them being
   the substitution that TS performs. This makes the rule a no-op for
   Twelf search (it never fires on its own) but a usable hook for the
   translator.

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