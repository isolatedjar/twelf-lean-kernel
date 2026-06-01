# TCB-completeness checklist

What this document is: a tick-box accounting of how much of Mario's
declarative specification of Lean's type theory our TCB encodes. The
specification is `VEnv.IsDefEq` (Figure 1 of the lean4lean paper, implemented
in `Lean4Lean/Theory/Typing/Basic.lean`) plus the inductive and quotient
extensions added via `t-extra`.

**What "TCB-complete" means here.** For every defeq fact that holds in Mario's
declarative relation, there exists an inhabitant of the corresponding LF type
in our signature. **Translator-completeness is a separate question**: given a
TCB-complete signature, can our translator find the witness? We are explicitly
OK with the translator failing to find proofs (it's a heuristic search), as
long as the witness exists for someone or something else — human, LLM,
decision procedure — to construct.

## 1. The core defeq judgment (paper Figure 1)

Mario's judgment is `Γ ⊢_{E,n} e ≡ e' : α`, with implicit reflexivity
(`Γ ⊢ e : α` defined as `Γ ⊢ e ≡ e : α`). We map this onto our
`defeq E1 E2 A`, treating the LF context as the typing context (each
`{x : expr} defeq x x A -> ...` binder corresponds to a `Γ, x : α` extension).

| Paper rule                                         | Our TCB                                                                                                                                                                                                                                                                                                                                                                                                                                      | Status                                                                                                        |
| -------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------- |
| `l-zero`, `l-succ`, `t-bvar`                       | LF context lookup; `defeq x x A` hypothesis introduced under each binder                                                                                                                                                                                                                                                                                                                                                                     | ✓ adequate by LF α-equivalence                                                                                |
| `t-symm`                                           | `defeq/symm`                                                                                                                                                                                                                                                                                                                                                                                                                                 | ✓                                                                                                             |
| `t-trans`                                          | `defeq/trans`                                                                                                                                                                                                                                                                                                                                                                                                                                | ✓                                                                                                             |
| `t-conv`                                           | `defeq/conv`                                                                                                                                                                                                                                                                                                                                                                                                                                 | ✓                                                                                                             |
| `t-sort`                                           | `defeq/sort-eq` (via `lvl-eq`)                                                                                                                                                                                                                                                                                                                                                                                                               | ✓ (modulo `lvl-eq` completeness — §2)                                                                         |
| `t-all`                                            | `defeq/forall`                                                                                                                                                                                                                                                                                                                                                                                                                               | ✓                                                                                                             |
| `t-lam`                                            | `defeq/lam`                                                                                                                                                                                                                                                                                                                                                                                                                                  | ✓                                                                                                             |
| `t-app`                                            | `defeq/app`                                                                                                                                                                                                                                                                                                                                                                                                                                  | ✓                                                                                                             |
| `t-beta`                                           | `defeq/beta`                                                                                                                                                                                                                                                                                                                                                                                                                                 | ✓                                                                                                             |
| `t-eta`                                            | `defeq/eta`                                                                                                                                                                                                                                                                                                                                                                                                                                  | ✓                                                                                                             |
| `t-const`                                          | `defeq/const` (via `declared`)                                                                                                                                                                                                                                                                                                                                                                                                               | **✗ partial — only same-level diagonal**                                                                      |
| `t-proof-irrel`                                    | `defeq/proof-irrel` (premise: `defeq P P (esort lzero)`, two proofs of `P` are defeq)                                                                                                                                                                                                                                                                                                                                                        | ✓                                                                                                             |
| `t-extra` (δ for `defn`)                           | `defeq/delta`                                                                                                                                                                                                                                                                                                                                                                                                                                | ✓                                                                                                             |
| `t-extra` (iota for recursors)                     | `defeq-extra` + `defeq/extra` + per-ctor-count enum rules (`defeq/iota-enum-{1,2,3}-{...}`) — **stage 1 only: enums with 1-3 ctors, no params, no recursive args.** Rules pattern-match on `declared` witnesses and `enum-rec-type` schema; no trust gap. Translator auto-detects iota redexes (`tryIotaEnum`) and emits witnesses via per-ctor `<ctor>/iota` helpers, with β-conv normalization of the type index when the motive is a lam. | **✓ stage 1** (Bool, Unit, three-ctor enums); end-to-end working as of test 069; ✗ stages 2+ (Nat, List, ...) |
| `t-extra` (structural eta for one-ctor inductives) | —                                                                                                                                                                                                                                                                                                                                                                                                                                            | **✗ missing entirely**                                                                                        |
| `t-extra` (Quot's primitive `lift∘mk` rule)        | —                                                                                                                                                                                                                                                                                                                                                                                                                                            | **✗ missing entirely**                                                                                        |

### 1.1 Detail on `t-const` partial coverage

Mario's full rule:

> Given `ū.(c_ū : α) ∈ E` and `∀i. n ⊢ ℓᵢ, ℓ'ᵢ ok ∧ ℓᵢ ≡ ℓ'ᵢ`, conclude
> `Γ ⊢ c_{ℓ̄} ≡ c_{ℓ̄'} : α[ū ↦ ℓ̄]`.

The `ℓᵢ ≡ ℓ'ᵢ` premise means the two instantiations can be different level
expressions, provided they're defeq as levels. Our `defeq/const`:

```
defeq/const :
   declared N LS T DK W
   -> defeq (econst N LS) (econst N LS) T.
```

handles only the `ℓᵢ = ℓ'ᵢ` diagonal (same `LS` on both sides). To get
`defeq (econst N LS) (econst N LS') T` for `lvls-eq LS LS'`, we'd need either:

- a new rule
  `defeq/const-lvl-cong : declared N LS T DK W -> lvls-eq LS LS' -> defeq (econst N LS) (econst N LS') T'`
  (where T' is T with LS substituted), or
- prove `lvls-eq` lifts through `defeq` via the structural congruence on
  `defeq` (probably not directly possible without the rule).

**Practical impact**: any time the same polymorphic constant appears with
provably-equal-but-not-syntactically-equal level args on two sides of a defeq,
we can't close the gap. Example: `id.{max u v} α` vs `id.{max v u} α` — these
are the same in Mario's spec but our TCB can't witness it.

### 1.2 Detail on the missing `t-extra` cases

Mario's `t-extra` is the catch-all environment-provided equality rule. Iota,
structural eta, and Quot's primitive rule are all added via `t-extra` in the
formalization. Each is a fixed family of equations parameterized by the
inductive declaration. In LF this becomes one rule per (inductive, applicable
operation) pair — there's no encoding-level obstacle, just bookkeeping (and a
coupling-to-defeq concern when the rule is supposed to fire modulo whnf).

Specifically:

- **Iota for `Foo.rec`**: one rule per `(Foo, ctor_k)` pair, of shape
  `defeq (Foo.rec ... (Foo.ctor_k a₁...aₘ)) <body-using-args> α`.
  Pattern-matching on the ctor head is standard LF.

- **Structural eta for one-ctor `Foo`**: one rule per such `Foo`, of shape
  `defeq (Foo.mk (π₁ x) ... (π_n x)) x Foo`. Requires the TCB to identify the
  ctor and the projection set, which we currently don't track explicitly.

- **Quot's primitive rule**: `defeq (Quot.lift f h (Quot.mk r a)) (f a) α`.
  One rule, hardcoded for the four `Quot.*` constants.

## 2. Level equality (`lvl-eq`) completeness

Mario's `ℓ ≡ ℓ'` is _extensional_: defined by `⟦ℓ⟧_v = ⟦ℓ'⟧_v` for every
assignment `v : ℕ → ℕ` of nat values to universe variables (`VLevel.Equiv` in
the formalization).

**Status: mostly closed by the `mleq` decision procedure (May 2026).** The
old reactive table of `lvl-eq` algebraic rules has been superseded by a port
of **Carneiro's algorithmic level inequality** (Type Theory of Lean thesis,
p.7): the offset relation `mleq L L' N` (⟦L⟧ ≤ ⟦L'⟧ + N for every valuation),
with `lvl-eq L L'` recovered as two-sided `mleq L L' 0 ∧ mleq L' L 0`
(`lvl-eq/le`). It is the inference-rule algorithm (searchable/checkable), NOT
the semantic `VLevel.Equiv`. The 15 structural rules (the thesis' 13 + the two
RHS `imax` simplification duals `imax-lzR`/`imax-lsR`, which the comparison
needs once an offset has put the imax on the right) decide the **universe-
variable-free fragment completely** — including associativity, commutativity,
distributivity, and the max/imax zero/succ/idempotence laws the old table had
to special-case. The prover (`synth.ts`, `proveMleq`) supplies a concrete
integer offset at every step, so Twelf only *checks* ground `N±1` / `N >= 0`
constraints (the `enatlit` `nonneg` witness pattern), never solves for them.

**Remaining gap: universe-variable `imax`.** `mleq`'s structural rules cover
`imax` whose second argument is `zero`/`succ`/`imax`/`max`, but not a bare
universe variable (`limax _ (lvar i)`). The genuine fix is the thesis' 14th
rule, variable elimination by the case split `u ↦ 0` / `u ↦ S u`. It is
deferred: in this proof-checking setting the natural HOAS encoding
(`mleq (LF U) (LG U) N` from the `u = 0` and `u = S u` branches) relies on a
degenerate higher-order unification of `LF U = a` for concrete `U`, which is
fragile. Pending it, the legacy reduce-and-congruence rules (`lvl-eq/imax-idem`
+ the `*-cong` / `symm` / `trans` family, still in `tcb.elf`) are kept as a
**fallback** that reaches the common `imax(L, L) → L` case under a congruence
for variable `L` (e.g. `imax (imax u u) u ≡ imax (succ u) u` in a Peano
encoding — corpus tests 023–025). `proveLvlEq` tries `mleq` first, then this
fallback. The fallback rules are all sound level identities, redundant with
`mleq` on the variable-free fragment; once `mleq/var-elim` lands they can be
dropped. As of this change 36 corpus tests prove their sort equalities via
`mleq`; only the 3 Peano tests use the fallback.

## 3. Inductive-type acceptance (orthogonal to defeq)

Lean's kernel performs structural checks on inductive declarations that are
NOT part of `IsDefEq`. They live in our TCB as separate closed families.

| Check                                                    | Our TCB                           | Status                                                                                                  |
| -------------------------------------------------------- | --------------------------------- | ------------------------------------------------------------------------------------------------------- |
| Inductive type ends in `Sort _`                          | `ends-in-sort`                    | ✓                                                                                                       |
| Constructor strict positivity                            | `ctor-positive` + `no-self-ref`   | ✓ (single-self, non-nested; sound in-TCB via `string-neq` + global `%query`)                            |
| Mutual inductives                                        | —                                 | ✗ deferred — generalize `ctor-positive` to a _list_ of self-refs                                        |
| Nested inductives                                        | —                                 | ✗ deferred — per-type-former "positivity-preserving" predicate                                          |
| Recursor type well-formedness                            | none beyond `defeq T T (esort U)` | **✗ no kernel-side synthesis check — we trust the export**                                              |
| Universe consistency (ctor field sorts ≤ inductive sort) | —                                 | **✗ missing**                                                                                           |
| Subsingleton elimination check                           | generator pre-flight (check f)    | ◑ ≥2-ctor Prop large-elim rejected translator-side (127); ≤1-ctor subsingleton case not LF-verified     |
| Positivity modulo defeq                                  | —                                 | **✗ deepest open issue: lifting `ctor-positive` through `defeq` stops being a closed-family operation** |

The recursor and universe-consistency cases are notable because Lean's kernel
_constructs_ the recursor and _enforces_ universe consistency during inductive
elaboration. We accept whatever the export gives us. This is sound (we
type-check what we're given) but means we can't catch a malformed-recursor
export. For our current threat model (the export is trustworthy), this is
fine.

## 4. Other things in Mario's spec that aren't defeq rules

Mario's `Theory.Typing.Basic` and `Theory.Inductive` files also encode:

- **`Δ ⊢ Γ ok`** (context well-formedness) — implicit in our LF context via
  the `{x : expr} defeq x x A -> ...` pattern. Adequate.
- **`n ⊢ ℓ ok`** (level-param index in range) — we don't carry this
  explicitly; level params appear under `{u : lvl}` LF binders and can't be
  misused. Adequate.
- **VEnv well-formedness** — each `declared` carries its own `dkind-ok` proof;
  the `%unique` seal enforces functional dependency on names. Equivalent to
  Mario's per-decl WF + global injectivity.

## 5. Honest gap list, ranked by impact

By "impact" I mean: how often does the corpus / a real Lean library exercise
this?

## Translator-side declines (formerly tcb-violation cases)

The LF encoding doesn't verify several kernel-level invariants that Lean
checks. When the translator detects one, it emits `%% SKIP:` and declines to
emit the offending declaration. **This is honestly tracked as INCOMPLETE
(🤷)** — not as a Twelf rejection, even when the .ndjson was supposed to be
rejected. Previously the translator emitted `%solve _ : tcb-violation.`
forcing a Twelf abort, which we counted as a "success" rejection; that was a
self-deception, since Twelf wasn't checking the actual soundness condition.

### Migrations completed: 🤷 → ✅ via genuine Twelf mechanisms

The following bad-test rejections were converted from translator-side declines
to Twelf-decided rejections this session (+10 bad ✅):

- **Duplicate names via `%unique declared`** (120, 121, 123, 125, 126). The
  TCB already has `%unique declared +N +LS -1T -1DK *W`. We now emit both
  clashing declarations with distinct LF mangles (`<base>` and
  `<base>__dup<n>`) but the same Lean-name string in the first arg of
  `declared`; `%unique` then catches the overlap during world-checking and
  ABORTs the file.

- **`%solve` on `ends-in-sort` for monomorphic inductives** (039, 040). When
  the translator's `endsInSortProof` returns null, we emit
  `%solve <mn>/ends-in-sort : ends-in-sort <T>.` instead of SKIPping. The
  `ends-in-sort` judgment is closed and decidable; Twelf's proof search
  succeeds for valid Π-chain-to-sort types and ABORTs otherwise. Polymorphic
  case still falls back to SKIP (would need %solve on closed instantiations).

- **`%solve` on `ctor-positive` for monomorphic head-mismatches** (049). When
  `buildCtorSpine` fails, we walk past leading Π binders to the result type
  and test whether `buildAppliesSelf` accepts the head. If not — i.e., the
  ctor's result-type head isn't the inductive at the right level instantiation
  — defer to Twelf via `%solve`. This is sound: `applies-self` only inhabits
  chains ending in `[S] S` (via `applies-self/refl`) or `[S] eapp (M S) E`
  (via `/app`, recursive), with no rule that fires on a constant or
  wrong-named head, so Twelf's search correctly aborts.

- **Level-substituted `%solve` for polymorphic head-mismatches** (045). The
  `inductWrongCtorResLevel` test has a ctor whose result uses swapped level
  params `[u2, u1]` against the inductive's declared `[u1, u2]`. Since
  `%solve` needs a closed goal, we substitute each level param `u_i` with a
  distinct concrete level (`lzero`, `lsucc lzero`, `lsucc lsucc lzero`, ...)
  via fresh `substLevel`/`substExprLevels` helpers, then emit `%solve` on the
  closed instance. Substitution preserves syntactic structure, so a head
  mismatch in the polymorphic original (the swapped levels) survives as a head
  mismatch in the substituted version (`[lsucc lzero, lzero]` vs
  `[lzero, lsucc lzero]`), and `%solve` correctly aborts.

- **Dup-aware downstream synth suppression** (122). The dup_ctor_def test has
  a defn and a ctor with the same Lean name. `%unique` would catch this, but a
  downstream recursor type-synth failure (caused by declTable's
  first-occurrence-wins lookup returning the defn's type when the recursor
  expects the ctor's type) was emitting a SKIP marker that masked the abort in
  the harness. When `dupCounter.size > 0`, the translator now emits a plain
  `%% (declined to emit ...)` comment for synth failures rather than
  `%% SKIP:`, letting `%unique` do its work.

### SAFELIST: encoding gaps Twelf fundamentally cannot represent under the current TCB

**Strict positivity for field-position negative occurrences (047, 050, 105,
plus 106 from a related universe-check fallback).** The TCB's
`ctor-positive/intro` rule is:

```
ctor-positive/intro :
   {T_HOAS : expr -> expr}
   ctor-spine T_HOAS
   -> ctor-positive N0 LS0 (T_HOAS (econst N0 LS0)).
```

The adequacy comment claims T*HOAS is \_the* canonical full-capture function
`(λS. T[N0 LS0 ↦ S])`. But nothing in the encoding enforces this — any T_HOAS
that reproduces T when applied to `(econst N0 LS0)` is accepted. Twelf's
higher-order pattern unification can pick a T_HOAS that leaves some
occurrences of `(econst N0 LS0)` unreplaced inside a sub-expression that's
then S-free as a function of `T_HOAS`'s argument, and `strict-pos/no-occur`
fires vacuously on the closed sub-expression to "prove" strict positivity of a
negative-occurrence ctor.

**Concrete witness Twelf finds for `mk : (I → I) → I`** (test 047):

```
T_HOAS = [e] eforall (eforall (econst I) ([x] econst I)) ([y] e)
```

Only the outer I is abstracted. The inner `eforall (econst I) ([x] econst I)`
— i.e., `I → I` — is closed (doesn't mention `e`), so `strict-pos/no-occur`
accepts it as a vacuously-positive "argument type", and the rest of
`ctor-spine` walks through unchecked.

`%solve` is **unsound** for `ctor-positive` whenever the failure is at
field-position. We detect this via `headIsApplicable` (walk past Π binders,
test `buildAppliesSelf` on the result): if the head IS applicable but
`buildCtorSpine` still fails, the failure must be a field strict-pos issue,
and we stay 🤷 rather than defer to Twelf.

**Pure-TCB fix DONE (May 2026).** `strict-pos` now carries the inductive's
name `N0`, and its absence leaves take a `no-self-ref N0 E` premise (likewise
the Π-domain of `strict-pos/forall`).  `no-self-ref` is a structural traversal
that, at each `econst N` leaf, demands `string-neq N N0`.  So the LF signature
itself — not the generator — bars a self-occurrence from any closed domain:
the under-abstracted `T_HOAS` above leaves `econst I` in the inner domain,
which now forces a `string-neq "I" "I"` obligation.

`no-self-ref/const`'s `N ≠ N0` decision is supplied without a Twelf string-
inequality domain (none ships in the limited-thaw build) by *faking*
disequality the same way the name→meaning functional dependency is faked: a
new OPEN family `string-neq : string -> string -> type` (thawed in
`freeze.elf`) lets an environment *posit* any disequalities its positivity
proofs need, and a global

```
%query 0 * string-neq X X.
```

in `final-checks.elf` ABORTs the whole load if any posited pair is reflexive.
Honest claims (`a ≠ b`) never match `X X`; a lie (`a = a`) sinks the
development.  Net effect: `T_HOAS` correctness is no longer a soundness
condition — a wrong/adversarial `T_HOAS` or spine can only lose completeness (a
HOLE), never fake positivity.  `ctor-positive` is now sound *independent of the
generator* (only `tcb.elf` + `freeze.elf` + `final-checks.elf` + `parse.ts` +
`generate-twelf.ts` + `shared.ts` need auditing; `prover.ts`/`synth.ts` do
not).

Guarded by a hand-written regression:
`lf/soundness/positivity-underabstraction.elf` reconstructs the exact
under-abstraction attack on
`mk : (indNeg → Empty) → indNeg` and is rejected by `scripts/check-soundness.sh`
(the attack type-checks only by declaring `string-neq "indNeg" "indNeg"`, which
the global query then catches).  Note the new check is also *name-only* (any
level instantiation of `N0` counts as an occurrence), closing the related
latent gap where the old name+level `isSelfRef` ignored cross-level self-uses.

The still-deferred generalizations (mutual self-refs, nested inductives,
positivity modulo defeq) are unchanged — see the table rows above.

### Other translator-side declines still active

Each remains a 🤷 candidate for migration into Twelf-verified checks. They
need substantial TCB extensions:

- **numParams ≤ #leading Π in inductive type** (042). Would need `numParams`
  reified in LF (perhaps via a Peano `nat` and a `numparams-ok` judgment).
- **ctor result-type's first numParams args are the right param-binder bvars**
  (043, 044). `applies-self/app` accepts any arg expressions; we'd need a
  stricter `applies-self-bvar-spine` judgment that checks
  position-by-position.
- **ctor result-type's index args don't mention the inductive itself** (046).
  Needs an `s-free` syntactic predicate over Expr, integrated into the
  `applies-self`/`ctor-spine` chain at the right places.
- **concrete-case field universe ≤ inductive universe minus 1** (054). Needs
  universe arithmetic in LF.
- **large elimination from a ≥2-ctor Prop** (127). Gated translator-side
  (check (f)): a Prop inductive with ≥2 ctors whose recursor motive targets a
  non-Prop sort is rejected (SKIP). A pure-TCB fix would add an `le-ok` premise
  to `dkind-ok/irec` that reads the motive's target sort and checks
  subsingleton eligibility; needs universe comparison + ctor-field analysis in
  LF. The ≤1-ctor subsingleton case (Acc/Eq/Quot-style legitimate large elim)
  is currently admitted on typing alone.
- **projection-expression support** (009, 078, 079, 081, 083, 084, 085, 087,
  088, 104). Need `proj` constructor in the expr datatype and corresponding
  typing/reduction rules.

## Honest harness reporting

`check-tests.sh` reports good and bad tests separately:

```
Good (expected accept):  ✅ N1   ⚠️ N2   ❌ N3
Bad  (expected reject):  ✅ N4   ⚠️ N5   💥 N6
```

The bad ⚠️ column makes it visible when a translator-side decline is being
substituted for a Twelf-verified rejection. Bad ✅ counts bad tests Twelf
actually rejected via its LF-encoded checks. After this session: **Good 50 ✅
/ 26 ⚠️ / 10 ❌, Bad 20 ✅ / 19 ⚠️ / 1 💥 = 70 Twelf-verified passes**.

The 20 bad ✅ split:

- **10 from the LF encoding's own checks**: 002, 010, 011, 016, 041, 091, 092,
  102, 103, 113 (defeq failures, `applies-self` rejections, etc., that the
  translator emits directly and Twelf type-checks normally).
- **10 from this session's migrations**: 039, 040, 045, 049, 120, 121, 122,
  123, 125, 126 (via `%unique`, `%solve` on `ends-in-sort`, conditional
  `%solve` on `ctor-positive` for head mismatches, level-substituted `%solve`
  for polymorphic head mismatches, and dup-aware synth suppression).

## Ranked gap list

1. **~~Iota for recursors~~** ✓ **stage 1** (enums, 1-3 ctors, no params, no
   recursive args). Adds:
   - `cnames` (ordered ctor-name list)
   - `enum-rec-body`, `enum-rec-type` (structural recognizer for enum recursor
     types)
   - `defeq-extra` (closed family, no open extension allowed) + `defeq/extra`
     lift
   - 6 iota rules (one per ctor-count × position): `defeq/iota-enum-1`,
     `defeq/iota-enum-2-{first,second}`,
     `defeq/iota-enum-3-{first,second,third}`

   No trust gap: rules pattern-match on `declared` witnesses for the recursor
   and ctors, verify the recursor type fits the enum schema via
   `enum-rec-type`, and require typing premises on motive + minor premises.
   Hand-verified that Bool.rec on Bool.false fires correctly.

   Stages 2+ (first-order trees / Nat, ctors with non-recursive fields / List,
   indexed / Eq, mutual, nested) are bounded incremental rule additions — each
   follows the same pattern: extend `enum-rec-body`-style walker + per-shape
   iota rule. Tests 070/110/112 are still failing; closing them requires stage
   2 (Nat.rec on Nat.succ has recursive arg).

2. **Positivity modulo defeq** (test 048). Hits when a ctor arg type contains
   an unreduced application of a reducible def. Architectural issue: fixing it
   couples positivity to defeq.

3. **Structural eta for one-ctor inductives** (tests 096–098). Hits
   anonymous-constructor reasoning and proofs that rely on the eta law for
   records.

4. **~~Proof irrelevance~~** ✓ added (test 095 still fails —
   translator-incompleteness, the search heuristic doesn't construct
   conv-via-proof-irrel chains. The TCB rule is verified by hand-test.)

5. **K rule** (test 090). Hits dependent pattern-matching on Eq. Part of iota
   (`Eq.rec` on `Eq.refl`).

6. **Function eta** (tests 100, 101). Tests 100/101 are interesting — we have
   `defeq/eta`, so these may be translator-incompleteness, not
   TCB-incompleteness. Worth re-investigating.

7. **`t-const` level-poly congruence**. Probably rare in practice; the corpus
   may not exercise it. Worth adding for completeness but not urgent.

8. **`lvl-eq` algebraic completeness**. Bound to bite eventually. The
   eval-based decision procedure closes it wholesale.

9. **Quot's primitive rule**. No corpus test currently, but blocking for any
   real library that uses quotients (i.e., almost all of them).

10. **Mutual/nested inductives**. Deferred by choice; documented limitation.

## 6. What this means for the project plan

The "complete the TCB" obligation is finite and tractable. The items above are
a finite list; ticking each off is well-defined work, not research. Once
they're all ticked, we'd have a TCB that's declaratively complete relative to
Mario's spec — meaning any Lean environment that the spec accepts, our TCB has
a proof for.

What we'd give up by not pursuing this: the ability to say "the translator
failing means Lean shouldn't have accepted this either". With gaps remaining,
a translator failure can mean either (a) Lean shouldn't have accepted it, or
(b) we just don't have the rule, or (c) the translator search heuristic gave
up. Closing the TCB-completeness gaps reduces (b) to ∅.

What we don't get even after closing them: a decision procedure. The
translator can still time out, give up, or fail to find a proof that exists.
That's an explicit non-goal — we're OK with handing off to a
human/LLM/external procedure in the gap. The closure of the TCB just
guarantees those handoffs are well-posed: the proof exists somewhere in the LF
signature, the question is just whether someone (us, them, something else) can
find it.

---

## 7. Salvaged design notes (from deleted `archive/`, May 2026)

When the `lean2lf.ts → generate-twelf.ts + prover.ts + synth.ts` refactor
landed, the old `archive/` design docs and `plugin-refactor.md` were deleted
(the refactor is done; full text in git history). These are the high-value,
still-actionable nuggets that were in them. The framework stance and a longer
soundness comparison lived in `archive/mm0-analysis.md` (vs. Carneiro's
`lean.mm1`); the level material in `archive/first-version-report.md`.

### 7.1 Level-equality decision procedure (closes §2 wholesale)

The highest-leverage `lvl-eq` fix is to port **Carneiro's algorithmic level
inequality** (Type Theory of Lean thesis, p.7): the offset relation
`ℓ ≤ ℓ' + n`, `n ∈ ℤ`, with `ℓ ≡ ℓ'` as `ℓ ≤ ℓ' + 0 ∧ ℓ' ≤ ℓ + 0`. (NB: this
is the _inference-rule_ algorithm, searchable by Twelf — **not** lean4lean's
`VLevel.LE`, which is a semantic universal-over-valuations definition and
isn't directly searchable.)

The thirteen structural rules transcribe directly into Twelf over the integer
constraint domain and were validated against `%solve` (all queries <10 ms,
including nested `imax`/`max`, commutativity, and correct _failure_ on
`1 ≤ 0`):

```twelf
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

**The one sticking point** is the fourteenth rule — universe-variable
elimination by case-split `u ↦ 0` / `u ↦ Su`. The naive HOAS transcription
(`mleq (L lz) (L' lz) N -> ({u} mleq (L (ls u)) (L' (ls u)) N) -> mleq (L U) (L' U) N`)
loops in Twelf search (`L, L' : level -> level` unify with anything).
**Recommended: Option B (hybrid).** Keep the thirteen structural rules in
Twelf; detect `imax _ U` for free `U` in TypeScript, perform the case-split
there, `%solve` each branch, and recombine via a no-op `mleq/var-discharge`
axiom (concrete levels passed in from TS, so it never fires on its own during
search). The variable-elim case is empirically rare. Net effect: replaces the
reactive `lvl-eq` rule table with a near-complete decision procedure, and also
fixes the `t-const` same-level diagonal limitation (§1.1) once levels compare
up to equivalence. The `%solve`-carries-a-side-condition pattern (already used
for `enatlit`'s `N >= 0`) is the template.

### 7.2 Name-reservation soundness check (principled fix for 124-style)

`124_dup_rec_def2` is currently rejected by a _translator-side_ pre-flight
check in `generate-twelf.ts` (a primitive recursor must be named
`<type>.rec`). The **principled, Twelf-verified** alternative — model Lean's
implicit "adding inductive `Foo` reserves the name `Foo.rec`" rule — was
validated with five Twelf spikes. Root cause: Lean generates the recursor name
fresh as `mkRecName ind = ind ++ ".rec"`, so the reservation exists no matter
what the export calls the recursor; an export naming it `original_rec` is
adversarial.

Validated LF design (deviates from the obvious sketch in 3 ways that matter):

1. **`name-kind` payloads are payload-free** (`is-declaration`, `is-rec`,
   `is-quot`) — a `string` payload inside the _kind_ puts a non-ground
   variable in `%mode name +S -K` output (Twelf can't run string
   deconcatenation). The inductive↔recursor link rides in the _string index_
   via `(N ++ ".rec")`, which Twelf evaluates forward fine.
2. **The reservation family is open with ground per-decl constants only**
   (exactly like `declared`). Generic constructors make `%unique` report a
   static overlap on every file (false positive).
3. **Reservations live in the `dkind-ok` rules with a threaded
   `{N : string}`** (forcing `N` = the `declared` name), not in the `dkind`
   constructors. The recursor (`irec`) reserves **nothing** — the inductive
   owns the `.rec` slot (`%unique` flags _any_ two constants sharing a string,
   even same-kind).

Then `dkind-ok/indt` requires both `name N is-declaration` and
`name (N ++ ".rec") is-rec`, and `final-checks.elf` adds
`%mode name +S -K. / %worlds () (name _ _). / %unique name +S -1K.` — so a
`def Foo.rec` and inductive `Foo` both reserving string `"Foo.rec"` with
different kinds make uniqueness false → ABORT. This requires repurposing
term-level `name` to `string` throughout `tcb.elf` (mechanical; generated
`.elf` already use string literals). Out of scope of the spike: forcing a
recursor's _own_ name to be `<ind>.rec` in general (needs a `+kind -string`
uniqueness in the other direction).

### 7.3 `lean.mm1` borrows + the trusted-export soundness gaps

Carneiro's `lean.mm1` is a _complete_ declarative spec of the same `IsDefEq`;
where our TCB is partial it reads as a checklist. No bug found in rules we
already check; the gaps are exactly the things §3 marks "we trust the export",
which flip from _incomplete_ to _unsound_ if the export isn't trustworthy:

- **Ctor field-universe constraints** — `lean.mm1`'s `ctor_Pi` carries
  `l2 <=l l` (each field's sort ≤ the inductive's sort); `ctorR_S` carries
  `l_imax l2 l <=l l` for recursive args. We check only `defeq T T (esort U)`.
  (Our translator-side concrete-case check (d) approximates this; encoding it
  in LF removes the trust.)
- **Large-elimination / subsingleton eligibility** — `lean.mm1`'s `LE` /
  `LE_ctor` / `LE_mem` apparatus decides whether a Prop-inductive may
  eliminate into `Type`. Missing here; allowing large elimination from a
  non-subsingleton Prop is a classic route to a closed proof of `False`.
- **Recursor type well-formedness** — `lean.mm1` _synthesizes_ the recursor
  type (`Rec_*`) and checks it; we accept the export's. Our iota rules
  currently lean on the export supplying a genuine recursor rather than a
  schema-shaped lookalike.

Porting discipline (LF vs. MM0): **delete every `subst: A[e/x] = B` premise
and replace `B` with the LF application `(λx.A) e`** — MM0 reifies
substitution only because it lacks LF's meta-level β. Stance: this project
follows **Appel & Felty** (LF as proof-checking with a tiny trusted checker),
_not_ Crary–Sarkar (safety argued inside the Twelf metalogic). Keep
`%total`/`%worlds`/`%covers` off the trusted checking path; the only
legitimate metatheorem use is confidence _about_ the TCB (e.g. proving two
`lvl-eq` characterizations coincide), living outside `tcb.elf`. `%unique` and
the open-`declared` discipline are the two non-pure-LF checks we do rely on —
small decidable side-conditions, the kind a flit-style minimal LF checker
would need to add.

### 7.4 Name-usages not captured by Lean's `Declaration` (adequacy checklist)

A faithful `.render.elf` must account for names that don't appear
syntactically in the per-`Declaration` input:

1. **Quot family** — `Declaration.quotDecl` is payload-free; the kernel
   injects `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`/`Quot.sound` with hardcoded
   types.
2. **Literal-reduction names** — `Nat`, `Nat.zero`, `Nat.succ` (+ arithmetic),
   `String`, `String.mk`, `List.nil/cons`, `Char.ofNat`, … are hardwired into
   the kernel's literal extension; none appear in the literal `Expr`.
3. **Recursors** — synthesized fresh as `Foo.rec` (lean4export does serialize
   them, so our NDJSON carries them — but the bare `Declaration` type
   doesn't).
4. **`proj typeName idx`** — needs the structure's single constructor for its
   reduction; carried today as opaque `eproj` data with no link to the names
   it depends on.
