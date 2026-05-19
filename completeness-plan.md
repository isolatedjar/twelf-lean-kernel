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

Our `lvl-eq` is a derivability relation with explicit rules. Status:

| Rule                             | Status                                              |
| -------------------------------- | --------------------------------------------------- |
| `lvl-eq/refl`                    | ✓                                                   |
| `lvl-eq/symm`                    | ✓                                                   |
| `lvl-eq/trans`                   | ✓                                                   |
| `lvl-eq/max-comm`                | ✓                                                   |
| `lvl-eq/max-self`                | ✓                                                   |
| `lvl-eq/imax-zero`               | ✓                                                   |
| `lvl-eq/zero-imax`               | ✓                                                   |
| `lvl-eq/imax-succ`               | ✓ (`imax(a, S b) = max(a, S b)` — `b+1` is nonzero) |
| `lvl-eq/imax-idem`               | ✓ (`imax(L, L) = L`)                                |
| `lvl-eq/{lsucc,lmax,limax}-cong` | ✓                                                   |
| max-assoc                        | ✗ missing                                           |
| max-left-id (`max 0 L = L`)      | ✗ missing                                           |
| max-right-id (`max L 0 = L`)     | ✗ missing                                           |
| imax-with-max distributivity     | ✗ missing                                           |
| general normalization            | ✗ missing                                           |

**Completeness gap.** Our rules are sound but provably incomplete: e.g.,
`max(max u v) w ≡ max u (max v w)` (associativity) isn't derivable. We've
added rules reactively when the corpus forces them.

**The decision-procedure alternative** (sketched in earlier conversation):
replace this whole table with `eval : nats -> level -> nat -> type` and a
finite-test-set quantifier. That gives TCB-completeness for `lvl-eq` in one
move, relative to Mario's `VLevel.Equiv`. It's a refactor of working code
rather than a fix to any of the failing corpus tests, so not the highest
leverage right now, but it'd close this whole section as a single tick-box.

## 3. Inductive-type acceptance (orthogonal to defeq)

Lean's kernel performs structural checks on inductive declarations that are
NOT part of `IsDefEq`. They live in our TCB as separate closed families.

| Check                                                    | Our TCB                           | Status                                                                                                  |
| -------------------------------------------------------- | --------------------------------- | ------------------------------------------------------------------------------------------------------- |
| Inductive type ends in `Sort _`                          | `ends-in-sort`                    | ✓                                                                                                       |
| Constructor strict positivity                            | `ctor-positive`                   | ✓ (single-self, non-nested)                                                                             |
| Mutual inductives                                        | —                                 | ✗ deferred — generalize `ctor-positive` to a _list_ of self-refs                                        |
| Nested inductives                                        | —                                 | ✗ deferred — per-type-former "positivity-preserving" predicate                                          |
| Recursor type well-formedness                            | none beyond `defeq T T (esort U)` | **✗ no kernel-side synthesis check — we trust the export**                                              |
| Universe consistency (ctor field sorts ≤ inductive sort) | —                                 | **✗ missing**                                                                                           |
| Subsingleton elimination check                           | —                                 | ✗ missing (affects large elimination from Prop into Type)                                               |
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

The adequacy comment claims T_HOAS is _the_ canonical full-capture function
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

**Principled fix (not done):** add a `fully-captures N0 LS0 T_HOAS T` judgment
that's only inhabited when T_HOAS abstracts _every_ occurrence of
`(econst N0 LS0)` in T. Make `ctor-positive/intro` take a `fully-captures`
premise. The judgment is recursive over Expr structure and decidable (no
higher-order ambiguity), so the resulting strengthened `ctor-positive` would
be soundly `%solve`-able.

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
