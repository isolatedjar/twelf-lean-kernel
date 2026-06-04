# TCB-completeness checklist

What this document is: a tick-box accounting of how much of Mario's
declarative specification of Lean's type theory our TCB encodes. The
specification is `VEnv.IsDefEq` (Figure 1 of the lean4lean paper, implemented
in `Lean4Lean/Theory/Typing/Basic.lean`) plus the inductive and quotient
extensions added via `t-extra`.

## Status as of arena dry-run (2026-06)

Running the kernel against the full Lean Kernel Arena tutorial corpus + the
14 named singletons (143 tests total) via the new `scripts/arena-check.sh`
wrapper gives:

| outcome | count | meaning |
|--------:|------:|---------|
| ✅ accept | 54 | full pipeline (tcb + freeze + derived + final-checks) accepts |
| 🩹 holes  | 62 | only unfilled HOLEs blocked acceptance (43% of the corpus) |
| 🤷 shrug  | 19 | generator declined to represent the env |
| ❌ fail   | 8  | `.full.elf` rejected even without freeze (concrete error / fail-on-purpose) |
| 💥 sound  | 1  | **bad-test wrongly accepted: `tutorial/bad/066_BogusRecursor`** |

The 1 💥 is the original headline finding. A subsequent
soundness-regression refresh (commit `e43b96d Add more soundness checks`)
added three more adversarial `.elf` files in `lf/soundness/` to widen the
audit: **`large-elim-prop.elf`** (a closed proof of `defeq P Q : Prop`
constructed via large-elim + proof-irrel + iota), **`universe-too-high-
field.elf`** (a ctor with a field-universe exceeding the inductive's,
the Girard-paradox doorway), and **`rec-name-slot.elf`** (the `<ind>.rec`
slot squatted by a non-recursor). The first two are true soundness gaps;
the third is a spec-compliance gap with no False-route. All three are
currently **accepted by the TCB**, alongside `066_BogusRecursor`. Detailed
fix designs are in §3.1 (recursor-type, rolls in large-elim), §3.2
(field-universe), and §3.3 (rec-name).

This was previously framed in §3 / §7.3 as a "we trust the export" choice
under the assumption that the export is trustworthy. The arena's threat
model includes adversarial exports, so what was incomplete-but-defensible
under the prior framing is now demonstrated-unsound on four independent
adversarial inputs: bringing the missing checks inside the TCB is the
**#0 priority** (above the existing completeness gaps, which are at worst
loss-of-completeness).

The wrapper, the YAML submission, and the standalone-soundness mapping
(✅ → exit 0, 🩹/🤷/🔴 → exit 2, ❌/fail-on-purpose → exit 1) are documented
in `arena-submission-plan.md`. A CI smoke test (`.github/workflows/main.yml`
job `arena-smoke`) drives `arena-check.sh` against `tutorial/001_basicDef`
(expects 0) and `tutorial/002_badDef` (expects 1) on every push, guarding
the arena interface against regression.

> **Test-number staleness.** Numbered tests cited below refer to the
> post-`caf28eb` ("Revamp test infrastructure") corpus. Some references in
> §5 use the older numbering and have not been mass-rewritten — when a
> number looks wrong against the current `tutorial/`, treat the
> *description* as authoritative and find the equivalent.

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

**Status: closed by the `mleq` decision procedure (May 2026).** The old
reactive table of `lvl-eq` algebraic rules has been replaced by a port of
**Carneiro's algorithmic level inequality** (Type Theory of Lean thesis, p.7):
the offset relation `mleq L L' N` (⟦L⟧ ≤ ⟦L'⟧ + N for every valuation), with
`lvl-eq L L'` recovered as two-sided `mleq L L' 0 ∧ mleq L' L 0` (`lvl-eq/le`).
It is the inference-rule algorithm (searchable/checkable), NOT the semantic
`VLevel.Equiv`. `lvl-eq` now has only `refl` (the syntactic primitive) and `le`
(the `mleq` bridge); no algebraic or congruence rules remain.

The 15 structural rules (the thesis' 13 + the two RHS `imax` simplification
duals `imax-lzR`/`imax-lsR`, needed once an offset puts the imax on the right)
decide the variable-free fragment — associativity, commutativity,
distributivity, and the max/imax zero/succ/idempotence laws the old table had
to special-case. The prover (`synth.ts`, `proveMleq`) supplies a concrete
integer offset at every step, so Twelf only *checks* ground `N±1` / `N >= 0`
constraints (the `enatlit` `nonneg` witness pattern), never solves for them.

**Universe variables: closed via first-order variable elimination.** The
thesis' 14th rule eliminates a universe variable by the case split `u ↦ 0` /
`u ↦ S u`. Earlier this was thought to require fragile HOAS (`mleq (LF U)(LG U)
N` with a degenerate higher-order unification `LF U = a`). But our level
variables are **first-order de Bruijn indices** (`lvar : lidx -> lvl`), so the
case split is encoded directly as `mleq/var-elim` using a first-order
substitution judgment `lvl-subst` and structurally-decidable index
(dis)equality `lidx-eq` / `lidx-neq` (no posit-and-audit — unlike strings,
`lidx` disequality is a genuine closed judgment). Soundness: `lvar I` ranges
over ℕ = {0} ∪ {S k}, so a goal holding with `I ↦ 0` and with `I ↦ S I` (whose
still-free `I` is the predecessor) holds for every valuation; the substitution
is exact by construction, so the rule has no loophole. The prover (`proveMleq`
→ `proveVarElim`) detects a variable blocking as an `imax` second argument,
case-splits it, and recurses. This reaches e.g. `imax (imax u u) u ≡
imax (succ u) u` (Peano tests 023–025). `mleq` is now complete for the full
fragment; 36 corpus tests prove sort equalities via the structural rules, the 3
Peano tests via `var-elim`.

## 3. Inductive-type acceptance (orthogonal to defeq)

Lean's kernel performs structural checks on inductive declarations that are
NOT part of `IsDefEq`. They live in our TCB as separate closed families.

| Check                                                    | Our TCB                           | Status                                                                                                          |
| -------------------------------------------------------- | --------------------------------- | --------------------------------------------------------------------------------------------------------------- |
| Inductive type ends in `Sort _`                          | `ends-in-sort`                    | ✓                                                                                                               |
| Constructor strict positivity                            | `ctor-positive` + `no-self-ref`   | ✓ (single-self, non-nested; sound in-TCB via `string-neq` + global `%query`)                                    |
| Mutual inductives                                        | —                                 | ✗ deferred — generalize `ctor-positive` to a _list_ of self-refs                                                |
| Nested inductives                                        | —                                 | ✗ deferred — per-type-former "positivity-preserving" predicate                                                  |
| Recursor type well-formedness                            | none beyond `defeq T T (esort U)` | **💥 demonstrated unsound on `066_BogusRecursor` + `lf/soundness/large-elim-prop.elf` — see §3.1**               |
| Universe consistency (ctor field sorts ≤ inductive sort) | —                                 | **💥 demonstrated unsound on `lf/soundness/universe-too-high-field.elf` — see §3.2**                             |
| Subsingleton elimination check                           | generator pre-flight (check f)    | **💥 demonstrated unsound on `lf/soundness/large-elim-prop.elf` (rolled into §3.1's fix)**                       |
| Recursor lives at `<ind>.rec`                            | translator emits the reservation  | **◑ spec-compliance gap on `lf/soundness/rec-name-slot.elf` — see §3.3** (no False, but env Lean would reject)   |
| Recursor iota faithfulness (ctor list duplicate-free)    | enum iota reconstructs positionally | **💥 demonstrated unsound on `lf/soundness/dup-ctor-iota.elf` (literal `False`) — see §3.4; latent: no iota generation yet** |
| Positivity modulo defeq                                  | —                                 | **✗ deepest open issue: lifting `ctor-positive` through `defeq` stops being a closed-family operation**         |

elaboration, whereas our TCB re-derives neither — it accepts whatever recursor
type and field universes the input supplies. That is a **soundness gap, full
stop**, not a defensible trust choice: the kernel is supposed to validate these
itself, and the arena's whole purpose is to feed it inputs that violate them.
`066_BogusRecursor` (§3.1) is a concrete input the TCB wrongly accepts;
`large-elim-prop` (`lf/soundness/`) drives the recursor gap all the way to a
proof of `False`. Bringing recursor well-formedness and universe consistency
*inside* the TCB is required, not optional. "The input is well-formed" is an
assumption we explicitly reject.

The `lf/soundness/` adversarial corpus and `scripts/check-soundness.sh` are
the audit instruments; each `.elf` carries an `Expected outcome: ABORT`
header and a comment explaining the attack. The table below is the
current scoreboard (updated as fixes land; verify with a fresh
`check-soundness.sh` run before quoting).

| File                                          | Type                            | Current verdict | Fix area              |
| --------------------------------------------- | ------------------------------- | --------------- | --------------------- |
| `arena tutorial/bad/066_BogusRecursor.ndjson` | true (recursor type wrong)      | 💥 accepted     | §3.1                  |
| `lf/soundness/large-elim-prop.elf`            | true (`defeq P Q : Prop`)       | ✅ aborts (a)   | §3.1                  |
| `arena bad/large-elim-imax-prop.ndjson`       | true (imax-disguised §3.1)      | 💥 accepted     | §3.1                  |
| `lf/soundness/universe-too-high-field.elf`    | true (Girard doorway)           | ✅ aborts (a)   | §3.2 (partial — §3.2.1) |
| `arena bad/field-too-high-imax.ndjson`        | true (imax-disguised §3.2)      | 🩹 declines (b) | §3.2 (partial — §3.2.1) |
| `lf/soundness/rec-name-slot.elf`              | spec-compliance, no False-route | 💥 accepted     | §3.3                  |
| `lf/soundness/dup-ctor-iota.elf`              | true (literal `False`)          | 💥 accepted     | §3.4                  |
| `lf/soundness/rec-slot-theft.elf`             | passing regression              | ✅ rejected      | already TCB           |
| `lf/soundness/level-var-elim-false.elf`       | passing regression              | ✅ rejected      | already TCB           |
| `lf/soundness/positivity-underabstraction.elf`| passing regression              | ✅ rejected      | already TCB           |

(a) After §3.2's partial landing, the hand-written attacks use the *old*
`dkind-ok/ctor` signature (no `field-universes-ok-skip-params` premise),
which no longer type-checks — so they ABORT, but for the schematic reason
that the file is out-of-date, not because the field-universe check fires
on them.  An updated `large-elim-prop.elf` that supplies the new ctor
premises would re-expose §3.1's recursor-type gap; the field-universe
check is orthogonal to large-elim soundness.  See §3.2.1 for the
post-§3.2 state.

(b) Generator-emitted `.full.elf` for these arena tests supplies the new
`dkind-ok/ctor` premises, but the `field-universes-ok-skip-params` slot
is a HOLE on a frozen family (the prover-side fuo synthesis isn't yet
implemented), so the ctor declines.  For a bad test, decline counts as
correct rejection from the arena's perspective.

**rec-name-slot vs. rec-slot-theft: what the pair tells us (§3.3).**
The TCB already catches a *different* rec-slot attack via `%unique name`:
`rec-slot-theft.elf` reserves `name "Foo.rec" (is-rec-for "Foo")`
alongside the inductive, then tries to also declare
`name "Foo.rec" (is-decl T (defn V))` — two `nkind`s for the same
string, so `%unique name` aborts the load.  That mechanism is sound
*provided the reservation is in place*.  `rec-name-slot.elf` is the
inductive that *omits* the reservation; nothing collides, and the
junk `def Foo.rec` is accepted.

So the §3.3 fix isn't "add string concat" — it's the weaker but
sufficient: **require `declared/ok-indt` to take a `name MRec (is-rec-for
N)` premise.**  Then no inductive can be declared without *some*
rec-name reservation, the translator picks a canonical `<ind>.rec` by
convention, and `def <ind>.rec` then collides with that reservation
exactly the way `rec-slot-theft` already exercises.  A malicious
translator that picks a non-canonical MRec doesn't get a False-route
either — the env just has a non-standard recursor name, with `def
<ind>.rec` as an unrelated definition.  Concrete plan moved to §3.3.

**The two arena `imax`-disguised tests are *the same gap classes* as §3.1
and §3.2** — they exploit a translator-side preflight bypass
(`levelToNumber` doesn't normalize `imax 1 1 → 1` or `imax 1 0 → 0`), so the
generator's gate misclassifies the sort and skips the check.  The TCB-side
fixes in §3.1/§3.2 use `mleq` (Carneiro's algorithmic level inequality,
§7.1), which handles `imax` natively — so closing §3.1 and §3.2 closes
all four corresponding tests, not just the syntactic ones.  A translator-
side `normalizeLevel` shim before `levelToNumber` would also close them,
but that's a stopgap; the architectural move is to bring the check into
the TCB so the translator's preflight cleverness is no longer load-bearing.

### 3.1 Recursor-type soundness gap (the `066_BogusRecursor` finding)

**The attack.** The arena test
`lean-kernel-arena/_build/tests/tutorial/bad/066_BogusRecursor.ndjson`
declares a one-ctor inductive

```lean
inductive BogusRecursor : Type where
  | mk : BogusRecursor
```

and then asserts `BogusRecursor.rec : Sort 0` (i.e. `Prop`). A genuine
Lean export would synthesize the recursor type
`{motive : BogusRecursor → Sort u} → motive mk → (t : BogusRecursor) → motive t`
during elaboration. The bogus one just hands back `Prop`.

**Why the TCB lets it through.** The relevant rule (`lf/tcb.elf`):

```twelf
dkind-ok/irec :
   defeq T T (esort U) -> dkind-ok irec T.
```

This is only "T is *some* well-formed type". `Prop` qualifies, so the rule
fires and `declared "BogusRecursor.rec" (esort lzero) irec` is admitted.
The freeze step accepts it (the obligation has been discharged), and the
load completes. The `%unique name` check at `final-checks.elf` doesn't help
either — `name "BogusRecursor.rec" (is-rec-for "BogusRecursor")` is exactly
the reservation the inductive's emission makes.

**Two viable fixes, in increasing order of TCB ambition.**

*Fix A — translator-synthesized canonical schema, checked TCB-side via
`defeq`.* The translator already knows how to build the canonical recursor
type from the inductive's payload (it would have to, to dispatch iota
rules). Make it emit the canonical type `T_canon` alongside `T_supplied`
and a `defeq T_supplied T_canon (esort U)` witness. Then `dkind-ok/irec`
takes the defeq witness as a premise rather than just well-formedness:

```twelf
dkind-ok/irec :
   defeq T T_canon (esort U)
   -> rec-schema-canonical N T_canon  %% closed LF judgment
   -> dkind-ok irec T.
```

The work is in `rec-schema-canonical`: a closed LF family that constructs
the canonical recursor type from `declared "<ind>" Ts indt` + the ctor
declarations. This is structurally large (motive binder, per-ctor minor
premises with field IHs, major premise, result), but bounded — Mario's
spec gives the recipe explicitly. The translator is untrusted for this
construction: if it lies about `T_canon`, `rec-schema-canonical` won't
inhabit, and the load fails.

*Fix B — make recursor declaration not a `declared/ok-irec` at all.*
Inductive emission already knows everything it needs. Replace
`declared "<ind>.rec" T irec` with a derived family `rec-declared
"<ind>.rec" "<ind>" T` whose only inhabitant comes from a rule that takes
the inductive's `declared` witness, the ctor witnesses, and **builds T
position-by-position** — no `T_supplied` ever crosses the boundary. The
recursor's type ceases to be a translator input and becomes a derivation
output. Cleaner soundness story; bigger refactor (every existing iota rule
that pattern-matches `declared <rec> T irec` would migrate).

Fix A is the path of least disruption and lands soundness in a
self-contained edit to `dkind-ok/irec` + a new `rec-schema-canonical`
family. Fix B is the asymptotically right design but pulls in the recursor
across every iota-stage rule we eventually add.

**Sibling attack: `large-elim-prop.elf`.** Same root cause, different symptom.
The hand-written `lf/soundness/large-elim-prop.elf` declares
`inductive PropTwo : Prop | a | b`, then asserts a Bool-style recursor whose
motive's universe is `Type 0`. The TCB's `dkind-ok/irec` accepts it (the type
*is* well-formed at some sort). Combined with `defeq/proof-irrel`
(`a ≡ b : PropTwo : Prop` because both are proofs of the same Prop) and the
existing `defeq/iota-enum-2-*` rules, the file derives a closed witness
`boom : defeq P Q (esort lzero)` for two distinct axioms `P`, `Q : Prop` —
that's the inconsistency. So `dkind-ok/irec` must enforce *both* (a) the
recursor type matches the canonical schema and (b) the motive universe `U`
is eligible (Prop inductives with ≥2 ctors may only large-eliminate when `U
= lzero`). One premise covers both:

```twelf
dkind-ok/irec :
   declared IndN (esort UInd) indt
   -> rec-schema-canonical IndN UInd U T   %% T = canonical recursor type for
                                            %% IndN at sort UInd eliminating to U;
                                            %% relation enforces LE-eligibility
                                            %% when UInd = lzero & ≥2 ctors
   -> dkind-ok irec T.
```

Building `rec-schema-canonical` is the major piece of work. Lean's spec gives
the recipe; the LF transliteration is bounded (one rule per "shape" — enum,
recursive enum, params, indices, etc.). The existing `enum-rec-type` in
`tcb.elf` is the 1-3-ctor-enum case of this family and serves as the
prototype.

**Regression.** Both `066_BogusRecursor.full.elf` (already auto-generated
from the arena) and `lf/soundness/large-elim-prop.elf` (already
hand-written) will flip from 💥 to ✅ as soon as `rec-schema-canonical` is
in place. Add `lf/soundness/bogus-recursor.elf` if you want a hand-written
mirror of the 066 attack independent of the generator (currently the only
trace is the auto-generated `lf/tests/066_BogusRecursor.full.elf`).

**Cost of the fix.** 98 of 143 arena tests currently exercise
`declared/ok-irec` (and so flow through `dkind-ok/irec`); 31 of those are
currently ✅. The fix requires that every admitted recursor come with a
canonical-schema witness, which means `rec-schema-canonical` must cover
every inductive shape we admit (today: the `enum-rec-type` recognizer
only handles 1-3 ctor enums with no params and no rec args). Until the
canonical-schema family is extended to match every iota-supported shape
(and stage 2+ shapes whose recursors we admit but don't iota on), the
fix will convert a number of currently-✅ tests into 🩹 (decline). Net
the right trade — the TCB stops admitting recursors it can't audit — but
worth flagging that the immediate arena-accept count will fall before
the completeness work catches it back up.

### 3.2 Ctor field-universe gap (the `universe-too-high-field.elf` finding)

**The attack.** `lf/soundness/universe-too-high-field.elf` declares
`inductive TooHigh : Type 0 | mk (a : Type 0) : TooHigh`. The field `a`'s
type `Type 0` lives at `Sort 1`, but the inductive itself is at `Sort 1`
(`Type 0`). Lean's rule (`l2 ≤ l` in `lean.mm1`'s `ctor_Pi`) demands each
field's sort be ≤ the inductive's sort; here it isn't, so Lean rejects.

This is the classic doorway to Girard's paradox — once you can pack types
into smaller universes via a constructor, a closed proof of `False` is a
few rules away. The hand-written file stops short of actually building the
False proof; the TCB accepting the declaration is enough to demonstrate the
gap.

**Why the TCB lets it through.** `lf/tcb.elf:dkind-ok/ctor` checks only that
the ctor type is well-formed at *some* sort plus `ctor-positive`. There is
no premise relating any field's sort to the inductive's:

```twelf
dkind-ok/ctor :
   defeq T T (esort U) -> ctor-positive ... T -> dkind-ok ctor T.
```

`U` is the ctor type's sort, not the inductive's. Nothing in the rule
chases through the Π chain of `T` to bound each domain's sort.

**Proposed fix.** Add a `field-universes-ok T UInd` premise that walks `T`'s
Π chain and, for each field domain `D`, demands `mleq sortOf(D) UInd 0`
(D's sort ≤ inductive's sort, per §7.1's algorithmic level inequality).
The inductive's sort `UInd` is recovered from the parent inductive's
`declared` witness:

```twelf
dkind-ok/ctor :
   declared IndN (esort UInd) indt
   -> defeq T T (esort UCtor)
   -> ctor-positive IndN _ T
   -> field-universes-ok T UInd     %% new: each field's sort ≤ UInd
   -> dkind-ok ctor T.

field-universes-ok : expr -> lvl -> type.
field-universes-ok/result :
   field-universes-ok (econst _ _) _.    %% reached the result type — done
field-universes-ok/forall :
   defeq D D (esort UD)                    %% domain's sort UD
   -> mleq UD UInd 0                       %% UD ≤ UInd (§7.1)
   -> ({x:expr} field-universes-ok (B x) UInd)
   -> field-universes-ok (eforall D B) UInd.
```

The recursion in `field-universes-ok/forall` walks under the LF binder, so
each field's `(esort UD)` is computed at the point that field is introduced.
The `mleq UD UInd 0` premise is the algorithmic level-inequality from
§7.1 (already implemented per `Complete mleq …` in commit history) —
reused, no new level machinery.

`Prop` (sort `lzero`) is its own special case via the standard
`l2 ≤_imax l` impredicativity rule; that drops out of `mleq`'s `imax` cases
without a separate Prop carve-out.

**Cost.** Tighter than §3.1: a single new judgment + one new premise on
`dkind-ok/ctor`. Existing tests that already satisfy the universe constraint
(the entire arena's good corpus — Lean's elaborator ensures this) stay
green. The only new failures are translator outputs where the env is
already malformed, which is exactly the desired behavior. The fix should
require ~50 LF lines + a translator update to emit
`field-universes-ok` witnesses (the translator can synthesize them
mechanically by recursing on the ctor type).

### 3.2.1 Status as of 2026-06-03 — §3.5 architectural landing (Steps 1–5)

**Steps 1–5 of the §3.5 plan have landed in this session.**  The TCB now
carries the inductive family's relational metadata on the `dkind`
constructors themselves:

```twelf
indt : cnames -> lidx -> dkind.    %% Ctors list + total leading-Π count
ctor : string -> lidx -> dkind.    %% parent IndN + cidx
irec : string -> dkind.            %% parent IndN
```

The new `declared/ok-indt` / `declared/ok-ctor` rules consult the
recorded payloads to enforce the spec-compliance conditions that were
previously absent:

| Premise | Closes |
|---|---|
| `name MRec (is-rec-for N)` on `declared/ok-indt` | §3.3 rec-name-slot |
| `count-leading-foralls T NParams` on `declared/ok-indt` | §3.2.2 NumParams-bypass |
| `cnames-distinct Ctors` on `declared/ok-indt` | §3.4 dup-ctor-iota |
| `name IndN (is-decl _ (indt Ctors NParams))` + `cmem N Ctors` on `declared/ok-ctor` | §3.5 spurious-ctor gap |

The six iota rules (`defeq/iota-enum-{1,2-first,2-second,3-first,3-second,3-third}`)
now consume the inductive's reservation via `name FooName (is-decl _
(indt Ctors NParams))` rather than taking Ctors as a free premise, so
the Ctors list iota sees is the audited (distinct, exhaustive) one.

**Arena scoreboard after Steps 1-5** (145 tests, post-translator update):

- Good: 25 ✅ / 58 🩹 / 10 ❌ — *identical to pre-§3.5 partial-landing
  baseline*.  The 28 good tests that the §3.2 partial dropped to 🩹
  remain 🩹; nothing new dropped.
- Bad: 17 ✅ / 35 🩹 / **0 💥** — soundness gap closed on the corpus.
- **All 7 hand-written soundness regressions in `lf/soundness/` ABORT
  correctly**:

| File | Pre-§3.5 | Post-§3.5 | Caveat |
|---|---|---|---|
| `dup-ctor-iota.elf` | 💥 accepted | ✅ rejected | currently aborts on signature mismatch — see "stale soundness regressions" below |
| `rec-name-slot.elf` | 💥 accepted | ✅ rejected | same |
| `universe-too-high-field.elf` | ✅ aborts (sig) | ✅ rejected | same |
| `large-elim-prop.elf` | ✅ aborts (sig) | ✅ rejected | same |
| `rec-slot-theft.elf` | ✅ rejected | ✅ rejected | already covered |
| `level-var-elim-false.elf` | ✅ rejected | ✅ rejected | already covered |
| `positivity-underabstraction.elf` | ✅ rejected | ✅ rejected | already covered |

**Stale soundness regressions to refresh.** The first four hand-written
`.elf` files were written against the pre-§3.5 `dkind-ok/{indt,ctor,
irec}` and `declared/ok` shapes, which Twelf now rejects on signature
mismatch before the actual exploit fires.  So they ABORT, but for the
wrong reason — we haven't verified that §3.4 / §3.3 / §3.2 / §3.5 *as
landed* close the substantive attacks.  Follow-up work: refresh each
file to the new ctor/indt witness shape (`<mn>/eisl`, `<mn>/cmem`,
`<ind>/clf`, `<ind>/cnd`, and the new declared/ok-indt / declared/ok-ctor
calls) and re-verify the abort is via the soundness audit (e.g.
`cnames-distinct` forcing reflexive `string-neq` for dup-ctor-iota).

**Still open: fuo prover (§3.2 completeness).**  The 28 currently-🩹
good tests come back when the prover synthesizes `field-universes-ok-
skip-params` witnesses instead of HOLEing them.  Same plan as before
(synth.ts walk producing defeq + mleq subgoals); now that §3.5 pins
NParams via `count-leading-foralls`, the prover has a well-grounded
skip count to consult.

### 3.2.2 fuo prover landed (2026-06-03)

The `buildFieldUniverses` function in `synth.ts` and a new `fieldUniverses`
method on `Prover` discharge the §3.2 obligation.  Strategy:

  1. Walk the ctor type's leading Π chain for the first `nParams` binders
     (= parent inductive's `numParams + numIndices`), introducing a HOAS
     `([x][h] ...)` pair under each `field-universes-ok-skip-params/skip`.
  2. For each remaining binder (real field): synthesize `defeq A A (esort
     UA)` via existing `synthRec` (with `reduceToSort` fallback when the
     synth result isn't literally a sort), then `proveMleq UA UInd 0`
     (Carneiro's algorithmic ≤, already implemented).  Emit
     `field-universes-ok/forall <dom> <mleq> ([x][h] body)`.
  3. At the not-forall result: `field-universes-ok/done <not-forall/...>`.

**Arena scoreboard after fuo prover** (145 tests):

- Good: **48 ✅** / 35 🩹 / 10 ❌  (+23 tests, from 25/58/10).
- Bad: 17 ✅ / 33 🩹 / **2 💥** — see "regression" below.

**count-leading-foralls semantics fix.**  While wiring up the fuo prover
I hit an interesting bug.  The §3.5 design had `count-leading-foralls T
N` as an "exactly N" judgment, with the inductive's `NParams` payload
set to `numParams + numIndices` (so Eq with numParams=1, numIndices=2
got NParams=3).  But the ctor side wants to skip only `numParams`, not
`numParams + numIndices` — Eq.refl has 2 leading Πs (α, a), not 3.
So I relaxed `count-leading-foralls T N` to an "at least N" judgment
and pinned the indt's `NParams = c.numParams`.  This still blocks the
§3.2.2 over-claim attack: a translator that claims `NParams = 5` for a
3-binder inductive type runs out of binders before reaching `liz` and
the count-leading-foralls witness fails to inhabit.

**Soundness regression on `066_BogusRecursor` + `large-elim-imax-prop`**.
Pre-fuo, every ctor HOLE'd on `fuo`, which sank the entire inductive
declaration (the `declared/ok-ctor` failed without all premises filled).
That HOLE was *incidentally* masking the §3.1 recursor-type gap: with
the ctor declined, the recursor's `declared/ok-irec` lookup failed too,
and the bad recursor type never got into `declared`.  With fuo now
filled, ctors are admitted, the inductive is admitted, and the bad
recursor is admitted — exposing the §3.1 gap on the corpus again.

This is **not a regression** in the strict sense (these tests were
always 💥-eligible; the §3.2 HOLE was a false-negative cover), and the
fix is §3.1, the next architectural piece in the plan.  No
hand-written soundness regression in `lf/soundness/` is affected.

**Net** on the corpus, post-fuo: +22 good tests pass, 2 bad tests
re-expose their (pre-existing) §3.1 status as 💥.  Soundness check
trades a *masked* false-negative for a *visible* one — strictly more
honest reporting.

### 3.2.3 declared/ok catch-all guard (2026-06-03)

**Finding from the companion adversarial process.** When the soundness
regressions were migrated to the new payloaded `dkind` API
(`indt Ctors NParams`, `ctor IndN Cidx`, `irec IndN`), three of them
*re-exposed* their soundness gaps because **`declared/ok`'s `K` was
unconstrained** — every soundness premise on the specialized rules
(`declared/ok-indt`, `-ctor`, `-irec`) was optional, since the catch-all
could seal `indt _ _` / `ctor _ _` / `irec _` directly.  In particular:

  * `dup-ctor-iota.elf` was sealing its dup-list inductive via
    `declared/ok` → cnames-distinct never demanded → dup iota
    double-fires → literal `False`.
  * `universe-too-high-field.elf` similarly bypassed the
    field-universe check via `declared/ok` on the ctor.

**Fix.**  A new closed predicate `dkind-non-inductive K` (inhabited only
for `defn _`, `thm _`, `opq _`, `ax`, `quot`) gets added as a premise to
`declared/ok`.  Inductive-family `K`s have no `dkind-non-inductive`
witness available, so the catch-all rule fails to apply — forcing those
declarations through the specialized sealing rules where the audit
premises live.

```twelf
dkind-non-inductive : dkind -> type.
dkind-non-inductive/defn : dkind-non-inductive (defn V).
dkind-non-inductive/thm  : dkind-non-inductive (thm V).
dkind-non-inductive/opq  : dkind-non-inductive (opq V).
dkind-non-inductive/ax   : dkind-non-inductive ax.
dkind-non-inductive/quot : dkind-non-inductive quot.

declared/ok :
   name N (is-decl T K)
   -> dkind-non-inductive K
   -> dkind-ok K T
   -> declared N T K.
```

Translator supplies the witness via the matching constructor when
emitting each non-inductive-family decl.  Closed family — no thaw, no
external posit — so the audit is local (no global `%query` needed).

**Effect on scoreboard.**  None on the arena corpus (the catch-all
bypass was a hand-written attack vector, not something the trusted
generator exercises).  Hand-written `lf/soundness/`: `dup-ctor-iota.elf`
and `universe-too-high-field.elf` were both rewritten to the
post-migration API and now `💥`-eligible *had the guard not landed*;
with the guard, both genuinely ABORT (verified by inspection of the
abort location — line 36 / line 28 respectively, on the missing
`dkind-non-inductive` witness).

**Remaining hand-written 💥 candidate**:

  * `rec-name-slot.elf` — `declared/ok-indt` requires `name MRec
    (is-rec-for N)`, but the translator's MRec is unconstrained.  A
    translator picking `"Foo.evilrec"` instead of canonical `"Foo.rec"`
    satisfies the premise, and `def Foo.rec` then doesn't collide.
    Pure-LF fix needs string concat or a name-shape built-in — see
    §3.3's "why we don't pursue full canonicality" note.  Best practical
    fix: surface the translator's canonicality as a TCB-side `%query`
    audit on the rec-name string, paralleling the string-neq pattern.

### 3.1.1 §3.1 landing (2026-06-03)

§3.1 lands as a *minimum-soundness, partial-completeness* fix.  The
`dkind-ok/irec` rule now takes 5 premises:

```twelf
dkind-ok/irec :
   defeq T T (esort URecType)                          %% well-formed
   -> name IndN (is-decl IndType (indt Ctors NParams))  %% parent lookup
   -> ends-in-sort-with-level IndType UInd              %% extract UInd
   -> enum-rec-type T IndN lnil Ctors U                 %% canonical schema
   -> le-eligible UInd Ctors U                          %% large-elim restriction
   -> dkind-ok (irec IndN) T.
```

Plus a new closed family `le-eligible UInd Ctors U` (encoding the
subsingleton / non-prop / prop-prop case split via `mleq` on the level
sides, so imax-disguised UInd and U both normalize through).

**Closes**:

  * `lf/soundness/large-elim-prop.elf` — ≥2-ctor Prop with motive
    targeting `Sort u`: `le-eligible` has no rule matching this case
    (non-prop fails because `mleq 1 lzero 0` is false; prop-prop fails
    because the motive sort `lvar liz` doesn't ≡ lzero).  ✅ rejected.
  * `arena bad/066_BogusRecursor.ndjson` — recursor's claimed type is
    `Sort 0`, not the canonical `∀ M m t, M t`: `enum-rec-type` fails
    structurally.  No witness → recursor declines (`🩹`).  From the
    arena's perspective, decline on a bad-test is a pass.
  * `arena bad/large-elim-imax-prop.ndjson` — same as `large-elim-prop`
    via imax-disguised UInd (`limax 1 0`), which `mleq` correctly
    normalizes to `lzero`.  Declines (`🩹`).

**Scope (Phase 1)**: `enum-rec-type` only covers ctors with zero fields
on non-parametric, non-level-polymorphic, non-indexed inductives.  Every
inductive outside that shape (Eq, Nat, List, Acc, TwoBool's recursor,
And, Prod, …) has no `enum-rec-type` witness and its recursor declines.
The translator pre-checks shape via `enumShaped =
indType.numParams === 0 && indType.numIndices === 0 &&
indType.levelParams.length === 0 &&
ctorsForInd.every((c) => c.numFields === 0)`; if false, emit a HOLE on
the frozen `declared` family rather than a wrong-shape `enum-rec-type/intro`
witness (which would 🔴-reject at the render step).

**Arena scoreboard after §3.1** (145 tests):

- Good: **28 ✅** / 55 🩹 / 10 ❌  (down from 48/35/10 in §3.2.2).  The
  20 lost goods are recursors of shapes outside the phase-1 scope.
- Bad: 17 ✅ / 35 🩹 / **0 💥** — soundness gap closed.
- All 7 hand-written `lf/soundness/` regressions still ✅.

**Phase 2 path** (to recover the lost good ✅): generalize
`enum-rec-type` to a `rec-canonical-schema` family covering more
inductive shapes — non-recursive ctors with fields (TwoBool, And),
recursive ctors (Nat, List), parametric inductives, level-polymorphic
inductives, and finally indexed inductives (Eq).  Each shape is a
distinct LF rule in the family.  Bounded incremental work.  Not in
scope for this session.

**Updated soundness scoreboard** (2026-06-03 end of session, **post-§3.1**):

| File | Verdict | Closes via |
|---|---|---|
| `arena tutorial/bad/066_BogusRecursor.ndjson` | 🩹 declines | §3.1 done (enum-rec-type fails structurally) |
| `arena bad/large-elim-imax-prop.ndjson` | 🩹 declines | §3.1 done (le-eligible fails via mleq) |
| `lf/soundness/large-elim-prop.elf` | ✅ rejected | §3.1 done |
| `lf/soundness/rec-name-slot.elf` | 💥 accepted | §3.3 (research-level, see below) |
| `arena bad/field-too-high-imax.ndjson` | 🩹 declines | §3.2 done + catch-all guard |
| `lf/soundness/universe-too-high-field.elf` | ✅ rejected | §3.2 + catch-all guard |
| `lf/soundness/dup-ctor-iota.elf` | ✅ rejected | §3.4 + catch-all guard |
| `lf/soundness/rec-slot-theft.elf` | ✅ rejected | pre-existing |
| `lf/soundness/level-var-elim-false.elf` | ✅ rejected | pre-existing |
| `lf/soundness/positivity-underabstraction.elf` | ✅ rejected | pre-existing |

### 3.2.1.old Status as of 2026-06-03 — partial landing

**Landed in this session.** `lf/tcb.elf` now carries
`ends-in-sort-with-level`, `not-forall`, `field-universes-ok`, and
`field-universes-ok-skip-params`. `dkind-ok/ctor` requires the new
premises. All four new families are frozen in `freeze.elf`. The translator
in `src/generate-twelf.ts` synthesizes the structural `eisl` witness
inline (a mechanical walk via `buildEisl`) and emits a bare-HOLE
declaration for the `fuo` witness on the now-frozen
`field-universes-ok-skip-params` family.

**Arena verdict after the change** (145 tests):

- Good: 25 ✅ / 58 🩹 / 10 ❌ — *28 previously-✅ tests dropped to 🩹*
  (the expected cost of the soundness ratchet; recovers when the fuo
  prover lands, below).
- Bad: 17 ✅ / 35 🩹 / **0 💥** — soundness gap closed on the corpus.
- Hand-written `lf/soundness/`: `universe-too-high-field.elf` aborts
  cleanly (the file uses the *old* `dkind-ok/ctor` signature, which no
  longer type-checks); `large-elim-prop.elf` also aborts for the same
  reason (its ctors fail the signature change), though §3.1's `rec-
  schema-canonical` is what actually closes the large-elim gap. (A file
  that updates the ctor invocations to the new signature would re-expose
  the large-elim soundness gap; the field-universes check is orthogonal.)
- `rec-name-slot.elf` still 💥 — §3.3 work, not on this critical path.

**Still open: fuo prover (planned for the next session).** The HOLE on
every ctor's `fuo` is what's dropping 28 good tests. To recover them, a
new Prover method (`fieldUniverses`) walks the ctor type, synthesizes
each field's `defeq A A (esort UA)` via existing `synth.synthRec`
machinery, and accumulates `mleq UA UInd 0` subgoals to be emitted as
top-level `%solve` directives (mleq is decidable per §7.1; closed level
expressions only, so the %solve never depends on LF binders).

The prover's job is structural with one moving piece — the recursion
under LF binders for each Π — and Twelf's `%solve` handles the per-field
`mleq` cheaply.  Estimated: a day's work in `synth.ts`, plus the wiring
through `prover.ts` + a small generator change to emit the witness
inline instead of a HOLE.

### 3.2.2 NumParams-bypass — §3.2 has a hole until §3.5 lands

**Finding (2026-06-03).** The `NumParams` argument of
`field-universes-ok-skip-params` is a translator-supplied `lidx` with
nothing in the TCB constraining it to match the inductive's actual
leading-Π count.  An adversarial translator can *over-claim*
`NumParams`, in which case the rule's `/skip` case consumes the
would-be-field's Π binder as a "param" and the `field-universes-ok/forall`
mleq check never fires on it.

**Concrete probe** (out-of-tree, `/tmp/numparams-bypass.elf`).  Re-derives
the `universe-too-high-field.elf` attack under the new `dkind-ok/ctor`
signature, but claims `NumParams = (lis liz)` (= 1) for an inductive
with no params:

```twelf
TooHigh_mk/fuo : field-universes-ok-skip-params (lis liz)
                   (eforall (esort (lsucc lzero)) ([x] (econst "TooHigh" lnil)))
                   (lsucc lzero)
   = field-universes-ok-skip-params/skip
       ([x] [h] (field-universes-ok-skip-params/start
                  (field-universes-ok/done (not-forall/const "TooHigh" lnil)))).
```

This loads CLEAN through `final-checks.elf` — `TooHigh.mk` is admitted
despite its field-universe violation.  So §3.2 as landed doesn't actually
close the field-universe gap against an adversarial translator; it only
catches *honest* translators that report the correct param count.

**Why this is a §3.5 problem.**  The bypass is the same shape as §3.4's
dup-ctor and §3.3's rec-name-slot: a piece of inductive-family wiring
(the param count) is translator-supplied free metadata, not stored on
the inductive's reservation and not consulted at check time.  §3.5's
Tier 2 lists `numParams`/`numIndices` as exactly this — dropped
relational metadata.  Closing it requires the same architectural move
§3.4/§3.5 prescribe: pull `numParams` onto the inductive's `is-decl`
payload (or somewhere `%unique name` pins it), and have
`dkind-ok/ctor`'s skip-params consult the inductive's reservation
rather than accept a free argument.

**Stopgap until §3.5 lands.**  We could constrain `NumParams` by
deriving it from `IndType` structurally: a `count-leading-foralls
IndType N` judgment forces `N` to match the inductive's actual leading-Π
count.  Composed with the existing `ends-in-sort-with-level IndType
UInd` premise, this would close the over-claim path without waiting on
the full §3.5 reservation refactor.  Trade-off: bolt-on, won't survive
the §3.5 restructure cleanly.  Worth doing if §3.5 is more than a
session away; skip if §3.5 is next on the agenda.

### 3.3 Recursor-name slot (the `rec-name-slot.elf` finding)

**The attack.** `lf/soundness/rec-name-slot.elf` declares `inductive Foo`
*without* reserving `name "Foo.rec" (is-rec-for "Foo")` — only the trusted
generator emits that reservation; a hand-written file may omit it — then
declares `def Foo.rec : Type 0 := Foo`. The TCB accepts; Lean rejects (the
recursor slot is reserved by elaboration regardless of source-text).

**Not a soundness bug.** The resulting environment has a definition named
`Foo.rec` and an inductive `Foo` with no recursor. That's weird but it
doesn't construct a proof of False. The motivation to fix it is
spec-compliance: every Lean env our TCB admits should be one Lean would
also admit.

**What the rec-slot-theft regression already buys us.** A *companion*
hand-written file `lf/soundness/rec-slot-theft.elf` is already passing
(rejected): it declares `inductive Foo` *and* a rec-name reservation
`name "Foo.rec" (is-rec-for "Foo")`, then attempts to declare a junk
`def Foo.rec` whose `name "Foo.rec" (is-decl T (defn V))` clashes with
the reservation under `%unique name +N -K`.  Two different `nkind`s for
the same string → ABORT.  So the global mechanism that catches the attack
is *already in place* in the TCB; what's missing is the guarantee that
the rec-name reservation always exists at all.

That reframes the problem.  We don't need to *constrain the rec-name
string* to be `<ind>.rec` (which would require LF-level string concat —
see "String-concat in LF" below for why that's a dead end).  We only need
to **require that an inductive's declaration come with some `is-rec-for`
reservation**.  The translator emits the canonical `<ind>.rec` by
convention; `%unique` does the rest.

**Concrete fix.**  Split `declared/ok` into a separate
`declared/ok-indt` (parallel to the existing `declared/ok-irec`) that
takes the rec-name reservation as a premise:

```twelf
declared/ok-indt :
   name N (is-decl T indt)
   -> name MRec (is-rec-for N)         %% rec-name slot reserved (some MRec)
   -> dkind-ok indt T
   -> declared N T indt.
```

`MRec` is a translator-chosen string.  The premise demands *some*
`is-rec-for N` reservation exists; without one, no `declared N T indt`
witness can be constructed and the inductive declaration is rejected.
That closes `rec-name-slot.elf` directly — Foo declares no reservation,
so no `declared "Foo" _ indt` is provable.

**What this does *not* close.**  A malicious translator that picks
`MRec = "FooWeirdName"` (not the canonical "Foo.rec") would still get
through, with the env's recursor slot at the weird name and `def
Foo.rec` proceeding as an unrelated definition.  That's *not* a
False-route: the kernel doesn't perform iota-reduction on `def
Foo.rec` because it isn't reserved as a recursor; the env is just
internally inconsistent with Lean's naming convention.  Spec-compliance
loss, soundness preserved.

**Why we don't pursue full canonicality.**  Pinning `MRec = "<N>.rec"`
in pure LF would require a `string-cat` family with a `%query`-style
audit, paralleling §3's `string-neq` discipline.  But unlike
`string-neq` (where `%query 0 * string-neq X X` decides the audit by
reflexive pattern-match, no string introspection required), a posited
`string-cat N ".rec" M` claim is *unverifiable* without inspecting the
strings' characters.  We can't catch a lie like
`string-cat "Foo" ".rec" "FooWeirdName"` with a closed Twelf query.
Bringing real string structure into the TCB (strings as cons-lists of
characters) would solve it but is a major refactor with pervasive
fallout.  The translator-side audit ("the trusted generator emits
canonical `<ind>.rec`") is what we lean on instead.

**Recommendation.**  Land `declared/ok-indt` with the rec-name premise
alongside §3.1's `dkind-ok/ctor` restructure (they both touch
`declared`-family rules).  Cost: ~10 LF lines, one matching change in
the translator (emit `Foo/decl = declared/ok-indt Foo/name Foo/rec-name
(dkind-ok/indt …)`), audit `generate-twelf.ts` to confirm the canonical
rec-name reservation is always emitted.  Result: `rec-name-slot.elf`
ABORTs, the canonical-name story stays "translator-audited" without
needing string concat, and the `rec-slot-theft` mechanism keeps
catching the dual attack as before.

### 3.4 Duplicate-constructor iota gap (the `dup-ctor-iota.elf` finding)

**The attack.** The enum iota rules are split by *position*
(`defeq/iota-enum-2-first`/`-second`, `-3-first/second/third`, …), and
`enum-rec-type`/`enum-rec-body` walk the supplied ctor list structurally — with
**no distinctness check**. So declare `B : Type` with one real ctor `B.a`, but a
recursor `B.rec : {M} → M B.a → M B.a → (t) → M t` whose `enum-rec-type` lists
`[B.a; B.a]`. `dkind-ok/irec` accepts the type (it's well-formed), and then
`iota-enum-2-first` (its `C1 = B.a`) gives `B.rec M m₁ m₂ B.a ≡ m₁` while
`iota-enum-2-second` (its `C2 = B.a`) gives `… ≡ m₂` — *same LHS*, so
**`m₁ ≡ m₂`** for arbitrary minors. With `m₁ = true`, `m₂ = false`:
`defeq Bool.true Bool.false Bool`; a `decode = Bool.rec (fun _ => Prop) True False`
plus congruence then yields `defeq True False`, and `True.intro` inhabits
`False`. `lf/soundness/dup-ctor-iota.elf` carries this all the way to a literal
`falseProof : False` — the strongest of the soundness regressions.

**Root cause (see §3.5).** The recursor's authoritative reduction rules
(`recInfo.rules`: one `{ctor, nfields, rhs}` per ctor) are dropped in
translation; the TCB *reconstructs* iota positionally from the recursor type's
minor chain. A duplicated ctor in that chain makes two per-position rules fire
on one ctor application. Lean's own `rules` (one per `cidx`) never duplicate, so
this only bites adversarial input — exactly the threat model.

**Arena-boostability: NOT today, but LATENT-live.** The generator currently
emits **no iota witnesses at all** (`iota`/`defeq/extra`/`enum-rec-type` occur in
zero `lf/tests/*.full.elf` and nowhere in `generate-twelf.ts`/`synth.ts` — only a
stale `parse.ts` comment; the "stage-1 enum iota working" claim elsewhere is out
of date). So every iota-dependent proof HOLEs and declines (`boolRecEqns`,
`nRecReduction`, … are all `🩹`), and an ndjson can't drive this collapse to an
accept — it declines (⊘). The only arena-reachable residue is Twelf accepting a
dup-*minor* recursor *declaration*, which is the same `dkind-ok/irec` gap §3.1
already covers. **But** the moment stage-1 enum-iota *generation* lands, this
flips to live + arena-boostable (a real proof-of-`False` from an ndjson).

**Fix.** Require the ctor list to be pairwise-distinct, via the existing
`string-neq` posit + global `%query 0 * string-neq X X` audit: a duplicate forces
a reflexive `string-neq C C`, which sinks the load. Enforce it on the list
`enum-rec-type` consumes — ideally the list *derived from the inductive's
reserved ctor set* (§3.5), not a free premise. **Sequencing constraint: this
must land before (or with) enabling iota generation**, or turning iota on
re-opens the hole.

### 3.5 Common root: the NDJSON→LF translation drops the inductive family's relational metadata

§§3.1–3.4 are, at bottom, **one omission**. Compare an NDJSON declaration to its
`.render.elf` image: the render keeps each declaration's **type** (+ value for
`defn`/`thm`/`opq`) and a **kind tag**, and discards the *structural metadata*
Lean's kernel uses to know how an inductive family's pieces fit together. Because
`.render.elf` is the moral (NullProver) view that structurally contains
everything `.full.elf` does, **a field absent from the render is one no prover
can recover** — it is simply not translated into any checkable LF fact. Auditing
the render against the NDJSON schema is therefore the precise lens for "what
invariants are we unable to check," and the dropped fields *are* those
invariants.

Dropped fields, by soundness priority:

**Tier 1 — the inductive family's wiring (one gap, three faces):**

- **recursor `rules`** (per-ctor `{ctor, nfields, rhs}` iota equations) — the
  authoritative ctor→minor→rhs map. Dropped; iota reconstructed positionally
  from the recursor type (root of §3.4, and means the recursor's *computational
  behavior* is never checked against Lean's).
- **constructor `cidx`** (canonical 0-based index) — the authoritative position
  that should pin which minor a ctor maps to. Dropped; minor↔ctor falls back to
  name/list-position.
- **inductive `ctors`** (the constructor set) — dropped; no exhaustiveness, no
  "these are the only ctors" (§3's spurious-ctor / exhaustiveness gap).

  These are the *same* omission: the LF stores each declaration's type but throws
  away **which ctors belong to which inductive, in what order, which minor each
  maps to, under which reduction rule.** Lean constructs that wiring and checks
  it; the TCB reconstructs it positionally from types. The fix is one family
  (the `name`/`%unique` reservation discipline): carry the ctor set onto the
  inductive (`indt Ctors`), `cidx`+`induct` onto each ctor, and have the
  recursor/iota rules *consult* that wiring — with the distinctness audit of
  §3.4 — instead of reconstructing positionally.

**Tier 2 — soundness-relevant but latent / deferred:**

- **recursor `k`** (K-like reduction eligibility, e.g. `Eq.rec`) — dropped; once
  iota lands, K-reduction must fire only when `k = true` and only for legitimate
  subsingletons.
- **inductive `isReflexive` / `isRec` / `numNested`** — govern which
  positivity/recursor forms are legal (reflexive, nested); deferred, so latent.
- **inductive `numParams` / `numIndices`** — the param/index split. Used by the
  *translator* preflight (`checkCtorStructure`) but not stored in LF, so not
  re-checkable there; the split itself is the dropped datum (not recoverable from
  the type alone).

**Tier 3 — recoverable from the type or not soundness-relevant:**

- ctor `numFields` / `numParams` — recoverable by counting Πs given the split.
- def `hints` (regular/abbrev) — reducibility only; the `defn`/`opq` tag already
  captures the delta-relevant distinction.
- `isUnsafe` / `safety = partial` / `all` (mutual blocks) — translator
  rejects/defers, so moot.

**Adjacent (same shape, worth its own audit):** structure **projections**
(`eproj StructName fieldIdx e`) need the structure's field list/types to type
soundly — the same "structure metadata" omission as the ctor set, for `proj`
rather than `rec`. `proj-of-prop` exercises one corner; whether field *types* are
pinned vs trusted deserves the same check.

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
actually rejected via its LF-encoded checks.

**Current full-corpus snapshot** (143 tests, 2026-06 arena run):

- **Good (93 tests):** 53 ✅ / 30 🩹 / 10 ❌
- **Bad  (50 tests):** 17 ✅ / 32 🩹 / **1 💥** (`066_BogusRecursor` — see §3.1)
- All 3 hand-written soundness regressions in `lf/soundness/` are still
  correctly ABORTed.

The previously-celebrated "10 migrations" from translator-decline to
Twelf-decided rejection are still in place. The session that wrote the
arena-submission story did not regress them; it surfaced the BogusRecursor
gap that the prior corpus did not stress.

**For the arena interface specifically** (different verdict mapping; see
`arena-submission-plan.md` §3):

- ✅ (54 tests) → exit 0 (accept) — *1 of these is wrong: `066_BogusRecursor`*
- 🩹 / 🤷 / 🔴 (81 tests) → exit 2 (decline)
- ❌ (8 tests) → exit 1 (reject) — *all 8 are correct*

The arena cares only about (correct-accept, correct-reject, decline,
wrong-accept, wrong-reject). It will report us as 53 correct accepts, 17
correct rejects, 81 declines, 1 wrong accept (the soundness gap), 10 wrong
rejects (good tests we couldn't verify and refused to claim accept on).

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

There are now two distinct project obligations on the TCB, with very
different costs and very different consequences for missing them:

**A. Soundness.** The TCB must not admit an env Lean would have rejected.
The arena run found exactly one such admission (`066_BogusRecursor`, §3.1).
Other tests with `expect: reject` that we currently mishandle are *declines*
(🩹), not soundness failures — the kernel refused to claim accept on them.

A separate finding (`047`, addressed in May 2026 via `string-neq`) hardened
the encoding for under-abstracted `T_HOAS` positivity attacks. That work
sets the pattern for §3.1: a translator-side construction is allowed to
*posit* facts, and the TCB's closed rules + a global audit (e.g. `%query`,
`%unique`) make a lie fatal.

**B. Completeness.** The TCB must admit every env Mario's spec admits. The
arena run quantifies the gap as 30 holes-on-good-tests + 19 generator
declines on good tests = 49 out of 93 good-tests we don't accept (47%).
This is the work the rest of this document tracks.

The pre-arena framing collapsed both into "complete the TCB" and assigned
them comparable urgency. The arena run separates them: closing §3.1 (and
auditing for other §7.3 "trusted-export" assumptions that the arena's
threat model invalidates) is a *prerequisite* for taking the kernel
seriously as a checker; completeness is a quality metric on top.

The "complete the TCB" obligation, taken alone, is finite and tractable.
The items in §5 are a finite list; ticking each off is well-defined work,
not research. Once they're all ticked, we'd have a TCB that's declaratively
complete relative to Mario's spec — meaning any Lean environment that the
spec accepts, our TCB has a proof for.

What we'd give up by not pursuing completeness: the ability to say "the
translator failing means Lean shouldn't have accepted this either". With
gaps remaining, a translator failure can mean either (a) Lean shouldn't
have accepted it, (b) we just don't have the rule, or (c) the translator
search heuristic gave up. Closing the TCB-completeness gaps reduces (b)
to ∅.

What we don't get even after closing them: a decision procedure. The
translator can still time out, give up, or fail to find a proof that exists.
That's an explicit non-goal — we're OK with handing off to a
human/LLM/external procedure in the gap. The closure of the TCB just
guarantees those handoffs are well-posed: the proof exists somewhere in the
LF signature, the question is just whether someone (us, them, something
else) can find it.

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

### 7.3 `lean.mm1` borrows + the inductive-acceptance soundness gaps

Carneiro's `lean.mm1` is a _complete_ declarative spec of the same `IsDefEq`;
where our TCB is partial it reads as a checklist. No bug found in rules we
already check; the gaps are exactly the inductive-acceptance checks §3 marks
missing/💥 — recursor well-formedness, ctor field-universe, ctor-set
exhaustiveness. These are **soundness bugs**, not incompleteness: the TCB must
perform these checks itself, and `066_BogusRecursor` / `large-elim-prop`
already exhibit inputs that exploit their absence. The same audit applies to
the two siblings below.

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
