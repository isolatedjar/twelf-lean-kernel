# TCB-completeness checklist

What this document is: a tick-box accounting of how much of Mario's
declarative specification of Lean's type theory our TCB encodes. The
specification is `VEnv.IsDefEq` (Figure 1 of the lean4lean paper,
implemented in `Lean4Lean/Theory/Typing/Basic.lean`) plus the inductive
and quotient extensions added via `t-extra`.

**What "TCB-complete" means here.** For every defeq fact that holds in
Mario's declarative relation, there exists an inhabitant of the
corresponding LF type in our signature. **Translator-completeness is a
separate question**: given a TCB-complete signature, can our translator
find the witness? We are explicitly OK with the translator failing to
find proofs (it's a heuristic search), as long as the witness exists for
someone or something else — human, LLM, decision procedure — to construct.

## Architecture: derive, don't check

The trusted side of the project is a Twelf encoding of Lean's declarative
type theory, plus a small translator that turns lean4export NDJSON into
LF declarations.  The untrusted side is a prover that tries to discharge
proof obligations the translator raises.  The trust boundary is the
generator file `src/generate-twelf.ts`, the parser `src/parse.ts`, the
shared types/interfaces in `src/shared.ts`, and the three audited LF
files `lf/tcb.elf`, `lf/freeze.elf`, `lf/final-checks.elf`.

**The kernel-derived declarations are *not* env-supplied.** Lean's export
format includes redundant information that the kernel itself derives from
other declarations: every inductive's recursor (one or more, plus the
recursion rules), and the four constants of the Quot family.  An honest
kernel-checker rederives these from first principles rather than
checking what the export supplies — see PR #46 on the arena repo for
the upstream consensus.  Our translator follows the "rederive" stance:

* **Recursors do not appear in `.render.elf`.** The TCB has a closed
  family `rec-derived "<ind>" T_canonical` whose only inhabitants are
  constructed from the inductive's reservation (`name "<ind>" (is-decl
  IndType (indt Ctors NParams))`) and the ctor reservations.  Iota
  rules consume `rec-derived` directly.  The translator emits a
  Twelf-comment-block representation of the lean4export-supplied
  recursor types/rules in `.render.elf` for human readability, but no
  load-bearing `declared` entry.
* **Quot's four constants do not appear in `.render.elf`.** The TCB has
  a closed family `quot-derived` with four constructors, one per
  Quot/Quot.mk/Quot.lift/Quot.ind, each with the canonical type baked
  in.  The translator skips Quot declarations entirely (apart from a
  banner comment).

**The essential metadata that *does* appear** in `.render.elf`:

* **Inductive declarations** — name, type, level params, NumParams, full
  cidx-ordered ctor list (`Ctors`).
* **Constructor declarations** — name, type, parent inductive's name,
  cidx within parent.
* **def / thm / opaque / axiom** declarations as before.

Soundness of the inductive family hinges on what's on this list, audited
by the TCB rules in §3.  Anything not on this list (recursors, Quot,
iota equations, structural eta) is either derived by the TCB or
synthesized by the prover with TCB-side audits.

## Status

The current scoreboard, against the lean-kernel-arena's tutorial + named
singleton corpus (145 tests), is in flux while the derive-canonical
pivot lands.  Verify with a fresh `check-tests.sh` + `check-soundness.sh`
before quoting.

What's stable:

* The defeq core (§1) — all of Mario's Figure 1 rules except the partial
  cases listed below.
* The level-equality decision procedure (§2) — `mleq` decides the
  variable-free fragment + universe-variable elimination via
  `mleq/var-elim`.
* The inductive-family essential-metadata checks (§3) — `cnames-distinct`
  (no duplicate ctors), `cmem` (ctor membership in parent's list),
  `field-universes-ok` (each field's sort ≤ inductive's sort),
  `count-leading-foralls` (NParams matches inductive's leading-Π count).
* The `declared/ok` catch-all guard via `dkind-non-inductive` — every
  inductive-family kind must go through the specialized sealing rules
  (`declared/ok-indt`, `declared/ok-ctor`); `declared/ok` covers only
  defn/thm/opq/ax/quot.

What's open:

* Phase 2 of the recursor derivation (§3.6) — generalize `rec-derived`
  from the current enum-only scope (no params, no indices, no level
  params, no ctor fields) to broader inductive shapes (non-recursive
  fields, recursive fields, parametric, indexed).  Each shape is one
  rule in the family.
* `t-const` level-poly congruence (§1.1) — same-level diagonal only.
* Quot's primitive `lift∘mk` rule (§1.2) — TCB has the four constants
  but not the iota rule yet.
* Structural eta for one-ctor inductives (§1.2).

## 1. The core defeq judgment (paper Figure 1)

Mario's judgment is `Γ ⊢_{E,n} e ≡ e' : α`, with implicit reflexivity
(`Γ ⊢ e : α` defined as `Γ ⊢ e ≡ e : α`). We map this onto our
`defeq E1 E2 A`, treating the LF context as the typing context (each
`{x : expr} defeq x x A -> ...` binder corresponds to a `Γ, x : α`
extension).

| Paper rule                                         | Our TCB                                         | Status                                            |
| -------------------------------------------------- | ----------------------------------------------- | ------------------------------------------------- |
| `l-zero`, `l-succ`, `t-bvar`                       | LF context lookup + α-equivalence               | ✓ adequate                                        |
| `t-symm` / `t-trans` / `t-conv`                    | `defeq/symm` / `/trans` / `/conv`               | ✓                                                 |
| `t-sort`                                           | `defeq/sort-eq` via `lvl-eq`                    | ✓ (see §2 for `lvl-eq` completeness)              |
| `t-all` / `t-lam` / `t-app`                        | `defeq/forall` / `/lam` / `/app`                | ✓                                                 |
| `t-beta` / `t-eta`                                 | `defeq/beta` / `/eta`                           | ✓                                                 |
| `t-const`                                          | `defeq/const` (via `declared`)                  | ✗ partial — same-level diagonal only; see §1.1    |
| `t-proof-irrel`                                    | `defeq/proof-irrel`                             | ✓                                                 |
| `t-extra` δ (defn unfolding)                       | `defeq/delta`                                   | ✓                                                 |
| `t-extra` iota (recursors)                         | `defeq-extra` + per-shape iota rules            | ✓ stages 1-2 (enum + non-rec fields); ✗ 3+ (§3.6) |
| `t-extra` structural eta (one-ctor inductives)     | —                                               | ✗ missing entirely (§1.2)                         |
| `t-extra` Quot primitive `lift∘mk`                 | —                                               | ✗ missing entirely; TCB has the four constants    |

### 1.1 `t-const` partial coverage

Mario's full rule:

> Given `ū.(c_ū : α) ∈ E` and `∀i. n ⊢ ℓᵢ, ℓ'ᵢ ok ∧ ℓᵢ ≡ ℓ'ᵢ`, conclude
> `Γ ⊢ c_{ℓ̄} ≡ c_{ℓ̄'} : α[ū ↦ ℓ̄]`.

The `ℓᵢ ≡ ℓ'ᵢ` premise allows the two instantiations to be different
level expressions, provided they're defeq as levels. Our `defeq/const`
handles only the diagonal (same `LS` on both sides):

```twelf
defeq/const :
   declared N Ts DK
   -> inst-expr Ts LS T
   -> defeq (econst N LS) (econst N LS) T.
```

To get `defeq (econst N LS) (econst N LS') T` for `lvls-eq LS LS'` we'd
need a `defeq/const-lvl-cong` rule that propagates the lvls-eq through
the instantiation.  Practical impact: any time the same polymorphic
constant appears with provably-equal-but-not-syntactically-equal level
args on two sides of a defeq, we can't close the gap.  Example:
`id.{max u v} α` vs `id.{max v u} α` — Mario sees these as equal; we
don't.

### 1.2 Missing `t-extra` cases

Iota for recursors is partially landed — see §3.6 for the rec-derived
family + Phase 2 plan.  The two remaining cases:

* **Structural eta for one-ctor `Foo`**: one rule per such Foo, of
  shape `defeq (Foo.mk (π₁ x) ... (π_n x)) x Foo`.  Requires the TCB to
  identify the ctor and the projection set.  Future work; not currently
  scoped.
* **Quot's primitive rule**: `defeq (Quot.lift f h (Quot.mk r a))
  (f a) α`.  One rule, gated on the four `quot-derived` constants.
  Future work; the `quot-derived` constants are present (§3.5), the iota
  rule is the missing piece.

## 2. Level equality (`lvl-eq`) completeness

Mario's `ℓ ≡ ℓ'` is *extensional*: defined by `⟦ℓ⟧_v = ⟦ℓ'⟧_v` for every
assignment `v : ℕ → ℕ` of nat values to universe variables.

**Status: closed** by the `mleq` decision procedure.  Carneiro's
algorithmic level inequality (Type Theory of Lean thesis, p.7) — the
offset relation `mleq L L' N` meaning `⟦L⟧ ≤ ⟦L'⟧ + N` for every
valuation — replaces the old reactive table of algebraic rules.
`lvl-eq L L'` is recovered as two-sided `mleq L L' 0 ∧ mleq L' L 0`
(via `lvl-eq/le`); `lvl-eq` has only `refl` and the `mleq` bridge.

The 15 structural rules (the thesis' 13 + the two RHS-imax simplification
duals needed once an offset puts the imax on the right) decide the
variable-free fragment — associativity, commutativity, distributivity,
max/imax zero/succ/idempotence — which the old table had to special-case
one law at a time.  The prover (`synth.ts`, `proveMleq`) supplies a
concrete integer offset at every step, so Twelf only *checks* ground
`N±1` / `N >= 0` constraints (via the `inequality/integers` domain),
never solves for them.  The `N >= 0` premises of `mleq/lz` and
`mleq/self` are discharged by the same `%solve nonneg_<n>` witnesses
the generator emits for nat literals.

**Universe variables: closed via first-order variable elimination.**
The thesis' 14th rule eliminates a universe variable by case-split
`u ↦ 0` / `u ↦ S u`.  Because our level variables are first-order de
Bruijn indices (`lvar : lidx -> lvl`), the case split is encoded
directly as `mleq/var-elim` using a first-order substitution judgment
`lvl-subst` and structurally-decidable index (dis)equality (no
posit-and-audit — unlike strings, `lidx` disequality is a genuine closed
judgment).  Soundness: `lvar I` ranges over ℕ = {0} ∪ {S k}, so a goal
holding with `I ↦ 0` and with `I ↦ S I` (whose still-free `I` is the
predecessor) holds for every valuation; substitution is exact by
construction, so the rule has no loophole.

The prover (`synth.ts`, `proveVarElim`) detects a variable blocking as
an `imax` second argument, case-splits it, recurses.  Closed examples
include `imax (imax u u) u ≡ imax (succ u) u` (Peano-style sort
equalities).  `mleq` is complete for the full fragment.

## 3. Inductive families: declarations + derived recursors

Lean's kernel performs structural checks on inductive declarations that
are NOT part of `IsDefEq`.  The post-pivot architecture splits these
into "essential metadata" (env-supplied, audited by the TCB) and
"derived from essential metadata" (TCB constructs the recursor + Quot).

The essential-metadata audits live on `declared/ok-indt` and
`declared/ok-ctor`.  The derived families live in §3.4 and §3.5.

| Check                                                     | Our TCB                          | Status                                       |
| --------------------------------------------------------- | -------------------------------- | -------------------------------------------- |
| Inductive type ends in `Sort _`                           | `ends-in-sort`                   | ✓                                            |
| NParams payload                                           | carried unchecked on `indt`      | ✓ no longer pinned — `field-universes-ok` checks all binders, no skip count to over-claim (`count-leading-foralls` removed 2026-06-06) |
| `cnames-distinct Ctors`                                   | premise of `declared/ok-indt`    | ✓ (via `string-neq` posit + global %query)   |
| `name MRec (is-rec-for N)` reserved by indt               | premise of `declared/ok-indt`    | ✓ MRec bound to the NDJSON's recorded `recs[].name`; canonicality (`MRec = N ++ ".rec"`) checked translator-side as a decline; see §3.3 |
| `cmem N Ctors` (ctor's name in parent's list)             | premise of `declared/ok-ctor`    | ✓                                            |
| Field-universe constraint (`field-universes-ok`)          | premise of `declared/ok-ctor`    | ✓ (translator-side prover fills `fuo`)        |
| Strict positivity                                         | `ctor-positive` + `no-self-ref`  | ✓ (single-self, non-nested)                  |
| Mutual / nested inductives                                | —                                | ✗ deferred                                   |
| Positivity modulo defeq                                   | —                                | ✗ deepest open issue                          |
| `declared/ok` catch-all guard                             | `dkind-non-inductive` premise    | ✓ blocks the inductive-family bypass         |

The recursor/Quot derivations occupy §3.4 / §3.5.

### 3.1 Inductive declaration

A `declared/ok-indt` witness has five premises:

```twelf
declared/ok-indt :
   name N (is-decl T (indt Ctors NParams))
   -> name MRec (is-rec-for N)
   -> count-leading-foralls T NParams
   -> cnames-distinct Ctors
   -> dkind-ok (indt Ctors NParams) T
   -> declared N T (indt Ctors NParams).
```

The translator emits, per inductive:

* `<ind>/name` — the open-name reservation carrying the `(indt Ctors
  NParams)` payload.
* `<ind>/rec-name` — `name "${recName}" (is-rec-for "<ind>")` where
  `recName` is the NDJSON's recorded `recs[].name` (verbatim, not
  synthesized).  Reserves the recursor's name slot; `%unique name` then
  catches a junk `def` colliding with the *actual* reserved name via the
  existing nkind-collision machinery.  The translator emits `%%% SKIP`
  if the recorded name isn't the canonical `<ind>.rec` (a translator-side
  decline, not a TCB rejection — see §3.3).
* `<ind>/clf` — `count-leading-foralls IndType NParams`, structural.
* `<ind>/cnd` — `cnames-distinct Ctors`, with leaves discharged by
  posited `string-neq` facts.
* `<ind>/eisl` — `ends-in-sort-with-level IndType UInd`, structural.
  Shared with both `declared/ok-ctor` and the derived recursor (§3.4).
* `<ind>/decl` — the sealed `declared`.

### 3.2 Constructor declaration

A `declared/ok-ctor` witness has six premises:

```twelf
declared/ok-ctor :
   name N (is-decl T (ctor IndN Cidx))
   -> name IndN (is-decl IndType (indt Ctors NParams))
   -> cmem N Ctors
   -> ends-in-sort-with-level IndType UInd
   -> field-universes-ok-skip-params NParams T UInd
   -> dkind-ok (ctor IndN Cidx) T
   -> declared N T (ctor IndN Cidx).
```

The translator emits, per ctor:

* `<ctor>/name`, `<ctor>/type-wf`, `<ctor>/positivity` — as for any decl.
* `<ctor>/cmem` — `cmem "<ctor>" Ctors`, the position-in-list witness.
* `<ctor>/fuo` — `field-universes-ok-skip-params NParams T UInd`,
  synthesized by `prover.fieldUniverses` (`buildFieldUniverses` in
  `synth.ts`).  Walks T's Π chain, skips the first `NParams` binders as
  the inductive's params, and for each remaining field synthesizes
  `defeq A A (esort UA)` plus `mleq UA UInd 0`.  Returns null (→ HOLE
  → freeze rejects → decline) when synthesis gives up.
* `<ctor>/decl` — the sealed `declared`.

`field-universes-ok-skip-params` is the §3.2 fix.  Its `NParams` is
pinned by `count-leading-foralls` on the indt side: an attacker that
over-claims `NParams` to make `/skip` consume real field binders runs
out of leading Πs in the inductive's type and the `count-leading-foralls`
witness fails to inhabit.

### 3.3 recursor-name canonicality — CLOSED

**Status (2026-06-06): closed via translator-side name threading + a
canonicality decline.**  The TCB doesn't pin a recursor's name; that was
never a soundness invariant.  The translator now carries the NDJSON's
recorded `recs[].name` verbatim into the `<ind>/rec-name` reservation,
and emits a `%%% SKIP` when that name diverges from the canonical
`<ind>.rec` (not a representable Lean kernel env in practice, even
though sound at the TCB level).

**Old framing (superseded).** `declared/ok-indt` requires `name MRec
(is-rec-for N)` for *some* MRec, unconstrained.  The worry was that an
adversarial translator picks a non-canonical MRec (`"Foo.evilrec"`),
leaving `"Foo.rec"` free for a junk def, and that closing this needs a
string-shape predicate (`N ++ ".rec" = MRec`, no LF primitive) or a
posit-and-audit on concatenation.  `rec-name-slot.elf` was filed 💥 on
this basis.  **This is the wrong model** — see below.

**Finding (2026-06-06): the inductive↔recursor binding is already
explicit in the NDJSON, by containment.**  lean4export emits one record
per inductive family — `{"inductive": {"types":[…], "ctors":[…],
"recs":[…]}}` — with the recursor(s) bundled in `recs`, each carrying its
own `name` and reduction `rules` that reference the family's own ctors.
In `lf/tests/030_boolType.json`:

```
"kind": "inductive",
"types":     [ { "name": ["Bool"], … } ]                 # the inductive   (lines 5–7)
"ctors":     [ ["Bool","false"], ["Bool","true"] ]        #                 (line 14)
"recursors": [ { "name": ["Bool","rec"],                  # recursor: bundled + named (lines 32–34)
                 "rules": [ {"ctor":["Bool","false"], …},  # rules ref Bool's own ctors (lines 80,113)
                            {"ctor":["Bool","true"],  …} ] } ]
```

(`parse.ts:141` `indRecSpec` has a `name` field; `parse.ts:179` `recs:
z.array(indRecSpec)` is a *sub-field of the `inductive` object*; the IR
keeps it bundled as `IndInductive.recursors`, `parse.ts:387`.)  So a
kernel reading the NDJSON never has to *infer* which recursor is Foo's,
nor *assume* it is named `Foo.rec`: containment answers "which recursor",
and `recs[].name` records the name verbatim.  The spec-level requirement
(Carneiro / lean4export) is only that Foo's recursor be **identifiable
and unique**, which containment already gives.  A non-canonical name is
at most a **decline** ("not recognizable canonical Lean"), never
unsoundness.

**Why the gap appears at all — the generator discards the bundling.**
`generate-twelf.ts:1021` emits

```js
emit(`${mn}/rec-name : name "${declName}.rec" (is-rec-for "${declName}").`);
```

It *re-derives* `<ind>.rec` from the inductive's name and ignores the
recorded `recs[].name` (consulted only for the preflight large-elim check
at `:825` and the human-readable comment at `:975`).  Flattening the
bundled recursor to a free `is-rec-for "<ind>"` reservation keyed on a
*synthesized* name is what manufactures the "must be `Foo.rec`"
obligation.  Note the `rec-name-slot` attack is **not even reachable
through the real pipeline**: the generator *always* reserves `<ind>.rec`,
so no exported environment produces the `Foo.evilrec` reservation —
`rec-name-slot.elf` is a hand-written-`.elf`-only artifact.

**What was implemented:**

1. *Generator.* `generateInductive` resolves the recursor for each
   type by NDJSON containment: for non-mutual (`ind.types.length === 1`)
   it's `ind.recursors[0]`; for mutual we fall back to a `<tname>.`
   prefix.  `generateIndType` then emits
   `<mn>/rec-name : name "${recName}" (is-rec-for "${declName}")` using
   that recorded name.  `tcb.elf` is unchanged.

2. *Canonicality decline.* Translator-side check: if the resolved
   recursor's name isn't `<declName>.rec`, emit `%%% SKIP` ("non-
   canonical recursor name") so the test classifies as a translator
   decline (🤷 = pass-on-reject for bad tests).  This is **not** a TCB
   premise — purely a courtesy for arena classification.

3. *Synth.* `buildEnvMap` parent-inductive lookup also uses containment
   (no name-suffix matching except as a mutual-family fallback).

4. *Soundness suite.* `rec-name-slot.elf` deleted (no longer a
   regression — its premise was wrong).  `rec-slot-theft.elf` continues
   to cover the genuine junk-def-steals-canonical-slot story via
   `%unique name`.

**Tests recovered:** 126_misnamed_rec (was 💥, now 🤷 → ✅ reject),
127_dup_rec_def2 (similar).  Scoreboard bad-column gained one 💥 → ✅
move.

### 3.4 Derived recursors (`rec-derived`)

**The TCB constructs each inductive's recursor; the translator never
supplies one.**  The closed family

```twelf
rec-derived : string -> expr -> type.   %name rec-derived RD.
```

has one constructor per inductive shape we support, where each
constructor's premises are the inductive's `declared` witness, the ctor
list, and any other essential metadata; and the conclusion's `expr` is
the canonical recursor type for that shape.

#### Phase 1 (current): enum-shaped inductives

An "enum-shaped" inductive has no params, no indices, no level params,
and every ctor has no fields.  Examples: `Empty`, `Bool`, `PropTwo`
(2-ctor Prop), 3-ctor enums.  The canonical recursor schema for an
enum-shaped `Foo` with ctors `c_1, …, c_n` is:

```
∀ (M : Foo → Sort U) (m_1 : M c_1) … (m_n : M c_n) (t : Foo), M t
```

The TCB encodes this via the existing `enum-rec-type` recognizer + a
single `rec-derived/enum` constructor:

```twelf
rec-derived/enum :
   declared IndN IndType (indt Ctors NParams)
   -> enum-rec-type T IndN lnil Ctors U
   -> le-eligible UInd Ctors U
   -> ends-in-sort-with-level IndType UInd
   -> rec-derived IndN T.
```

(`le-eligible UInd Ctors U` is the elimination-universe restriction:
≥2-ctor Prop may only large-eliminate to Prop.  See `tcb.elf` for the
case-split rules.)

Iota rules consume `rec-derived` instead of the old `declared <rec> _
irec`:

```twelf
defeq/iota-enum-2-first :
   rec-derived FooName RecType
   -> declared C1 (econst FooName lnil) (ctor FooName CidxC1)
   -> declared C2 (econst FooName lnil) (ctor FooName CidxC2)
   -> name FooName (is-decl _ (indt (ccons C1 (ccons C2 cnil)) _))
   -> defeq M M (eforall (econst FooName lnil) ([_] esort U))
   -> defeq Mp1 Mp1 (eapp M (econst C1 lnil))
   -> defeq Mp2 Mp2 (eapp M (econst C2 lnil))
   -> defeq-extra
        (eapp (eapp (eapp (eapp (econst "<ind>.rec" (lcons U lnil)) M) Mp1) Mp2)
              (econst C1 lnil))
        Mp1
        (eapp M (econst C1 lnil)).
```

(The recursor's name in the LHS — `"<ind>.rec"` — is recovered from
`FooName ++ ".rec"`, which we can't compute in LF.  Workaround: the
recursor's `econst` carries a *separate* name string; the iota rule
matches it by structural unification against `(econst RecName _)` where
RecName is bound by the rec-name reservation `name RecName (is-rec-for
FooName)`.  See `lf/tcb.elf` for the actual encoding.)

The legacy `declared/ok-irec`, `(irec IndN)` dkind variant, and
`dkind-ok/irec` rule are removed.

#### Phase 2: broader shapes

Each subsequent stage adds one `rec-derived/...` constructor (and
likely one or more new helper judgments paralleling `enum-rec-body`):

1. **Enums with ctor fields, non-recursive non-dependent** (TwoBool,
   And): minor type is `∀ a_1 … a_k, M (c a_1 … a_k)` — one
   universally-quantified binder grouping the field args under the
   motive application.  `enum-rec-body/minor-Nf` rule per field-count
   (N ∈ {1, 2} currently).  **Landed** — 057_twoBoolRec ✅.
2. **Level-polymorphic inductives** (PUnit.{u}, Eq.{u}): inductive's
   `(econst FooName FooLvls)` uses non-`lnil` FooLvls; the rec-name
   reservation already supports this — the schema needs `enum-rec-type
   T IndN FooLvls Ctors U` to accept arbitrary FooLvls (currently
   pinned to `lnil`).
3. **Recursive ctors** (Nat, List): minor type adds an IH binder per
   recursive field.  A field `a_i : Foo` produces `∀ a_i, ∀ ih_i : M
   a_i, ...` *inside* the minor's type (the minor itself remains a
   single binder).
4. **Parametric inductives** (List.{u}, Prod): inductive's `econst`
   carries non-trivial parameter args; the schema is parameterized
   over a parameter prefix.
5. **Indexed inductives** (Eq, Vec, Acc): motive's type has the
   indices bound before the type-of-the-major.
6. **Mutual / nested**: deferred — different family altogether.

Each stage is bounded LF transcription work, mostly straight from
Mario's spec.  Stages 3-5 should unlock ~20 currently-declining
recursor-using good tests in the arena corpus.

### 3.5 Derived Quot family (`quot-derived`)

The four Quot constants — `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` —
are *not* translator-input.  The TCB hardcodes them via:

```twelf
quot-derived : string -> expr -> type.

quot-derived/quot : quot-derived "Quot"      <canonical type> .
quot-derived/mk   : quot-derived "Quot.mk"   <canonical type> .
quot-derived/lift : quot-derived "Quot.lift" <canonical type> .
quot-derived/ind  : quot-derived "Quot.ind"  <canonical type> .
```

The canonical types are:

* `Quot      : ∀ (α : Sort u) (r : α → α → Prop), Sort u`
* `Quot.mk   : ∀ (α : Sort u) (r : α → α → Prop), α → Quot α r`
* `Quot.lift : ∀ (α : Sort u) (r : α → α → Prop) {β : Sort v} (f : α → β) (h : ∀ a b, r a b → f a = f b), Quot α r → β`
* `Quot.ind  : ∀ (α : Sort u) (r : α → α → Prop) {β : Quot α r → Prop} (h : ∀ a, β (Quot.mk α r a)) (q : Quot α r), β q`

The iota rules consume `quot-derived` directly:

```twelf
defeq/iota-quot-lift :
   quot-derived "Quot.lift" _
   -> quot-derived "Quot.mk"   _
   -> ... typing premises ...
   -> defeq-extra
        (eapp (eapp (eapp ... (econst "Quot.lift" ...)) ...) (eapp (econst "Quot.mk" ...) A2))
        (eapp F A2)
        ... .
```

The translator emits a `%%% Quot family (TCB-derived; not declared
here)` banner comment in `.render.elf` but no actual declarations.

### 3.6 Recursor / Quot in `.render.elf` and the translator

The translator's job for the kernel-derived names is informational
only.  `generate-twelf.ts`'s recursor loop emits, per recursor, a
*comment block* in `.render.elf` documenting the lean4export-supplied
type/rules — purely for human readability.  The same loop in
`.full.elf` emits the same comment block (no executable Twelf).

Example output:

```
%% recursor Bool.rec (TCB-derived; this block is informational only)
%%   type:   ∀ {u} (M : Bool → Sort u) (m_f : M Bool.false) (m_t : M Bool.true) (t : Bool), M t
%%   rules:  Bool.rec.{u} M m_f m_t Bool.false = m_f
%%           Bool.rec.{u} M m_f m_t Bool.true  = m_t
```

The structured fields (motive types, ctor refs, RHSes) come from the
NDJSON's RecursorVal and are rendered in a mangled Twelf/Lean hybrid
that's grepable without being parseable as LF.

**Trust property:** the comment block is not in the audit surface —
even if the translator misreports the supplied type/rules in the
comment, no Twelf check depends on it.  Auditing
`shared.ts + parse.ts + generate-twelf.ts` (the trust boundary) still
suffices.

## 4. Other parts of Mario's spec

* **`Δ ⊢ Γ ok`** (context well-formedness) — implicit in our LF context
  via the `{x : expr} defeq x x A -> ...` binder pattern.  Adequate.
* **`n ⊢ ℓ ok`** (level-param index in range) — we don't carry this
  explicitly; level params appear under first-order `lidx` and can't be
  misused.  Adequate.
* **VEnv well-formedness** — each `declared` carries its own
  `dkind-ok` proof; `%unique name` enforces the functional dependency
  on names.  Equivalent to Mario's per-decl WF + global injectivity.

## 5. Forward-looking gap list (ranked by impact)

Highest impact first.  "Impact" here is roughly: fraction of a real Lean
library this would unlock.

1. **§3.6 Phase 2: broader inductive shapes.** Bool/Empty/PropTwo work;
   the next wins are non-recursive ctor fields (And, Prod, Sum), then
   recursive ctors (Nat, List), then parametric inductives, then
   indexed (Eq).  Each shape is one LF rule and one translator-side
   recognizer.  Without this, every non-enum recursor declines and the
   downstream iota-using proofs decline with it.

2. **§1.2 Structural eta for one-ctor inductives.** Used by
   anonymous-constructor reasoning and proofs that rely on the eta law
   for records.  Encoding: one rule per such Foo of shape
   `defeq (Foo.mk (π₁ x) ... (π_n x)) x Foo`.  Requires tracking the
   projection set per inductive.

3. **§1.2 Quot primitive iota.**  The four `quot-derived` constants are
   in place (§3.5); the missing piece is the two iota rules
   (`Quot.lift f h (Quot.mk r a) ≡ f a` and `Quot.ind ...`).  Bounded
   work, similar to enum iota.

4. **§1.1 `t-const` level-poly congruence.** Probably rare in practice;
   adds a `defeq/const-lvl-cong` rule that propagates `lvls-eq` through
   instantiation.

6. **Mutual and nested inductives.** Deferred by choice; would require
   generalizing `ctor-positive` to a list of self-refs, and (for
   nested) a per-type-former "positivity-preserving" predicate.

7. **Positivity modulo defeq.** The deepest open issue: lifting
   `ctor-positive` through `defeq` stops being a closed-family
   operation.  Architectural; not in scope for this iteration.

## 6. Project plan

The post-pivot architecture has two distinct project obligations on the
TCB:

**A. Soundness.** The TCB must not admit an env Lean would have
rejected.  The derive-canonical pivot makes recursor-type and Quot
attacks structurally impossible (those entries aren't translator-input;
they're TCB-constructed).  The remaining soundness gates are on
inductive declarations (§3); §3.3 is closed (the canonicality concern
turned out to be translator-side, not a TCB invariant).

**B. Completeness.** The TCB must admit every env Mario's spec admits.
The dominant remaining gap is §3.6 (broader recursor shapes); §1.2's
structural eta and Quot iota also contribute.

Soundness is the higher priority; the §3.x sequence landed soundness
for the inductive-declaration shape and pivoted recursor/quot to a
correct-by-construction architecture.  Completeness work after that is
bounded incremental: each Phase 2 stage in §3.6 is one LF rule and one
translator recognizer.

## 7. Background — Carneiro's `mleq` algorithm

(Reference material for anyone touching the level-equality fragment.)

`mleq L L' N` meaning `⟦L⟧ ≤ ⟦L'⟧ + N` for every valuation — the
inference-rule algorithm from the thesis, transcribed into Twelf over
the integer constraint domain.  The 15 structural rules (current
`tcb.elf` numbering):

```twelf
mleq/lz       : N >= 0 -> mleq lzero L N.
mleq/self     : N >= 0 -> mleq L L N.
mleq/sL       : mleq L L' (N - 1) -> mleq (lsucc L) L' N.
mleq/sR       : mleq L L' (N + 1) -> mleq L (lsucc L') N.
mleq/maxR-l   : mleq L L1 N -> mleq L (lmax L1 L2) N.
mleq/maxR-r   : mleq L L2 N -> mleq L (lmax L1 L2) N.
mleq/maxL     : mleq L1 L N -> mleq L2 L N -> mleq (lmax L1 L2) L N.
mleq/imax-lzL : mleq lzero L N -> mleq (limax L1 lzero) L N.
mleq/imax-lzR : mleq L lzero N -> mleq L (limax L1 lzero) N.
mleq/imax-lsL : mleq (lmax L1 (lsucc L2)) L N -> mleq (limax L1 (lsucc L2)) L N.
mleq/imax-lsR : mleq L (lmax L1 (lsucc L2)) N -> mleq L (limax L1 (lsucc L2)) N.
mleq/imax-imL : mleq (lmax (limax L1 L3) (limax L2 L3)) L N
                  -> mleq (limax L1 (limax L2 L3)) L N.
mleq/imax-imR : mleq L (lmax (limax L1 L3) (limax L2 L3)) N
                  -> mleq L (limax L1 (limax L2 L3)) N.
mleq/imax-mxL : mleq (lmax (limax L1 L2) (limax L1 L3)) L N
                  -> mleq (limax L1 (lmax L2 L3)) L N.
mleq/imax-mxR : mleq L (lmax (limax L1 L2) (limax L1 L3)) N
                  -> mleq L (limax L1 (lmax L2 L3)) N.
```

Universe-variable elimination (the 14th rule) via `mleq/var-elim` +
`lvl-subst` — see §2.  `lvl-eq L L'` is recovered as
`lvl-eq/le : mleq L L' 0 -> mleq L' L 0 -> lvl-eq L L'`.
