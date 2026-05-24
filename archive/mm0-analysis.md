# Metamath Zero vs. Twelf-as-LF: a comparison for the Twelf Lean kernel

What this document is: a comparison of two "specification languages for
logics" as applied to Lean's type theory — Twelf/LF (used the way Appel's
Foundational Proof-Carrying Code work uses it) and Metamath Zero (MM0), via
Mario Carneiro's `lean.mm1`
([digama0/mm0](https://github.com/digama0/mm0/blob/master/examples/lean.mm1)).
The goal is practical: identify what `lean.mm1` says about gaps and soundness
risks in our TCB (`lf/tcb.elf`), and how to borrow from it.

`lean.mm1` is the MM0 analog of lean4lean's _declarative_ spec
(`Theory/Typing/Basic.lean`) — the same `IsDefEq` relation our TCB targets.
The difference is that `lean.mm1` is essentially complete, and our TCB is (by
its own accounting in `completeness-plan.md`) partial; that asymmetry is the
useful content here.

## 1. The two frameworks

The two systems sit at opposite ends of one axis: **how much the framework
gives you for free vs. how small the trusted checker is.**

### Twelf / LF (the FPCC use)

The relevant approach here is **Appel & Felty's**: LF is used purely as a
proof-representation and proof-_checking_ framework. An object logic
(higher-order logic + a machine's operational semantics) is encoded as LF
type-family constructors; a safety proof _is_ a well-typed LF term; and
checking a proof is LF type-checking — nothing more. Crucially, **the full
Twelf system is deliberately kept out of the trusted base.** Appel's group
intended proofs to be checked by a comparatively tiny dedicated LF checker
([flit](https://github.com/standardml/twelf/tree/main/src/flit)), so that
Twelf's elaboration and metatheory machinery (`%mode` / `%worlds` / `%total` /
`%covers` / `%unique`) is _not_ on the checking path and _not_ trusted. The
trusted base is just: a tiny LF type-checker + the signature. The acknowledged
cost is that **adequacy must be argued by hand.**

The leverage comes from LF's dependent function space, all of which a tiny LF
checker gets natively:

- object-level binders become LF binders (HOAS),
- capture-avoiding substitution is meta-level β-reduction,
- α-equivalence is free,
- a typing context is just the LF context.

> **This project follows Appel & Felty, not Crary & Sarkar.** Crary & Sarkar
> took the opposite road — conducting the safety argument _inside_ the Twelf
> metalogic and relying on `%total`-style metatheoretic reasoning as part of
> the trusted account. We explicitly do **not** want that: no `%mode` /
> `%worlds` / `%total` / `%covers` reasoning in the kernel's checking path.
> Most Twelf documentation describes the Crary–Sarkar style; the agent should
> stay focused on the Appel & Felty style and treat metalogic tooling as off
> the trusted path by default. (§3.6 says what metatheorems _are_ good for.)

This is exactly what this project does: Lean's type theory is an LF signature;
a Lean environment becomes an LF signature; checking = LF type-checking.

The TCB is `tcb.elf` plus the LF checker — but note the checking path
currently relies on two pieces of Twelf machinery _beyond_ pure LF
type-checking, both used in a deliberately simple, non-metatheoretic way:

1. the open-world discipline that an environment may extend the signature
   _only_ with new `declared` constants (everything else is a `def`), and
2. `%unique declared …` to enforce the functional dependency of a Lean name on
   its declaration.

Neither is metatheoretic reasoning. `%unique` in particular is a very powerful
piece of program-analysis machinery being used in a very simple way — just to
check a functional dependency. The honest way to see both items: they are
checks we would need to **add to a flit-style tiny checker** if we wanted to
move off the full Twelf binary and onto a minimal trusted checker. They belong
to the same category as "only `declared` may be extended" — small, decidable
side-conditions on the signature, not `%total`-style proofs.

### Metamath Zero

MM0 is in the Metamath tradition: sorts, term constructors, and
axioms-as-inference-rules, where a proof is a tree of axiom applications under
substitution. It is **not** a dependent type theory. The design goal is the
most extreme version of the FPCC "small trusted checker" idea — a verifier
small enough to be formally verified down to machine code, with the heavy
lifting done by an unverified frontend (MM1, a Scheme-like metaprogramming
language) that _emits_ MM0 proofs the tiny verifier rechecks.

`lean.mm1` is written in MM1; the `focus` / `have` / `'(…)` are MM1 tactics,
but only the elaborated MM0 artifact is trusted.

Because MM0 doesn't hand you LF's meta-level substitution, `lean.mm1` must
**reify substitution** as object-level judgments:

- `subst: A [e / x] = B` for expressions,
- `l_subst` for levels,
- `substIS` for inductive specs,

complete with explicit α-conversion (`subst_lambda_alpha`, `subst_Pi_alpha`).
In our TCB those judgments don't exist: `defeq/beta` writes the result as the
LF application `(Body E')`, and `defeq/eta` uses `[x] eapp F x` directly.

**That single difference — substitution as meta-level β (Twelf) vs. a reified,
axiomatized relation (MM0) — is the cleanest way to see the two
personalities.**

### Where MM0 sits relative to FPCC-Twelf

| Axis                   | Twelf / LF                                                                                                                                      | Metamath Zero                              |
| ---------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------ |
| Framework class        | Dependent type theory (λΠ)                                                                                                                      | Many-sorted, Metamath-style; not dependent |
| Binding / substitution | HOAS; meta-level β; α free                                                                                                                      | Reified object-level relation; α explicit  |
| Typing context         | LF context                                                                                                                                      | Explicit `ctx` (`nil` / `cons`)            |
| Metalogic tooling      | `%total` / `%worlds` / `%covers` exists, but **off the trusted checking path** (Appel & Felty); used only for confidence _about_ the TCB (§3.6) | None — checks proofs only                  |
| Trusted checker (goal) | A tiny LF checker (flit), **not** the full Twelf binary; plus the small `declared`/`%unique` side-conditions                                    | Tiny, formally verified verifier           |
| Adequacy               | Argued by hand                                                                                                                                  | Argued by hand                             |

MM0 is in some sense the logical endpoint of the FPCC "minimize the trusted
checker" goal, at the cost of LF's conveniences. Both are declarative specs of
Lean's `IsDefEq`; `lean.mm1` is complete where our TCB is partial.

## 2. Soundness: does `lean.mm1` reveal problems in our TCB?

Two-part answer: **no outright bug in the rules we currently check**, but
`lean.mm1` precisely fills in the checks we currently delegate to "we trust
the export" — and those are the ones that flip from _incomplete_ to _unsound_
the moment the trust assumption weakens.

### 2.1 The reassuring part

The core `defeq` rules are faithful transcriptions of Carneiro's spec and
match `lean.mm1`:

- `defeq/beta`, `defeq/eta`, `defeq/lam`, `defeq/app`, `defeq/conv` — all
  check out, including the `Γ ⊢ e : α := Γ ⊢ e ≡ e : α` reflexivity-is-typing
  convention.
- `defeq/proof-irrel` correctly gates on `esort lzero` (Prop), matching
  `lean.mm1`'s `proof_irrel` (`G |- p : Prop`).
- `dkind-ok/thm` correctly forces theorem types to be Prop.

The `lvl-eq` algebraic rules were each checked individually against Lean's
level semantics — `max-idem`, `max-zero-{l,r}`, `max-succ`, `imax-succ`,
`imax-zero`, the congruences, and especially `imax-idem` (whose TCB comment
gives the right case split: `imax L L = 0` if `L = 0`, else `max L L = L`).
**Each rule is valid.** So our level theory is _sound but incomplete_: an
incomplete level equality only loses completeness, never soundness, as long as
no individual rule is wrong — and none is.

The strict-positivity no-occur HOAS trick is sound for the single-self
non-nested fragment as claimed, and the documented limits (nested, mutual)
**fail closed** — they make valid declarations unprovable rather than
accepting bad ones. That is the correct failure direction. The only residual
risk is translator-side (if `T_HOAS` abstracts the inductive incorrectly),
which is a translator-adequacy question, not a hole in the rule.

### 2.2 The "trusted-export" checks `lean.mm1` makes explicit

`completeness-plan.md` §3 already names these as "✗ … we trust the export."
`lean.mm1` shows exactly what is being trusted:

- **Universe consistency of constructor fields.** `lean.mm1`'s `ctor_Pi`
  carries `l2 <=l l` (each non-recursive field's sort ≤ the inductive's sort);
  `ctorR_S` carries `l_imax l2 l <=l l` for recursive arguments. Our TCB
  checks only `defeq T T (esort U)`. Lean's kernel enforces these inequalities
  during inductive elaboration; omitting them is fine for trusted Lean output
  but is a soundness hole against arbitrary signatures.

- **Large-elimination / subsingleton eligibility.** The big one. `lean.mm1`
  has the full `LE` / `LE_ctor` / `LE_mem` apparatus deciding whether a
  Prop-valued inductive may eliminate into `Type` (`LE_Prop`, `LE_Type` gated
  on `L1 <=l l`, `LE_1`, `LE_ctor_Pi_Prop`). Our plan lists this as missing.
  Allowing large elimination out of a non-subsingleton Prop is a classic route
  to a closed proof of `False`. Enum recursors (stage 1) haven't hit it
  because they're trivial; `lean.mm1` states the gate precisely.

- **Recursor type well-formedness.** `lean.mm1` _synthesizes_ the recursor
  type (`Rec_kappa`, `Rec_alpha`, `Rec_beta`, `Rec_epsilon`) and checks it; we
  accept whatever the export gives. Worse, our iota rules
  (`defeq/iota-enum-*`) fire on a `declared … irec` whose type only has to
  match the `enum-rec-type` schema — so iota soundness currently _leans on_
  the export having supplied a genuine recursor rather than a schema-shaped
  lookalike. `enum-rec-type` is specific enough that the room is small, but
  `lean.mm1` closes it structurally by tying iota (`conv_iota` →
  `iota_epsilon`) to the synthesized recursor.

### 2.3 Where `lean.mm1` will _not_ help

`lean.mm1` has function eta (`conv_eta`) only — **no projection term and no
structure-eta** for one-constructor inductives. Our `eproj` is likewise
representation-only with no rules. For structure-eta and projection reduction,
the reference to follow is lean4lean's kernel `Structure` handling, not this
file.

### 2.4 Framing

`lean.mm1` formalizes the rules and demonstrates them on sample inductives via
MM0 `def` / `theorem`; it does **not** ingest and check an arbitrary exported
environment. Our TCB is trying to be both that declarative spec _and_ an
executable environment checker (via `declared` + the translator). So coverage
comparison is "complete spec" vs. "partial spec + checker" — which is exactly
why `lean.mm1` reads as a checklist of what's left to encode rather than a
competitor. (If it did read like a competitor that would be fine — we're all
friends here and it's good to have different approaches to the same material.
We should borrow what we can, but it's excellent that we've developed what we
have starting from a relatively fresh perspective.)

## 3. How to exploit `lean.mm1` (ranked by leverage)

1. **Steal the level-comparison decision procedure.** `lean.mm1`'s
   `l_pl u a <= v b` offset relation + `l_pl_cases` (case-split each universe
   variable into `0` / `S x`, with `l_pl_imax_*` for the imax algebra) is
   exactly a decision procedure for `VLevel.Equiv` — i.e. the "eval over a
   finite test set" alternative sketched in `completeness-plan.md` §2. Porting
   it closes the entire `lvl-eq` incompleteness section in one move, stays
   sound (still derivability-based, each rule checkable), and also fixes the
   `t-const` diagonal limitation once levels compare up to equivalence.
   **Highest-value borrow.**

2. **Treat `lean.mm1` as the executable spec for the three trusted-export
   checks.** Port `ctor_Pi` / `ctorR_S` universe side-conditions (field-sort
   and imax constraints) and the `LE` / `LE_ctor` / `LE_mem` large-elimination
   gate into the TCB. Even before wiring them into the translator, encoding
   them removes the trust assumption and hardens the kernel against
   non-Lean-produced signatures.

3. **Use Nat and List as golden targets for iota stages 2–5.** `ty_nat_rec` +
   `nat_succ_iota` are the template for a recursive inductive with no
   parameters; `ty_list_rec` + `list_cons_iota` for a parameterized one with a
   recursive field. Watch how the inductive hypothesis threads: `Rec_beta_rec`
   produces the `D -> e3` motive slot, and `iota_beta_rec` feeds the
   recursor's own result back in (`v1 @ v`). Implement the LF iota rules so
   the Twelf analog of `list_cons_iota` goes through and you've effectively
   reached stages 2–3.

4. **Port Quot, propext, choice directly.** `lean.mm1` gives exact types for
   all four Quot constants (`ty_quot`, `ty_quot_mk`, `ty_quot_sound`,
   `ty_quot_lift`) and the primitive reduction `quot_iota`
   (`quot_lift … (quot_mk … a) = f a`). Our plan lists Quot as "missing
   entirely"; this is a near-mechanical port — four `declared`-style
   constants + one `defeq-extra` rule — and similarly for `propext` / `choice`
   if the corpus reaches them.

5. **Apply the substitution-premise translation discipline.** The main
   impedance mismatch. _Do not_ copy `subst` / `l_subst` / `substIS` — they
   exist only because MM0 lacks LF β. Rule of thumb when porting any
   `lean.mm1` rule: **delete every `subst: A [e/x] = B` premise and replace
   `B` with the LF application `(λx. A) e`.** The α-conversion premises
   (`subst_lambda_alpha`) vanish on the Twelf side. The one place to stay
   alert is _level_ instantiation at const-use sites: if you reify const
   re-instantiation (the `defeq/const-lvl-cong` rule the plan sketches) rather
   than getting it from LF, `l_subst_S` / `l_subst_max` / `l_subst_imax` show
   the shape you need.

6. **Keep metatheorems out of the kernel as much as possible — but know the
   one legitimate use.** The checking path stays pure LF type-checking (Appel
   & Felty); do **not** reach for `%total` / `%worlds` / `%covers` as part of
   how the kernel decides whether an environment is well-formed. The
   legitimate use of a Twelf metatheorem here is narrow: to prove a
   relationship _about_ the TCB that raises **human** confidence without
   entering the trusted path. The motivating example is level equivalence — if
   we keep two characterizations in the TCB (say, the current algebraic
   `lvl-eq` and the borrowed `l_pl`-style decision procedure from §3.1, each
   convenient for different derivations), a metatheorem that the two judgments
   coincide is worth having. But that metatheorem lives **outside `tcb.elf`**
   — it is a statement _about_ the TCB, not a rule _in_ it. Both judgments it
   relates are in the TCB; the proof of their equivalence is not, and would
   generally be low priority for our project. That is the only register in
   which `%total`-style machinery should appear in this project, and even then
   it is confidence-raising scaffolding, never a trusted check. The way we're
   currently using `%unique` is fine — it patches hole that we couldn't fill
   otherwise. If there are other ways in which Twelf's machinery can be
   adopted to serve us that's absolutely worth considering. It just shouldn't
   be the first tool we reach for.

## References

- `lean.mm1` — Carneiro, MM0 Lean formalization:
  https://github.com/digama0/mm0/blob/master/examples/lean.mm1
- Appel & Felty, _Foundational Proof-Carrying Code_ — LF as a proof-checking
  framework with a tiny trusted checker (the approach this project follows):
  https://www.cs.princeton.edu/~appel/papers/fpcc.pdf
- `flit` — the small dedicated LF proof checker, kept separate from the full
  Twelf system: https://github.com/standardml/twelf/tree/main/src/flit
- Appel, Michael, Stump & Virga, _A Trustworthy Proof Checker_, and Wu &
  Appel, _Foundational Proof Checkers with Small Witnesses_ — on minimizing
  the LF checker that sits in the trusted base.
- Appel, _Hints on Proving Theorems in Twelf_:
  https://www.cs.princeton.edu/~appel/twelf-tutorial/
- Crary & Sarkar, _Foundational Certified Code in a Metalogical Framework_
  (CADE-19, 2003) — the **contrast** case: safety conducted _inside_ the Twelf
  metalogic, relying on `%total`-style reasoning. Useful to recognize so as to
  avoid it; this project does not take this road.
- Carneiro, _The Type Theory of Lean_ (2019), and lean4lean
  `Theory/Typing/Basic.lean` — the `IsDefEq` spec the TCB targets.
