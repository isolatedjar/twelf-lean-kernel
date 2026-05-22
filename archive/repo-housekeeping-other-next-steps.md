# Plan: Render pass ("moral Twelf") + repo housekeeping

## Research note: name-usages NOT captured by Lean's `Declaration` type

Question: are there name-usages in Lean not captured by `Declaration` (lean4
`src/Lean/Declaration.lean`) or Mario's encoding? Findings:

`Declaration` constructors: `axiomDecl`, `defnDecl`, `thmDecl`, `opaqueDecl`,
`quotDecl` (payload-free!), `mutualDefnDecl`,
`inductDecl (lparams, nparams, types, isUnsafe)` where each `InductiveType`
carries `ctors : List Constructor` (name + type). `Expr` name-bearing
constructors: `const declName us`, `lam/forallE/letE` (binderName — cosmetic),
`proj typeName idx struct`, `lit (natVal | strVal)`, `fvar`/`mvar` (not in
closed kernel terms).

Name-usages that a per-`Declaration` encoding does NOT fully capture:

1. **Quot family** — `Declaration.quotDecl` carries _no payload_. The kernel
   injects `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, `Quot.sound` with
   hardcoded types (they appear as `ConstantInfo.quotInfo (QuotVal …)` only
   after the kernel adds them). Any `Expr.const "Quot.mk" …` references a name
   whose type is kernel-builtin, not in the input declaration. Mario's
   `lean.mm1` makes these explicit via `term quot/quot_mk/quot_lift …` + type
   axioms `ty_quot`, `ty_quot_sound`, etc.

2. **Literal-reduction names** — `lit (natVal n)` / `lit (strVal s)` carry no
   names but the kernel's literal extension references a fixed set: `Nat`,
   `Nat.zero`, `Nat.succ` (+ `Nat.add/mul/sub/div/mod/pow/beq/ble/…` for
   computation); `String`, `String.mk`, `List.nil`, `List.cons`, `Char.ofNat`,
   `Char`, `List`. None appear syntactically in the literal Expr — they're
   hardwired into the kernel and must exist as ordinary declarations for the
   reductions to typecheck.

3. **Recursors** — `Declaration.inductDecl` provides types + constructors but
   NOT recursors; the kernel synthesizes `Foo.rec` (+ its rules) from the
   inductive (it surfaces as `ConstantInfo.recInfo`). So `const "Foo.rec" …`
   resolves to a name with no `Declaration` constructor. (lean4export _does_
   serialize recursors explicitly, so our NDJSON already carries them — but
   the bare `Declaration` type does not.)

4. **`proj typeName idx`** — references a structure (inductive) name + numeric
   field index, not a named projection function. The name resolves to a
   declaration, but the projection's reduction needs the structure's single
   constructor — captured only indirectly.

Cosmetic / non-kernel: `lam/forallE/letE` binderNames (alpha-irrelevant),
`fvar`/`mvar` (open terms only), `mdata`.

**Relevance to adequacy:** a faithful `.render.elf` must account for (1)–(4)
beyond just echoing declarations — especially Quot (no input payload) and the
literal/`proj` reduction dependencies, which today's
`enatlit`/`estrlit`/`eproj` constructors carry as opaque data with no link to
the names they depend on.

## What is actually wrong with 124_dup_rec_def2

Confirmed from the NDJSON + lean4lean source. The test declares:

- `def dup_rec_def2.rec : Type := Prop` (name 3)
- inductive `dup_rec_def2` (name 1), ctor `dup_rec_def2.mk` (name 4), recursor
  exported as `dup_rec_def2.original_rec` (name 2).

All four names are distinct, so `%unique declared` (keyed on the declared
name) never fires → file wrongly accepted.

**Root cause:** Lean's kernel generates the recursor name _fresh_ as
`mkRecName indName = indName ++ "rec"` (lean4lean `Inductive/Add.lean`:
`let name := mkRecName indType.name`; "recursors are generated fresh … not
supplied by the user"). So adding inductive `dup_rec_def2` reserves
`dup_rec_def2.rec` **no matter what** — the export naming the recursor
`original_rec` is adversarial (a real kernel never names it that). The
`def dup_rec_def2.rec` then collides with the kernel-reserved
`dup_rec_def2.rec`. Our checker trusts the export's recursor name and doesn't
model the implicit `.rec` reservation, so it misses the clash.

(Note: when the recursor _is_ named `Foo.rec` normally, a conflicting
`def Foo.rec` is already caught — both emit `declared "Foo.rec"`, tripping
`%unique declared`. The gap is _only_ when the recursor name is hidden/ wrong,
leaving the implicit `.rec` reservation unmodeled.)

## Evaluation of the `name-kind` design

**Verdict: it makes sense and catches #124, with caveats.**

How it catches #124:

- inductive `dup_rec_def2` reserves
  `name "dup_rec_def2.rec" (is-rec-for "dup_rec_def2")`
- `def dup_rec_def2.rec` reserves `name "dup_rec_def2.rec" is-declaration`
- `%unique name +S -1K` (analogous to `%unique declared`) sees string
  `"dup_rec_def2.rec"` reserved with two different `name-kind`s → ABORT.

Mechanism is sound: `%unique`/`%mode`/`%worlds () (name _ _)` mirror the
existing `declared` closure in `lf/final-checks.elf`. Two top-level `name`
constants with the same string but different kind make uniqueness false,
exactly how `%unique declared` catches duplicate declarations.

**Caveats / things to resolve:**

1. **`name` is currently `%abbrev name = string`, used as a _term_ type** in
   `econst : name -> lvls -> expr`, `declared : {N : name} …`, etc. Making
   `name` a `type` family (`string -> name-kind -> type`) breaks all those
   term positions. Either (a) replace term-level `name` with `string`
   everywhere and repurpose the identifier `name` for the reservation family,
   or (b) keep `name = string` and give the reservation family a distinct name
   (e.g. `reserved`/`name-resv`). (b) is a much smaller diff; (a) matches the
   proposal's wording.

2. **Forcing the inductive to reserve `<ind>.rec`** (the proposal already
   flags this). The `indt` dkind must carry a
   `name "<ind>.rec" (is-rec-for "<ind>")` proof. Two options for the `.rec`
   string:
   - **translator-trusted**: emit the literal `"dup_rec_def2.rec"`. Simple,
     but a buggy/malicious translator could reserve the wrong string and evade
     the check.
   - **Twelf-verified**: emit `("<ind>" ++ "rec")` using the
     `equality/strings` constraint domain's `++` and let the solver prove it
     equals the reserved literal. Sounder; needs a quick spike to confirm
     Twelf evaluates ground string concatenation.

3. **`is-builtin` may not pull its weight.** Literal-reduction names (`Nat`,
   `Nat.succ`, `String.mk`, …) are normally _real_ declarations
   (`is-declaration`), so they don't need a separate builtin kind for
   reservation. `is-builtin` might only matter once we model the
   literal/`proj` reduction dependencies (the "second step").

4. **Recursor↔family linking is only half-forced.** The def-collision path
   catches #124, but to _force_ a recursor to be named `<ind>.rec` for its
   family in general, you'd also want "each `is-rec-for X` family has exactly
   one rec name" — a uniqueness in the other direction (`+kind -string`),
   which is awkward. Out of scope for #124; note as a follow-up.

5. **Wide but mechanical TCB+translator change.** Every `dkind` constructor
   gains reservation argument(s); every `dkind-ok/*` and the translator's emit
   paths thread them; `final-checks.elf` gains
   `%mode`/`%worlds`/`%unique name`. No new test artifacts needed (render.elf
   untouched, per the user).

## Implementation plan: name-reservation system (artifact-gap step 1)

**Goal:** model the implicit "inductive `Foo` reserves `Foo.rec`" rule so
`124_dup_rec_def2` is rejected, via a name-reservation family with a Twelf
`%unique` functional dependency. No `.render.elf`/`render-cli.ts` changes
(deferred to step 2). Validated by five Twelf spikes (see below).

### Validated design (deviates from the literal sketch in 3 ways)

1. **`is-rec` is payload-free**, NOT `is-rec-for : string -> name-kind`. A
   string payload in the _kind_ puts a non-ground variable in the
   `%mode name +S -K` output ("Occurrence of variable Ind in output not
   necessarily ground" — Twelf can't run string deconcatenation). The
   inductive↔recursor string link is carried in the _string index_ instead
   (the `(N ++ ".rec")` concat), which Twelf evaluates forward fine.
2. **The reservation family is open with ground per-declaration constants
   only** (exactly like `declared`). Generic constructors
   (`mk-rec-resv : {Ind} resv (Ind ++ ".rec") …`) make `%unique` report a
   _static_ overlap for every file (false positive). Spikes confirm: ground
   constants → `%unique` points at the specific colliding constants.
3. **Reservations live in the `dkind-ok` rules with a threaded
   `{N : string}`**, not in the `dkind` constructors, so the reservation's `N`
   is forced equal to the `declared` name. The recursor (`irec`) reserves
   **nothing** — the inductive owns the `.rec` slot. (`%unique` flags _any_
   two constants sharing a string, even same-kind, so a self-reserving
   recursor would false-positive against the inductive's slot.)

`is-rec-name`/string-concat _verification_ as a separate judgment is **not
needed for step 1**: `dkind-ok/indt` requiring `name (N ++ ".rec") is-rec`
(with `N` = the declared inductive name) already forces the concat.

### TCB changes — `lf/tcb.elf`

- Replace `%abbrev name = string.` Repurpose `name` as the reservation family;
  every current term-level `name` becomes `string`:
  - `econst : string -> lvls -> expr.`
  - `declared : {N : string} …`, `ctor-positive : string -> …`,
    `ccons : string -> cnames -> cnames.`, the iota rules' `name` args, etc.
    (mechanical rename across the file; generated `.elf` already use string
    literals so they're unaffected).
- Add:

  ```twelf
  name-kind : type.
  is-declaration : name-kind.
  is-rec         : name-kind.
  is-quot        : name-kind.
  %% is-builtin   : name-kind.   %% reserve for step 2 (literals); unused now

  name : string -> name-kind -> type.   %% open; ground per-decl constants only
  ```

- Thread `N` through `dkind-ok` and require reservations per kind:
  ```twelf
  dkind-ok : string -> dkind -> expr -> type.
  dkind-ok/defn : defeq T T (esort U) -> defeq V V T
               -> name N is-declaration -> dkind-ok N (defn V) T.
  dkind-ok/thm  : … -> name N is-declaration -> dkind-ok N (thm V) T.
  dkind-ok/opq  : … -> name N is-declaration -> dkind-ok N (opq V) T.
  dkind-ok/ax   : … -> name N is-declaration -> dkind-ok N ax T.
  dkind-ok/ctor : … -> name N is-declaration -> dkind-ok N ctor T.
  dkind-ok/indt : … -> name N is-declaration
               -> name (N ++ ".rec") is-rec -> dkind-ok N indt T.
  dkind-ok/irec : … -> dkind-ok N irec T.            %% no reservation
  dkind-ok/quot : … -> name "Quot" is-quot -> … -> dkind-ok N quot T.
  ```
- `declared` passes `N` to `dkind-ok`:
  `declared : {N : string}{LS}{T}{K} dkind-ok N K T -> type.`

### Global check — `lf/final-checks.elf`

Add alongside `%unique declared`:

```twelf
%mode name +S -K.
%worlds () (name _ _).
%unique name +S -1K.
```

### Translator — `src/lean2lf.ts`

- `emitValDecl` (def/thm/opq) and `emitStructuralDecl` (axiom/ctor/indt/irec):
  emit one ground reservation constant per declaration and pass it into the
  `dkind-ok/*` witness, e.g.
  ```twelf
  <mn>/name-resv : name "<declName>" is-declaration.
  ```
  threading `"<declName>"` as the new first arg to `dkind-ok N …` (it equals
  the `declared` name string already emitted).
- For inductives (`indt`), additionally emit the rec-slot reservation using
  the concat form so the rule's `(N ++ ".rec")` pattern matches:
  ```twelf
  <mn>/rec-slot : name ("<indName>" ++ ".rec") is-rec.
  ```
  and pass it as the extra `dkind-ok/indt` argument.
- `irec` emits no reservation.
- `quot` stays SKIPped for now (full quot handling is later artifact-gap
  work); the `dkind-ok/quot` reservations are designed-for but unused until
  then.
- Hole interaction: when a `dkind-ok` witness is HOLE-admitted (Phase 3/4),
  still emit the reservation constant so the `%unique name` seal sees it. (The
  reservation is independent of the proof obligations.)

### Critical files

| File                              | Change                                                                                            |
| --------------------------------- | ------------------------------------------------------------------------------------------------- |
| `lf/tcb.elf`                      | rename term-`name`→`string`; add `name-kind`/`name`; thread `N` + reservations through `dkind-ok` |
| `lf/final-checks.elf`             | add `%mode`/`%worlds`/`%unique name`                                                              |
| `src/lean2lf.ts`                  | emit per-decl `name` reservations; rec-slot concat for inductives                                 |
| `lf/derived.elf`, `lf/shared.elf` | follow the term-`name`→`string` rename if they reference `name`                                   |

### Verification

1. `npx tsc --noEmit` and `npx eslint src/` clean.
2. `./scripts/gen-tests.sh && ./scripts/check-tests.sh …`:
   - **`124_dup_rec_def2` moves from accept to reject** (the target).
   - No regression elsewhere: ✅ counts hold, 💥 does not increase. (Watch for
     false positives where a healthy inductive's `.rec` slot collides with
     anything — spikes say it shouldn't, but verify across all 126.)
3. Sanity: load a healthy inductive test (e.g. `056_boolRec`) and confirm
   `%unique name` passes; load `124` and confirm the "Constants … overlap"
   ABORT.

### Out of scope (later)

- Forcing a recursor's _own_ name to be `<ind>.rec` (caveat 4): needs a
  recursor→family link (Strategy B / a `+kind -string` uniqueness). Not
  required for #124.
- `is-builtin` + literal/`proj` reduction-name dependencies (step 2).
- `.render.elf` adequacy encoding (step 2).

## Context

This repo is a Twelf-based kernel checker for Lean 4. The pipeline is:

```
.ndjson  →  parse.ts  →  JSON IR  →  lean2lf.ts  →  .elf  →  twelf  →  ✅ / 🩹 / ❌ / 🤷
```

**Done so far** (PRs #2, #4, #5):

- Phase 0+1: housekeeping + `eproj`/`enatlit`/`estrlit` constructors
- Phase R: extracted `src/render.ts`
- Phase 2: totalized `lfExpr` with `%solve` plumbing for `enatlit`
- Render-split interlude: `gen-tests.sh` produces `.full.elf` + `.render.elf`
- Phase 3: `%% HOLE/<tag>` markers + 🩹 verdict in the harness

**Current state (126 tests):**

- Good (should accept) 86: ✅ 50 / 🩹 17 / ⚠️ 9 / ❌ 10
- Bad (should reject) 40: ✅ 20 / 🩹 10 / ⚠️ 9 / 💥 1

---

## Next phase: collapse ⚠️ and ❌ into 🩹

Goal: move every remaining `⚠️` (translator declined) and `❌` (good test
Twelf rejects, no holes) into 🩹 (admitted holes). The 1 💥 is being consulted
with a human expert and is out of scope here.

The current ⚠️ and ❌ tests fall into **6 categories**, each fixed by a small,
local change to `src/lean2lf.ts`. The first four together handle every ❌ and
all but the quot ⚠️ tests; the quot work is deferred as a fifth, separate
change.

### Category 1 — `bridgeTypes` failure → HOLE/defeq (impact: 10 ❌ → 🩹)

**All 10 ❌ tests have exactly one `%% TRANSLATOR: could not bridge` marker.**
This path lives at `src/lean2lf.ts:1383-1388` inside `emitValDecl`:

```typescript
const bridge = bridgeTypes(valTy.tyExpr, d.type, {
  vars: [],
  hyps: [],
  tys: [],
});
if (bridge !== null) {
  valuePf = `(defeq/conv ${bridge} ${valTy.proof})`;
} else {
  emit(`%% TRANSLATOR: could not bridge inferred type to declared type`);
  emit(`%%   inferred type kind: ${valTy.tyExpr.kind}`);
  emit(`%%   declared type kind: ${d.type.kind}`);
  emit(`%%   emitting valTy.proof; Twelf will likely reject.`);
}
```

The translator currently emits `valTy.proof` knowing Twelf will reject.
**Fix:** swap to HOLE/defeq:

```typescript
} else {
  recordHole("defeq");
  // HOLE comment goes alongside valTyHoleComment, before the value-typed line
  valTyHoleComment = `%% HOLE/defeq: bridge-failed for ${declName} — inferred ${valTy.tyExpr.kind}, declared ${d.type.kind}`;
  valuePf = `(hole/defeq ${V_lf} ${V_lf} ${T_lf})`;
}
```

Affects: `070_prodRecEqns`, `090_ruleK`, `095_proofIrrelevance`,
`096_unitEta1`, `097_unitEta2`, `098_unitEta3`, `100_funEta`, `101_funEtaDep`,
`110_rtreeRecReduction`, `112_accRecReduction`.

### Category 2 — `emitStructuralDecl` synth-failure → HOLE/defeq (impact: 3+ ⚠️ → 🩹)

Same pattern as the Phase 3 change to `emitValDecl`, applied to
`emitStructuralDecl` (`src/lean2lf.ts:1461`) which handles
`axiom`/`indt`/`ctor`/`irec`/`quot` kinds. Currently SKIPs at
`src/lean2lf.ts:1497` ("could not translate type to LF" — dead post-Phase-2)
and `:1523` ("type synth failed").

**Fix:** on synth failure, emit
`%% HOLE/defeq: type-wf for <name> — <reason>`, use
`(hole/defeq T T (esort lzero))` as the type-wf proof, continue emitting
`/decl`, and **add to `declTable`** so downstream lookups succeed.

Affects directly: Quot.sound (in 070 — already gets HOLE'd by Category 1
indirectly), the recursor synths that cascade-fail when their ctor's mangle
isn't in declTable (`048_reduceCtorParam.mk`, `107_reduceCtorParamRefl.mk`,
`108_reduceCtorParamRefl2.mk`). Once the ctor (Category 3 below) is HOLE'd
into declTable, the recursor's synth here can succeed _or_ HOLE — either way
the cascade breaks.

### Category 3 — `ctor-positive` failure → HOLE/ctor-positive (impact: 3 ⚠️ → 🩹)

Current SKIP at `src/lean2lf.ts:1672` ("type is not strictly positive ...
soundness gap"). The ctor's type renders fine; only the strict-positivity
witness can't be built.

**Fix:** when `buildCtorPositive` returns `null`, emit
`%% HOLE/ctor-positive: <ctorName> — could not derive strict-positivity witness`,
use `(hole/ctor-positive N0 LS0 T)` in place of the positivity witness,
continue emitting `/decl`. Add new hole tag `"ctor-positive"` to
`HOLE_AXIOM_DECLS` (the axiom already exists in the inline declarations Phase
3 added — just wire the dispatch).

Affects: `047_indNeg`, `050_indNegReducible`, `105_reflOccLeft`.

### Category 4 — ctor result-shape / field-universe validation → HOLE/ctor-positive (impact: 6 ⚠️ → 🩹)

Several translator-side validations in `emitInductive` (`src/lean2lf.ts:1864`)
currently SKIP rather than emit a HOLE:

| Test     | Line                   | Check                               |
| -------- | ---------------------- | ----------------------------------- |
| 042      | :1873                  | `numParams` ≠ leading-Π count       |
| 043, 044 | inside ctor processing | ctor result-type param canonicity   |
| 046      | inside ctor processing | ctor result index mentions self     |
| 054, 106 | inside ctor processing | field universe > inductive universe |

These are all soundness checks on the constructor's _shape_, before the
strict-positivity witness is even attempted. They don't have a clean
Twelf-side judgment to admit — they're encoded as preconditions on
`ctor-positive/intro`.

**Fix:** unify them under HOLE/ctor-positive (same hole tag as Category 3).
The check failures emit the existing SKIP-reason text as
`%% HOLE/ctor-positive: <name> — <validation-failure-reason>` and the ctor's
emitted `/decl` uses `hole/ctor-positive` for the positivity witness.

Affects: `042_inductTooFewParams`, `043_inductWrongCtorParams`,
`044_inductWrongCtorResParams`, `046_inductInIndex`,
`054_typeWithTooHighTypeField.mk`, `106_reflOccInIndex`.

### Category 5 (deferred) — Quot family (impact: 6 ⚠️ remain ⚠️)

Tests `114_quotMkType` through `119_quotIndReduction` SKIP at
`src/lean2lf.ts:2112`
(`case "quot": emit('%% SKIP: quot not yet supported')`).

The Quot family is special: the IR has just `{ kind: "quot" }` (see
`src/shared.ts:97`) with no body, but the four Quot-family declarations
(`Quot`, `Quot.mk`, `Quot.sound`, `Quot.lift`, `Quot.ind`) need fully-typed
Twelf signatures to be useful as `declared` entries. The types are
_kernel-known_ (every Lean kernel knows them) but the translator doesn't
currently carry them.

This is a larger change than Categories 1–4 — it needs either a hardcoded type
schema or a Lean-side change to ship Quot types in the NDJSON. **Out of scope
for the next chunk**; revisit after Categories 1–4 land.

---

## Expected outcome after Categories 1–4

|         | Now | After                          |
| ------- | --- | ------------------------------ |
| Good ✅ | 50  | 50                             |
| Good 🩹 | 17  | 29 (17 + 12 new)               |
| Good ⚠️ | 9   | 3 (just the quot-related ones) |
| Good ❌ | 10  | 0                              |
| Bad ✅  | 20  | 20                             |
| Bad 🩹  | 10  | 14 (10 + 4 new)                |
| Bad ⚠️  | 9   | 3                              |
| Bad 💥  | 1   | 1                              |

22 tests collapse into 🩹; the only ⚠️ remaining are quot-family. Every
previously-failing good test (❌) gains a named HOLE explaining the missing
proof.

---

## Suggested PR split

Two PRs, stacked on PR #5:

**PR A — bridgeTypes + emitStructuralDecl HOLE-ization** (Categories 1+2)

- Smallest blast radius: only the proof-construction path changes, no new hole
  tag, no new IR shape checks bypassed.
- Impact: 10 ❌ → 🩹, 3 ⚠️ → 🩹.

**PR B — ctor-positive + shape-validation HOLE-ization** (Categories 3+4)

- Introduces `ctor-positive` as an active hole tag in dispatch.
- Bypasses translator-side soundness validations under hole admission — the
  _good_ effect is that test verdicts become more informative; the _honest_
  effect is that more files admit unproven facts. The 🩹 verdict already
  advertises this distinction.
- Impact: 9 ⚠️ → 🩹.

Quot (Category 5) is a separate, larger effort tracked for later.

---

## Critical files

| File                     | What changes                                                                                                                                                                                |
| ------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `src/lean2lf.ts`         | All HOLE-emission paths (Categories 1–4) live here. Existing infrastructure (`recordHole`, `HOLE_AXIOM_DECLS`, the inline-axiom prelude) was added in Phase 3 — just wire new tags through. |
| `scripts/check-tests.sh` | No changes — the 🩹 verdict already covers all hole cases.                                                                                                                                  |

## Verification

After each PR:

1. `npx tsc --noEmit` — no new errors.
2. `./scripts/gen-tests.sh && ./scripts/check-tests.sh /home/user/twelf-src/bin/twelf-server`
3. ✅ count must not decrease; 💥 count must not increase.
4. The new 🩹 entries should each carry at least one `%% HOLE/<tag>: <reason>`
   line readable from `head -20 <file>.full.elf`.

---

## Longer-term roadmap (tracked in `completeness-plan.md`)

The HOLE markers across `.full.elf` files are now the roadmap. Filling them
means:

1. **Iota stages 2+** — fills HOLE/defeq in Nat.succ, List.cons, indexed
   inductives
2. **Structural eta** — fills HOLE/defeq in tests 096–098 (unitEta)
3. **`t-const` level-poly congruence** —
   `defeq (econst N LS) (econst N LS') T'` when `lvls-eq LS LS'`
4. **`lvl-eq` algebraic completeness** — fills HOLE/lvl-eq
5. **Quot's primitive rule + Quot family typing** — fills the Category 5 gap
6. **`fully-captures` judgment** — replaces HOLE/ctor-positive for
   field-position negative occurrences (047, 050, 105)
7. **Mutual/nested inductives** — deferred, documented limitation
