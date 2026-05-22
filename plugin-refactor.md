Refactor guidelines

In order to get from where we are to where we want to be — to the state
described in the README — we're going to start over with a lot of our
typescript architecture.

A new file, `generate-twelf.ts`, is going to contain all of the `emit` logic
currently spread across `render.ts`, `render-cli.ts`, and `lean2lf.ts`. Its
principal function takes two arguments, a `Prover` and a `ParsedEnv`
(`ParsedEnv` is already defined in `shared.ts`, and `Prover` will be added).
The prover methods that try to discharge the various proof obligations we
might come across. These functions always either return `null`, representing
an inability to figure out the proof obligation, or `Fmt`, where `Fmt` is a
representation of string arguments that form a Twelf proof which the generator
knows how to pretty-print.

Each time the generator comes across a proof obligation, it calls the relevant
`Prover`. Success for the prover will allow the generator to provide a
definition for the proof obligation:

```
<const> : <type representing proof obligation> = <proof>.
```

failure of the prover (null return) will always mean the generator will
provide a declaration, meaning that the proof obligation is unfulfilled.

```
%%% HOLE
<const> : <type representing proof obligation>.
```

If the prover is able to definitively decide there is no way to fulfill the
mandatory proof obligation, it can signal this by triggering the generator to
print the definition `fail-on-purpose`, which ensures the resulting Twelf
signature will be treated as failing.

- The generation of `.render.elf` is very simple: we pass a `Prover` that
  always returns `null` for all of its methods. The `.full.elf` file is
  created by using a real prover.
- The generation of `.full.elf` is the same except it uses a much more
  complicated and featureful Prover instance that does actually try to fulfill
  proof obligations in a meaningful way.

This plugin architecture — one way of outputting Twelf files that gets a
prover plugged in — gets around a failing of the first architecture: there was
nothing enforcing that the `.render.elf` file contained "everything from the
ndjson". Here, if an audit of `shared.ts`, `parse.ts`, and `generate-twelf.ts`
ensures these conform to the intended design, the `prover.ts` file defining a
better prover can be completely untrusted and does not to be audited.

In principle, there needs to be a lightweight check on `Fmt` objects to make
sure that a prover cannot "smuggle" the end of a declaration and the start of
a new declaration into a `Fmt` object in the manner of a SQL injection attack.
For now, just don't do that.

Testing:

- The test outcome `🤷` means that we're unwilling to emit a Twelf file that
  fully represents that file (neglecting unfulfilled proof obligations).
  Ultimately we should be able to emit a valid Twelf signature for _every_
  valid Lean signature, but we don't expect that we'll be able to emit a valid
  Twelf signature for every invalid NDJSON signature. An NDJSON file that
  doesn't even parse as JSON is one example, an NDJSON with invalid de bruijn
  indices is another: these have on way of being meaningfully represented in
  Twelf.

  The `🤷` outcome is _equivalent_ to a reject from the Kernel Arena's
  perspective so it represents a failing verdict (❌) for expected-good tests
  and a success verdict (✅) for expected-bad tests. We distinguish it as an
  outcome because we'd _like_ to be able to represent as many NDJSON files as
  possible, but it's just not possible in all cases.

- The test outcome `🔴` means that the `.render.elf` file is created but is
  rejected by Twelf (when loaded as described in the README - the standard
  script but without loading freeze or final-checks).

  The `🔴` outcome is also equivalent to a reject from the Kernel Arena's
  perspective, so it represents a failing verdict (❌) for expected-good tests
  and a success verdict (✅).

- The test outcome `🩹` means that the `.full.elf` is rejected by Twelf when
  run against the full test, but **accepted** by Twelf if the
  `loadFile freeze.elf` step is skipped. This represents an incomplete verdict
  (`🩹`) in all cases, and corresponds to declining to evaluate a particular
  development in the Lean Kernel Arena.

- The test outcome `❌` means that `.full.elf` file is created and is rejected
  by Twelf (when loaded as described in the readme — the standard script,
  including freeze and final-checks,) AND that it does not contain `%%% SKIP`.
  This represents a failing verdict (❌) for expected-good tests and a success
  verdict (✅) for expected-bad tests.

- The test outcome `✅` means that `.full.elf` file is created and is accepted
  by Twelf, which implies that nothing was left with `%%% SKIP`, as that would
  have failed a freeze check. This represents a success verdict (✅) for
  expected-good tests and a worst-possible soundness-bug issue (💥) for
  expected-bad tests.

Process:

- This is going to reset us to zero on our metrics, and probably mean we need
  to completely rewrite the testing harness. That's fine, the whole point of
  the typescript stuff is to find out if we have the right TCB.
- The first goal is to maximize 🩹 results and minimize failures. I don't want
  to focus on the Prover architecture until we get generation right. It's okay
  to start with a prover that does a couple of things right to work out the
  design. It's only once we're back to about where we were before, but with
  many fewer ✅ verdicts, it's time to mine the old content of `lean2lf.ts` to
  get the prover back to where it was before.
- The TCB is in pretty good shape, though we've learned a lot recently from
  the ability to compare with the metamath project. If there are TCB refactors
  that really ought to come first that's a possibility, but it is not the
  immediate goal.
- The prover can absolutely be a class that update its own state if needed.
- Once we're about where we were before the refactor, all the stuff in
  `archive` should be summarized in CLAUDE.md and deleted, along with
  `lf2lean.ts` and this file. For the record, this is where we are before the
  refactor:

  ```
  Good tests (expected accept) — 86 total:
    ✅  pass:        54
    🩹  with-holes:  20  (would-be-verified-if-holes-filled)
    ⚠️   incomplete:  0  (translator declined — % SKIP)
    ❌  failed:      12

  Bad tests (expected reject) — 40 total:
    ✅  reject:      20
    🩹  with-holes:  13  (would-be-rejected-if-holes-filled)
    ⚠️   incomplete:  6  (translator declined — not Twelf-verified)
    💥  accept:      1  (soundness failure — no holes)
  ```

  One reason why this is important is that a lot of motivation has drifted.
  Two examples: the new README doesn't include caveats about functional
  dependencies (we check these fully with `%unique`) or which families are
  open (we check this fully with the ``). We won't need to obsess over what's
  moral twelf — the design is explaining what we mean.
