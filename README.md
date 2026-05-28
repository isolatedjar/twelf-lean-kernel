# A (Mostly Vibe Coded) Lean Kernel in Twelf

In the Lean Kernel Arena (https://arena.lean-lang.org/tutorial/), kernels are
handed text files, and must validate that those files represent valid NDJSON
representations of valid Lean environments that obey the rules of Lean's type
theory.

The goal of this project is to write a Lean kernel in Twelf. This means that,
if a a file TEST.elf loads in Twelf like this:

```
loadFile tcb.elf
set unsafe true
loadFile freeze.elf
set unsafe false
loadFile derived.elf
loadFile TEST.elf
loadFile final-checks.elf
OS.exit
```

then that file encodes a valid Lean signature, and that any valid Lean
signature can be encoded as such a file.

**Important:** this requires a modified semantics of the `%freeze` and `%thaw`
commands that is implemented on the `limited-thaw` branch here: 
https://github.com/robsimmons/twelf/tree/limited-thaw

## Evaluation pipeline

The script `scripts/gen-tests.sh` takes the NDJSON files in `tests` and
produces three files:

- A `.json` file that represents a non-structure-sharing version of the NDJSON
  signature; other than that it is in essentially the same format.
- A `.render.elf` file that represents the contents of the contents of the
  NDJSON file in Twelf. This can be directly loaded by and checked in Twelf by
  skipping the `loadFile freeze.elf` part of the process described above.
  Because the `%freeze` is not present, many facts and proof obligations are
  declared by fiat. Each declarations represents an unfulfilled proof
  obligations that a Lean kernel needs to check in order to be a valid Lean
  proof.
- A `.full.elf` file that matches the `.render.elf`, but with as many of those

## References

The primary sources for this development are:

- The Metamath0 specification of Lean
  (https://github.com/digama0/mm0/blob/master/examples/lean.mm1)
- Carneiro's "The Type Theory of Lean" (2019)
- lean4lean's Theory/Typing/Basic.lean
- Princeton's Foundational Proof Carrying Code project, which worked out the
  style of proof we're attempting.
