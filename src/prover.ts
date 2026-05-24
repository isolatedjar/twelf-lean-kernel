// prover.ts — Prover plugins for the Twelf generator.
//
// UNTRUSTED. The generator (generate-twelf.ts) only consumes the `Fmt`
// values returned here; nothing in this file is part of the trusted base.
// See plugin-refactor.md and the `Prover` interface in shared.ts.

import type { ProofResult, Prover, TypeWfResult } from "./shared.ts";

// NullProver discharges nothing: every obligation becomes a HOLE. Running
// the generator with this prover produces the `.render.elf` view — the
// declaration skeleton with every proof obligation declared by fiat.
export const NullProver: Prover = {
  typeWellFormed(): TypeWfResult {
    return null;
  },
  valueHasType(): ProofResult {
    return null;
  },
  endsInSort(): ProofResult {
    return null;
  },
  ctorPositive(): ProofResult {
    return null;
  },
};

// RealProver is the featureful prover used for `.full.elf`. In step 1 of the
// plugin refactor it is identical to NullProver (so .full.elf == .render.elf
// content and every representable test is 🩹). It will be built up by mining
// the old lean2lf.ts in later steps.
export const RealProver: Prover = NullProver;
