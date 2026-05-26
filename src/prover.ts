// prover.ts — Prover plugins for the Twelf generator.
//
// UNTRUSTED. The generator (generate-twelf.ts) only consumes the `Fmt`
// values returned here; nothing in this file is part of the trusted base.
// See plugin-refactor.md and the `Prover` interface in shared.ts.

import type { ProofResult, Prover, TypeWfResult } from "./shared.ts";
import { bridge, levelToFmt, synth } from "./synth.ts";

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

// RealProver is the featureful prover used for `.full.elf`. It discharges the
// closed sort/Π/λ fragment via src/synth.ts (sorts, Π-types, λ-abstractions,
// bound variables — no constants, reduction, or inductives). Obligations
// outside the fragment return null (→ a HOLE), so RealProver can only ever
// turn 🩹 into ✅, never produce an unsound proof. Remaining obligation kinds
// (ends-in-sort, ctor-positive) are still deferred. See src/synth.ts.
export const RealProver: Prover = {
  typeWellFormed({ type, levelParams }): TypeWfResult {
    const r = synth(type);
    if (!r || r.ty.kind !== "sort") return null;
    return { sort: levelToFmt(r.ty.level, levelParams), proof: r.proof };
  },
  valueHasType({ value, type }): ProofResult {
    const r = synth(value);
    if (!r) return null;
    const coerce = bridge(r.ty, type);
    return coerce ? coerce(r.proof) : null;
  },
  endsInSort(): ProofResult {
    return null;
  },
  ctorPositive(): ProofResult {
    return null;
  },
};
