// prover.ts — Prover plugins for the Twelf generator.
//
// UNTRUSTED. The generator (generate-twelf.ts) only consumes the `Fmt`
// values returned here; nothing in this file is part of the trusted base.
// See the `Prover` interface in shared.ts and the architecture note in CLAUDE.md.

import type { ParsedEnv, ProofResult, Prover, TypeWfResult } from "./shared.ts";
import { failOnPurpose, nameToString } from "./shared.ts";
import {
  bridge,
  buildCtorSpine,
  buildEnvMap,
  buildFieldUniverses,
  endsInSortProof,
  type EnvMap,
  levelToFmt,
  provablyDistinctSorts,
  synth,
} from "./synth.ts";

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
  fieldUniverses(): ProofResult {
    return null;
  },
};

// makeRealProver builds the featureful prover for `.full.elf`, backed by the
// full ParsedEnv for constant lookup and δ-reduction. It discharges:
//   - closed sort/Π/λ/bvar fragment (always)
//   - constants via defeq/const + explicit inst-expr witnesses
//   - applications via defeq/app with codomain substitution
//   - β-reduction (app of lam) via defeq/beta
//   - δ-reduction (def unfolding) via defeq/delta
// Obligations outside these rules return null (→ HOLE), never an unsound proof.
export function makeRealProver(env: ParsedEnv): Prover {
  const envMap: EnvMap = buildEnvMap(env);

  return {
    typeWellFormed({ type, levelParams, isThm }): TypeWfResult {
      const r = synth(type, envMap);
      if (!r || r.ty.kind !== "sort") return null;
      if (isThm) {
        // Generator emits proof at (esort lzero); coerce synth sort U → lzero.
        const U = r.ty.level;
        const lzero: import("./shared.ts").Level = { kind: "zero" };
        const coerce = bridge({ kind: "sort", level: U }, { kind: "sort", level: lzero }, envMap);
        if (!coerce) return null;
        return { sort: levelToFmt(lzero, levelParams), proof: coerce(r.proof) };
      }
      return { sort: levelToFmt(r.ty.level, levelParams), proof: r.proof };
    },
    valueHasType({ value, type }): ProofResult {
      const r = synth(value, envMap);
      if (!r) return null;
      const coerce = bridge(r.ty, type, envMap);
      if (coerce) return coerce(r.proof);
      // Decide-then-refute: if the synthesized type and the declared type are
      // both concrete closed sorts at different universe levels, the obligation
      // is provably false. Emit a genuine refutation (Twelf ❌) rather than a
      // HOLE — never an unsound proof.
      if (provablyDistinctSorts(r.ty, type)) return failOnPurpose;
      return null;
    },
    endsInSort({ type }): ProofResult {
      return endsInSortProof(type);
    },
    // Returns only the `ctor-spine` proof; the trusted generator computes the
    // matching `T_HOAS` and assembles `ctor-positive/intro`.  See shared.ts.
    ctorPositive({ ctorType, indName, indLevels, levelParams }): ProofResult {
      try {
        return buildCtorSpine(ctorType, nameToString(indName), indLevels, [], [], levelParams);
      } catch {
        return null;
      }
    },
    fieldUniverses({ ctorType, nParams, indUInd }): ProofResult {
      try {
        return buildFieldUniverses(ctorType, nParams, indUInd, envMap);
      } catch {
        return null;
      }
    },
  };
}
