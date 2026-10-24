# AIP Open Problem 4: Lattice Conductance at Fixed Width and Origin/Axis First-Jet Packets

- **ID:** aip-open-problem-4-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md` §7 Open Problem 4
- **Lean Module:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/LatticeConductanceFixedWidthAndOriginAxisJets.lean`
- **Lean Declarations:**
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.totalLatticeSameKernel`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.totalLatticeSameKernel_pos`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.totalLatticeNetKernel`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.totalLatticeNetKernel_eq`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.totalLatticeNetKernel_pos`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.totalLatticeCrossingKernel_diag_pos_iff`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.totalLatticeAxisKernel`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.totalLatticeAxisKernel_eq`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.totalLatticeAxisKernel_pos`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.jetQuotient`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.mul_jetQuotient_eq`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.continuous_jetQuotient`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.tendsto_origin_bump_sq_div_cube`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.tendsto_origin_axis_bump_pair_div_sq`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.fullEnergy_narrowBump_div_mass_ge`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.fullEnergy_latticeTrain_fixedWidth_ge`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.abs_incidenceForm_le`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.fullEnergy_latticeTrain_nonneg_of_le`
  - `GaloisForLFunctions.ArithmeticIncidencePositivity.eventually_fullEnergy_latticeTrain_nonneg`

## Gates
- [x] 0 → 1  in-progress: well-posed, corpus searched, complete mathematical structure derived
- [x] 1 → 2  fully-proven: complete paper proofs with zero open dependencies
- [x] 2 → 3  formalized: Lean module `LatticeConductanceFixedWidthAndOriginAxisJets.lean` verified with `lake --old env lean`, wired into `ArithmeticIncidencePositivity.lean`
- [x] 3 → 4  README updated crisply

## Log
- 2026-10-24 — created in 1-in-progress; formalized, verified with `lake --old env lean` (exit code 0), wired into `ArithmeticIncidencePositivity.lean`, and moved to `3-formalized`.
