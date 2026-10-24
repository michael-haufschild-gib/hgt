# AIP Open Problem 3: The Archimedean Part of the Bump Bridge and Calibrated Self-Energy Asymptotic

- **ID:** aip-open-problem-3-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md` §7 Open Problem 3 & Research Topic 3
- **Lean Module:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/ArchimedeanBumpBridgeAndSelfEnergyAsymptotic.lean`
- **Statement:** Complete resolution of Open Problem 3 and Research Topic 3:
  1. Width-independent Lipschitz-`L¹` shift domination (`abs_bumpPairShiftJump_le_mul_t`, `abs_shift_bumpProfile_le_mul_t`) and global integrability (`integrableOn_archLevyDensity_mul_signedShiftJump_bumpProfile`).
  2. Single-bump logarithmic self-energy asymptotic (`tendsto_gaugeArchJump_singleBump_div_mul_log`): for a Lipschitz compactly supported bump `β` on `[-1, 1]` and continuous gauge `M` with `|M x| ≤ C e^{-|x|}`, `gaugeArchJump M (fun x => β ((x - α) / w)) / (w * log(1 / w)) → M(α)² ∫ β²` as `w → 0⁺`.
  3. Quadratic `O(w²)` off-diagonal archimedean decoupling (`abs_gaugeArchJump_sub_sum_singleBump_le`, `tendsto_gaugeArchJump_sub_sum_singleBump_div`): for a multi-centre bump profile `shiftedBumpProfile β w P κ`, distinct centres `p ≠ q` decouple completely on `t ∈ (0, s/2]` and overlap only on `t`-intervals of width `4w` in `(s/2, ∞)`, so `|gaugeArchJump M u_w - ∑_{p ∈ P} κ_p² gaugeArchJump M β_{p,w}| ≤ K w²`.
  4. Multi-bump and lattice `w log(1/w)` asymptotics (`tendsto_gaugeArchJump_bumpProfile_div_mul_log`, `tendsto_gaugeArchJump_latticeBumpProfile_div_mul_log`, `tendsto_signedJumpEnergy_bumpProfile_div_mul_log`, `tendsto_signedJumpEnergy_latticeBumpProfile_div_mul_log`).
  5. Calibrated `O(w)` bump bridge (`tendsto_calibratedSignedJumpEnergy_bumpProfile_div`, `tendsto_calibratedSignedJumpEnergy_latticeBumpProfile_netAtom`) and ground-state source potential bridges (`tendsto_integral_sq_bumpProfile_mul_div`, `tendsto_integral_sq_latticeBumpProfile_mul_div`).

## Gates
- [x] 0 → 1  in-progress: well-posed, corpus searched, complete mathematical structure derived
- [x] 1 → 2  fully-proven: complete paper proofs with zero open dependencies
- [x] 2 → 3  formalized: Lean module `ArchimedeanBumpBridgeAndSelfEnergyAsymptotic.lean` verified with `lake --old env lean` (`task-474`, exit code 0), wired into `ArithmeticIncidencePositivity.lean`
- [x] 3 → 4  README updated crisply

## Log
- 2026-10-24 — created in 1-in-progress; formalized, verified (`task-474`), wired into umbrella, and moved to `3-formalized`.
