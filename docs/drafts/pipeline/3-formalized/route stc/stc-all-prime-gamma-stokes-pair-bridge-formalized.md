# All-prime equal-depth Gamma-to-Stokes pair bridge — Lean certificate

- **Paper card:** `stc-all-prime-gamma-stokes-pair-bridge.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.Deninger.DeningerGammaAllPrimeStokesPairBridge`,
  `GaloisForLFunctions.RHTower.STCGammaPairCalibrationGeometry`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

| Card item | Lean theorem |
|-|-|
| (3) division-free bridge | `source_pair_stokes_bridge` |
| (4) positive calibration form; `K > 0` | `source_pair_stokes_positive_bridge`, `sourcePairCalibration_pos` |
| `S = -(H_p-H_q) Q`; two-channel `Q` | `source_pair_commutator_identity`, `source_pair_symmetric_kernel_two_channel` |
| (5) `K_pq K_rs < K_pr K_qs` | `sourcePairCalibration_cross_lt` |
| no rank-one `a_p a_q` calibration | `no_rank_one_sourcePairCalibration`, `no_rank_one_prime_log_gap` |
| `K/(B_p B_q) = n log(q/p)/4` | `sourcePairCalibration_div_amplitudes` |
| infimum zero over large pairs (PNT) | `exists_sourcePairCalibration_normalized_lt` |
| unbounded divided difference `1/(H_q-H_p)` | `exists_halfHeight_gap_inv_gt` |
| raw exterior rank ≤ 2; reflection-odd rank ≤ 4; rescaling | `rank_modularExteriorPacket_le`, `rank_reflectionOddExteriorPacket_le`, `rank_rescaled_reflectionOddExteriorPacket_le` |
| no global-scalar × one-prime-rescaling identification | `no_scalar_rescaled_reflectionOdd_stokes_identification` |
