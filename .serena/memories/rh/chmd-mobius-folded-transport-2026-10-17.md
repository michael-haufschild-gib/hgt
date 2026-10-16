# CHMD Phase 2 Path 1 complete: folded Möbius series for the KG transport (MUST-1570)

Module `RHTower/CHMDMobiusFoldedTransportOfKleinGordonPrimeWave` (ns `RHTower.CHMDChebyshevTransport`), imports the conjugated-transport module (MUST-1569).

- `T(y) = K_y(0) − Σ'_m μ(m) Φ_y(log m)`, `Φ_y(v) = ∫_{Ioi 0} S(u) f_y''(u+v)`, `S = ccmPrimeDeficitDilationSource` (`ccmPrimeDeficitDilationSource_zero`, `abs_ccmPrimeDeficitDilationSource_le : |S u| ≤ sourceBound * exp u` for u ≥ 0, `sourceBound = 7/2 + 5/3 + log(2π)/2`).
- `mobiusFold_eq` (v ≥ 0): `Φ_y(v) = mobiusWaveConstant * conjugatedKernel y v + (γ+1)(e^{−v}∫_{Ioi v} K_y e^{s/2}) + remainderFold y v`; `abs_remainderFold_le : |remainderFold y v| ≤ 7 * laplacianBound * exp(−v/2)` for all y, v.
- `chebyshevDiscrepancyTransport_eq_mobius_pieces`, `riemannHypothesis_iff_mobius_pieces_bddAbove/_bddBelow` with `mobiusWave`, `mobiusTailPairing`, `remainderFoldSeries` (summable: `summable_moebius_mul_exp_neg_log`).
- Useful general lemmas: `setIntegral_Ioi_shift g ℓ : ∫_{Ioi ℓ} g = ∫_{Ioi 0} g(·+ℓ)`; `integral_Ioi_exp_sub_mul_conjugatedLaplacian` (pole IBP from base v ≥ 0).
- Lean traps: `IntegrableOn.comp_add_right` needs `IsAddRightInvariant` of the restricted measure (absent) — dominate directly; ascribe `IntegrableOn` before `.congr_fun`; `positivity` ignores hint lists; split `tsum_eq_sum` and `Finset.sum_congr`.
- Verdict: BRIDGE (Phase 2 Path 1 done). Remaining Paths 2 (Cesàro/√-Riesz quotient-block channels) and 3 (theta harmonic identity + chain variances) of docs/reports/cmhd-plan.md.
