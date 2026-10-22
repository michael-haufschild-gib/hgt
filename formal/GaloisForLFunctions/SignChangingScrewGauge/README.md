# Sign-Changing Screw-Resonant Gauges in GlobalIncidenceAllocation (`GaloisForLFunctions.SignChangingScrewGauge`)

This theorem area formalizes **Mechanism 3** of Project Argon (`docs/reports/review-2110/argon.md`, §1.4), addressing **Wall 1.1** (Prime-Shift Subsolution Failure for Nonnegative Gauges), **Wall 1.2** (The Edge-Tent Sharing Obstruction), and **Wall 2.1** (Odd Two-Bump Selectivity and the Screw Crossover at the Plastic Threshold).

## Module Ledger

1. **`SignChangingCollarGaugeLedger.lean`** — *Unconditional Sign-Changing Collar Gauge Energy Ledger, Prime-Shift Cancellation, and Collar Conservation*:
   - `hasCompactSupport_of_support_le`, `exists_abs_le_exp_of_support_le`: Compact support and exponential decay `|P(y)| ≤ C e^{-k|y|}` for any continuous gauge vanishing outside `(-R, R)`, with no `0 ≤ P` or `P ≤ 1` constraint.
   - `integral_mul_mul_shiftCommutator_eq_gaugeJumpProfile`: Unconditional commutator summation-by-parts identity `∫ x, F x * P x * shiftCommutator P F t x = gaugeJumpProfile P F t` for any continuous sign-changing gauge `P` and continuous compactly supported `F`.
   - `profilePrimeSum_nonneg_of_nonneg`, `profilePrimeSum_zero_eq_two_term_of_collar`, `profilePrimeSum_zero_neg_and_weilOperator_gain_of_neg_collar`: Whereas nonnegative gauges satisfy `0 ≤ profilePrimeSum P x`, an even sign-changing collar gauge with `P(log 2) < 0` (`P(log n) = 0` for `n ≥ 3`) achieves `profilePrimeSum P 0 = 2 * vonMangoldtAtom 2 * P(log 2) < 0` and strictly boosts `-poleFreeWeilOperator P 0 c_arch` above its prime-free baseline.
   - `gaugeJumpProfile_sub_shiftPotential_eq_neg_two_mul_autoCorr`, `signedCollar_netShiftEnergy_invariance`: Exact 1-for-1 collar conservation between collar-exit jumps and the shift potential on `supp F`, proving `gaugeJumpProfile P F L - ∫ x, F x ^ 2 * P x * (P (x + L) + P (x - L)) = -2 * autoCorr F L` for **every** continuous sign-changing collar gauge `P` with `P = 1` on `supp F`.

2. **`NetPrimeAutocorrelationAndEdgeTentResolution.lean`** — *Bilateral Net Prime-Autocorrelation Accounting and Resolution of the Edge-Tent Sharing Obstruction*:
   - `stripEvenPart`, `stripOddPart`, `evenStripGain`, `oddStripCost`, `netPrimeStripBalance`, `stripEvenPart_sq_sub_stripOddPart_sq`, `stripEvenPart_sq_sub_stripOddPart_sq_of_odd`: Defines `netPrimeStripBalance F r n := evenStripGain F r n - oddStripCost F r n` and establishes the reflected strip polarization `stripEvenPart F L u ^ 2 - stripOddPart F L u ^ 2 = F (L / 2 - u) * F (L / 2 + u)`.
   - `mul_shift_nonpos_of_odd_nonneg_on_Ici`, `autoCorr_nonpos_of_odd_nonneg_on_Ici`, `stripOddPart_sq_le_stripEvenPart_sq_of_odd_nonneg_on_Ici`, `netPrimeStripBalance_nonneg_of_odd_nonneg_on_Ici`, `oddStripCost_le_evenStripGain_of_odd_nonneg_on_Ici`: For **every** odd profile `F` supported in `[-r, r]` with `0 ≤ F` on `[0, ∞)` and **every** shift `L ≥ r`, `F(x) F(x + L) ≤ 0` pointwise on `ℝ`, `autoCorr F L ≤ 0`, and `0 ≤ netPrimeStripBalance F r n` (`oddStripCost F r n ≤ evenStripGain F r n`) for all `r ≤ log n`.
   - `exists_pos_and_neg_on_Ici_of_evenStripGain_lt_oddStripCost`: Rigidity law proving that any trans-half-width prime deficit `evenStripGain F r n < oddStripCost F r n` (`r ≤ log n`) requires `F` to change sign on `[0, ∞)`.
   - `stripEvenPart_sq_eq_stripOddPart_sq_of_edgeSupported`, `netPrimeStripBalance_eq_zero_of_edgeSupported`, `sum_netPrimeStripBalance_eq_zero_of_edgeSupported`: Complete resolution of the Edge-Tent Sharing Obstruction: for any profile `F` vanishing on `(-(r - ε), r - ε)`, `netPrimeStripBalance F r n = 0` identically on every strip in the thin band `r ≤ log n ≤ 2(r - ε)`.

3. **`ScrewResonantCollarAndPoleCalibration.lean`** — *Screw-Resonant Zero-Form Ledger, Plastic Crossover, and Collar Moment Calibration*:
   - `screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity`, `archLevyDensity_sub_two_mul_cosh_eq_neg_screwRegularKernel`, `archJump_sub_two_cosh_jump_eq_screwResonantJumpEnergy`: Unifies Suzuki's regular screw kernel `screwRegularKernel t = 2 cosh(t/2) - archLevyDensity t` with the archimedean-minus-cosh jump integral `screwResonantJumpEnergy P F`.
   - `screwRegularKernel_crossover_dichotomy`, `screwResonantJumpEnergy_nonneg_of_two_mul_le_screwSignThreshold`, `screwRegularKernel_mul_neg_autoCorr_pos_of_gt_threshold`: Sub-plastic nonnegativity (`2R ≤ screwSignThreshold ∈ (1/10, log 2)`) and super-plastic cross-correlation positivity (`screwSignThreshold < t`) for opposite-sign two-bump lags (`autoCorr F t < 0`).
   - `evenPoleMoment_eq_zero_of_odd`, `evenPoleMoment_add`, `evenPoleMoment_collar_cancellation`: Odd-sector even-pole vanishing and exact neutralization of `evenPoleMoment (P₀ + P_col) = 0` via a sign-changing outer collar `P_col`.

4. **`MasterSignChangingScrewGaugeTheorem.lean`** — *Master Synthesis*:
   - `sign_changing_screw_gauge_master_theorem`: Jointly packages all four legs into a single unconditional theorem.
