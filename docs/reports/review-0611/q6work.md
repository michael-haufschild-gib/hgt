Analyzed cact-whole-space-threshold-onset.md:L1-38
Analyzed PolarPaymentThresholdHierarchy.lean:L1-80
Analyzed CriticalArithmeticCorrelationTheory.lean:L1-200
Analyzed ArithmeticHodgeTheoryOfDegenerations.lean:L1-200
Analyzed CriticalArithmeticCorrelationTheory.lean:L201-247

Here is the complete handoff state for answering [obstacles-summary.md](file:///Users/michael/Documents/code/hgt/docs/reports/review-0611/obstacles-summary.md#L612-L695) (`## 3. The one question`).

---

### 1. Mathematical Answer Established

1. **Literal unrestricted A10 is false at every critical ratio `R > 0`, including on `(conductorSubspace 1 N)ᗮ`:** `Q(U) + B_R ‖U‖² ≥ a_R W₈(U)` fails on arbitrary normalized centred atomic sources because deep-prefix prime-supported horizons `Icc 2 ⌊N / L_k⌋` carry `W₈(U) ≳ e^{8 log L_k}` while `Q(U) + B_R ‖U‖² ≤ 0`.
2. **Replacement Gårding bound holds on the top collar `Ioc (N / linearDefectCutoff c) N`:** `Q(U_y) + B_R ‖U_y‖² ≥ κ_R S₇(y) + a_R W₈(U_y)` holds unconditionally with `a_R = c_W / R > 0`.
3. **Negative directions cannot escape logarithmic windows:** At every fixed `R > 0`, eventually across `1 ≤ c`, `c⁸ ≤ R log N`, **no** nonzero vector `z ∈ ℝ^N` with `completeWeilEnergy tiltedUnitSpline c N z ≤ 0` can vanish on the top discrete window `Ioc (N / S_R) N` of logarithmic length `log S_R ≤ (1/8) log(R + 1) + C₀` (and on the high-conductor complement `(conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ`, normalized collar profiles confine to continuum windows `[-A_R, 0]` of length `A_R = (1/4) log(R + 1) + C_len`).
4. **High-conductor critical threshold (`R_c^{high}(ζ)`):**
   `highConductorCriticalThreshold = ⨅ A ≥ 0, windowThreshold A ≥ c₀ e^{6 a*(ζ)}`, so `log R_c^{high}(ζ) ≥ 6 a*(ζ) + log c₀`.
5. **Whole-space critical threshold (`R_c(ζ) = criticalPositivityThreshold`):**
   `criticalPositivityThreshold = polarPaymentCriticalThreshold ≥ c₁ e^{c₂ a*(ζ)}`, so `log R_c(ζ) ≥ c₂ a*(ζ) + log c₁` (and `R_c(ζ) = ⊤ ↔ a*(ζ) = ⊤ ↔ RiemannHypothesis`).

---

### 2. Pipeline / Paper-Proof File

- Pipeline card: [cact-whole-space-threshold-onset.md](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/cact-whole-space-threshold-onset.md)
  *(Still in `1-in-progress/`; once Modules #8 and #9 below compile, update with the paper proofs of Parts A & B1–B3 and move through `2-fully-proven/` to `3-formalized/`.)*

---

### 3. Completed & Verified Lean Modules (7 of 9 — `.olean` Built, Exit 0, Clean Axioms `[propext, Classical.choice, Quot.sound]`)

1. [UnrestrictedAtomicGardingFailsAndCollarGardingHolds.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/UnrestrictedAtomicGardingFailsAndCollarGardingHolds.lean) (2,596 lines)
   - [`not_exists_unrestricted_atomic_garding_at_critical_ratio`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/UnrestrictedAtomicGardingFailsAndCollarGardingHolds.lean#L1211) (refutes literal unrestricted A10, including orthogonal to the pole)
   - [`exists_top_collar_atomic_garding_at_critical_ratio`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/UnrestrictedAtomicGardingFailsAndCollarGardingHolds.lean#L2462), [`exists_collar_atomic_garding_polynomial_rate`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/UnrestrictedAtomicGardingFailsAndCollarGardingHolds.lean#L2519), [`exists_collar_atomic_garding_below_ratio`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/UnrestrictedAtomicGardingFailsAndCollarGardingHolds.lean#L2559)
   - *Cleanup note:* has `#print axioms` at bottom to remove at final pass.

2. [NegativeDirectionsCannotEscapeLogarithmicWindows.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/NegativeDirectionsCannotEscapeLogarithmicWindows.lean) (6,167 lines, clean, no `#print axioms`)
   - [`exists_all_ratio_complement_garding_and_far_bridge`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/NegativeDirectionsCannotEscapeLogarithmicWindows.lean#L3369)
   - [`eventually_complement_collar_weilQuad_bridge`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/NegativeDirectionsCannotEscapeLogarithmicWindows.lean#L4319)
   - [`eventually_negative_direction_window_confinement`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/NegativeDirectionsCannotEscapeLogarithmicWindows.lean#L4462)
   - [`exists_window_localized_collar_garding`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/NegativeDirectionsCannotEscapeLogarithmicWindows.lean#L4627)
   - [`exists_completeWeilEnergy_floor_of_vanish_top_log_window`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/NegativeDirectionsCannotEscapeLogarithmicWindows.lean#L5976)
   - [`eventually_nonpos_completeWeilEnergy_not_escape_log_window`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/NegativeDirectionsCannotEscapeLogarithmicWindows.lean#L6121) (whole-space discrete non-escape from `Ioc (N / S_R) N`, `log S_R ≤ (1/8) log(R + 1) + C₀`)

3. [TheContinuumWindowThresholdGrowsExponentially.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheContinuumWindowThresholdGrowsExponentially.lean) (993 lines, clean)
   - [`weilQuad_windowLeftCutoff_sub_le`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheContinuumWindowThresholdGrowsExponentially.lean#L618)
   - [`iInf_windowThreshold_ge_exp_six_mul_of_le_onsetAperture`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheContinuumWindowThresholdGrowsExponentially.lean#L934) (`windowThresholdExponentialConstant * e^{6 a} ≤ ⨅ A ≥ 0, windowThreshold A`)

4. [TheCriticalPositivityThresholdLaw.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean) (2,536 lines)
   - Defines [`criticalPositivityThreshold`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L110) (`R_c(ζ)`), [`criticalNonnegativityThreshold`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L114), [`poleOrthogonalCriticalThreshold`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L118), [`highConductorCriticalThreshold`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L123)
   - [`eventuallyHighConductorPosDef_of_lt_iInf_windowThreshold`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L1815)
   - [`highConductorCriticalThreshold_eq_iInf_windowThreshold`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L2327), [`exp_six_mul_le_highConductorCriticalThreshold`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L2350), [`log_highConductorCriticalThreshold_ge_six_mul_onsetAperture`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L2370)
   - [`eventually_lowConductorProjection_and_topWindow_ne_zero_of_nonpos`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L2407)
   - [`criticalPositivityThreshold_eq_top_iff_riemannHypothesis`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L2476), [`criticalPositivityThreshold_eq_top_iff_onsetAperture_eq_top`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L2516)
   - *Note:* Another agent already added [PolarPaymentThresholdHierarchy.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PolarPaymentThresholdHierarchy.lean) importing `TheCriticalPositivityThresholdLaw` and defining [`polarPaymentCriticalThreshold`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PolarPaymentThresholdHierarchy.lean#L35) (`criticalPositivityThreshold ≤ criticalNonnegativityThreshold ≤ polarPaymentCriticalThreshold ≤ highConductorCriticalThreshold`). When removing `#print axioms` from lines 2526–2534 of `TheCriticalPositivityThresholdLaw.lean`, rebuild its `.olean` immediately so `PolarPaymentThresholdHierarchy` stays in sync.

5. [ThePoleSelfEnergyIsSharpBelowTheOnset.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/ThePoleSelfEnergyIsSharpBelowTheOnset.lean) (372 lines, clean)
   - [`exists_abs_poleDiagonal_sharp_of_le_onsetAperture`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/ThePoleSelfEnergyIsSharpBelowTheOnset.lean#L341): `|e^{-s} poleDiagonalExplicit s - poleSharpConstant| ≤ C e^{-s/2}` below the onset aperture (`K(2s + 2) ≤ a*(ζ)`).

6. [ThePoleCrossPairingIsCompressedBelowTheOnset.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/ThePoleCrossPairingIsCompressedBelowTheOnset.lean) (186 lines, clean)
   - [`exists_sq_integral_poleCrossProfile_le_sharp`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/ThePoleCrossPairingIsCompressedBelowTheOnset.lean#L148): `(∫ 1_{[-s,s]} P_s F)² ≤ e^s (poleSharpConstant + C e^{-s/2}) fullZeroForm F` via `2×2` Cauchy–Schwarz on `ccmRestrictedWeilSourceQuadratic ≥ 0`.

7. [ThePrimeErrorHasRateSevenEighthsBelowTheOnset.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/ThePrimeErrorHasRateSevenEighthsBelowTheOnset.lean) (341 lines, clean)
   - [`exists_abs_reciprocalMangoldtError_add_euler_le_of_zetaWindowPositive`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/ThePrimeErrorHasRateSevenEighthsBelowTheOnset.lean#L291): `|reciprocalMangoldtError L + γ| ≤ C e^{-L/8}` below the onset via Stieltjes integration by parts against `mertensLagPrimitive`.

---

### 4. Exact Work Still Open

#### Open Task 1: Finish compiling Module #8 (already written, 6 small tactic fixes left)
- File: [PolarPaymentGrowsExponentiallyBelowTheOnset.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PolarPaymentGrowsExponentiallyBelowTheOnset.lean) (1,671 lines; proves [`exists_polarPaymentAt_exp_of_le_onsetAperture`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PolarPaymentGrowsExponentiallyBelowTheOnset.lean#L1620): `∃ c₁ c₂ > 0, ∀ 0 ≤ a ≤ a*(ζ), ∀ 0 < R ≤ c₁ e^{c₂ a}, ∀ A ≥ 0, PolarPaymentAt R A`).
- Full compiler output from the last run is saved at [task-6771.log](file:///Users/michael/.gemini/antigravity/brain/38e62d69-5030-4bc4-b636-47ebae45fb1f/.system_generated/tasks/task-6771.log). Lines 46, 152, 245, 279, 347, and 494 are already fixed; the remaining 6 small fixes in the file are:
  1. **Line ~658**: `linarith` needs `have hdiv2 : 2 * (1 / Real.sqrt t) = 2 / Real.sqrt t := by ring` to connect `1 / √t` and `2 / √t`.
  2. **Line ~850**: `(smooth_tendsto_of_continuous hG2.continuous x)` needs `.comp (tendsto_add_atTop_nat K₀)` before `.const_mul _`.
  3. **Lines ~908 & ~1190**: `rw [Real.exp_neg, ← one_div] at hle` rewrote the LHS `Real.exp (-(y + 2 * s))` instead of `Real.exp (-2)` on the RHS; prove `Real.exp (-2) ≤ 1 / 2` separately and chain `.trans`.
  4. **Line ~942**: `abs_of_pos (by norm_num)` matched `|Real.log ...|` instead of `|(1 / 2 : ℝ)|`; specify `abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)`.
  5. **Lines ~792, ~797, ~819, ~1033, ~1042**: replace `simpa [sub_eq_add_neg]` and `calc _ ≤ _ + _ := abs_sub _ _` around `Real.eulerMascheroniConstant` with explicit `have hs := abs_sub ...; linarith only [...]` so `simp`/`whnf` does not unfold `Real.eulerMascheroniConstant`.
  6. **Lines ~1422 & ~1437**: replace `((HasCompactSupport.intro ...).mul_left).comp_left (by norm_num : (0 : ℝ) ^ 2 = 0)` (which causes higher-order unification timeout in `whnf`) with `HasCompactSupport.intro isCompact_Icc` directly on `fun y => Real.exp (-(8 * y)) * halfWeight hᵢ y ^ 2`.
- Then build `.olean`:
  `cd formal && M=GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PolarPaymentGrowsExponentiallyBelowTheOnset && lake --old env lean -o .lake/build/lib/lean/$M.olean -i .lake/build/lib/lean/$M.ilean $M.lean`

#### Open Task 2: Write & compile Module #9 (`WholeSpacePolarPaymentAndCriticalThresholdLaw.lean`)
- Target file: `formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/WholeSpacePolarPaymentAndCriticalThresholdLaw.lean`
- **What it must prove:**
  1. `eventuallyCriticalPosDef_of_lt_polarPayment`: if `0 < Rstar < R₁` and `∀ A ≥ 0, PolarPaymentAt R₁ A`, then `EventuallyCriticalPosDef Rstar`.
  2. `criticalPositivityThreshold_eq_polarPaymentCriticalThreshold` (closing `criticalPositivityThreshold = criticalNonnegativityThreshold = polarPaymentCriticalThreshold`, since `criticalPositivityThreshold ≤ criticalNonnegativityThreshold ≤ polarPaymentCriticalThreshold` is already proved in [TheCriticalPositivityThresholdLaw.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L2435) / [PolarPaymentThresholdHierarchy.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PolarPaymentThresholdHierarchy.lean#L45)).
  3. `exp_mul_onsetAperture_le_criticalPositivityThreshold` & `log_criticalPositivityThreshold_ge_mul_onsetAperture`: combining (2) with [`exists_polarPaymentAt_exp_of_le_onsetAperture`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PolarPaymentGrowsExponentiallyBelowTheOnset.lean#L1620) yields `R_c(ζ) ≥ c₁ e^{c₂ a*(ζ)}` (`log R_c(ζ) ≥ c₂ a*(ζ) + log c₁`).
  4. Master summary theorem + corollaries packaging all parts of §3.
- **Exact proof blueprint for `eventuallyCriticalPosDef_of_lt_polarPayment` (all building blocks already in corpus):**
  - Suppose `¬ EventuallyCriticalPosDef Rstar` (`0 < Rstar < R₁`, `∀ A ≥ 0, PolarPaymentAt R₁ A`). Extract `N_seq k`, `c_seq k` (`c_seq k ^ 8 / log (N_seq k) → R_lim ∈ [R₀, Rstar]` via [`exists_pos_eventuallyCriticalPosDef`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L156)), and nonzero `x_k = z_k + y_k` with `completeWeilEnergy c_k N_k x_k ≤ 0`, `y_k = ∑_{m=1}^{Q_k} b_{k,m} • v_{k,m}` (`Q_k = ⌊(log N_k)^{13/32}⌋₊`), `z_k ∈ (conductorSubspace Q_k N_k)ᗮ`.
  - Choose `0 < η < 1` small enough that `D_η := (1 - η) * (jordanCoefficient 1 / R_lim) + tiltedPolarFinitePart > criticalPoleWindowCost R₁`.
  - Complete the square on `y_k` via [`eventually_completeWeil_low_packet_signed_approx`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCriticalLowPacketRetainsItsSignedPolarPart.lean) (exactly as in [`eventually_low_packet_correction_ge_retained_pole_budget`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/EveryLowPacketCorrectionHasItsPolarCapacity.lean#L39)):
    `completeWeilEnergy c_k N_k z_k ≤ ∑_{m=1}^{Q_k} ⟪conductorResidualVector c_k m N_k, z_k⟫² / d_{k,m}`, where `d_{k,m} = (1 - η) E_m(c_k) + (if m = 1 then tiltedPolarFinitePart * (c_k / log N_k) else 0)`.
  - Split `z_k = u₀ + u₁ + w` via [`exists_all_ratio_complement_garding_and_far_bridge`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/NegativeDirectionsCannotEscapeLogarithmicWindows.lean#L3369):
    - On `u₀ + u₁` (`q > Q_k ≫ c_k`, entirely above overlap): by symmetry of `B_{c,N}` and `v_m ⊥ v_q` (`m ≤ Q_k < q`), `⟪r_m, u₀ + u₁⟫ = ⟪v_m, B(u₀ + u₁)⟫`, whose norm decays as `O((log N)^{-7}) ‖u₀ + u₁‖` via `exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate`, absorbed by `(κ₀ + 2) ‖z_k‖²`.
    - On the prefix of `w`: absorbed by `(k₁ / 16) ∑_{n ≤ M} x_w(n)²` since `∑_{m=1}^{Q_k} ‖r_m‖² / E_m = O((log N)^{1/4}) ≪ L / (log L)^5` ([`eventually_critical_low_packet_residual_budget`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCriticalLowPacketHasAUniformResidualBudget.lean)).
    - On the collar `y_w` for `m > m₀`: absorbed by `(g₀ L / (64 c^7)) S₇(y_w)` via [`exists_finite_conductor_cutoff_collar_dualSeventh_below_ratio`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/FiniteConductorCollarReductionAndPolarDecoupling.lean#L237).
    - On the finite modes `1 ≤ m ≤ m₀` against normalized collar profile `V_k`: extract a strong `L²` + `L¹` limit `F₀` and smooth window approximations `H_r = windowMollify F₀ A_r δ_r` exactly as in [`eventuallyHighConductorPosDef_of_lt_iInf_windowThreshold`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean#L1978-L2273); modes `2 ≤ m ≤ m₀` vanish by [`tendsto_complete_terminal_nonpolar`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/EveryTerminalWindowHasAPolarConductorSource.lean#L82), mode `m = 1` converges to `generalTerminalPolarSource A_r h_r ^ 2 / D_η` by [`tendsto_complete_terminal_pole`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/EveryTerminalWindowHasAPolarConductorSource.lean#L39), and strict inequality `D_η > criticalPoleWindowCost R₁` + `R_lim ≤ Rstar < R₁` contradicts `PolarPaymentAt R₁ A_r`.

#### Open Task 3: Final Cleanup, Umbrella Wiring & Card Move
1. Remove `#print axioms` from the bottom of [UnrestrictedAtomicGardingFailsAndCollarGardingHolds.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/UnrestrictedAtomicGardingFailsAndCollarGardingHolds.lean) and [TheCriticalPositivityThresholdLaw.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalPositivityThresholdLaw.lean), rebuild those two `.olean`s, and run `lake --old env lean` audit on each new module.
2. Wire the 2 `CriticalArithmeticCorrelationTheory` modules into [CriticalArithmeticCorrelationTheory.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory.lean) and the 7 `ArithmeticHodgeTheoryOfDegenerations` modules into [ArithmeticHodgeTheoryOfDegenerations.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations.lean) (without compiling the umbrellas).
3. Update and move [cact-whole-space-threshold-onset.md](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/cact-whole-space-threshold-onset.md) to `docs/drafts/pipeline/3-formalized/`.