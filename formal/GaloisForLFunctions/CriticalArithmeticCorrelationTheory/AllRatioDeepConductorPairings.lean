import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalSchurPairingRetainsTheCollarWeight
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalLowPacketHasAUniformResidualBudget

/-!
# Deep conductor residuals vanish at every positive critical ratio

The deep inverse-energy estimate leaves a strict exponent gap after bounding the
critical overlap by `(log N)^(2/15)`. This supplies arbitrarily small first-band
payments without restricting the critical ratio.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity ArithmeticHodgeTheoryOfDegenerations

/-- The deep inverse-energy residual of the whole low packet tends to zero at every critical ratio. -/
theorem eventually_critical_deep_residual_le
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ}
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ Icc 1 ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊,
        deepMass (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ)
          (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N) /
          completedConductorEnergy tiltedUnitSpline (c N) m) ≤ ε := by
  obtain ⟨C_p, C_s, C_q, K_up, hCp, hCs, hCq, hKup, hdeep⟩ :=
    exists_deepMass_conductorResidual_le contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_sh, -, hsh⟩ := exists_tiltedUnitSpline_conductor_uniform_affineShellCorrection_linear_log_rate
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (hsh 2 (by norm_num) 4)
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  let Kβ := C_s + 4 + 162 +
    32 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) ^ 2 +
    2048 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) ^ 2 + C_q +
    46875 * K_up + 2457600 + 6 * (65536 * C_sh ^ 2)
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_three_cutoff_bounds_one_ninth
      (by norm_num : (0 : ℝ) < 13 / 32) (by norm_num : (13 / 32 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 4096) (le_refl (1 / 4096 : ℝ)),
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1
      (by norm_num : (0 : ℝ) < 1 / 64) 1),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1
      (by norm_num : (0 : ℝ) < 1 / 2) 16),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 15)).comp hLlim).eventually_ge_atTop
      (72 * (C_p + 1) / (κ * ε)),
    hLlim.eventually_ge_atTop (2000 + |Kβ| + 2 * |Y₀|),
    eventually_criticalCurve_le_log_rpow hc hcrit (by norm_num : (1 / 8 : ℝ) < 2 / 15)]
    with N hcut hLX hpoly hpoly16 hlargeD hlarge hcN
  dsimp only [Function.comp_def] at hpoly hpoly16 hlargeD hlarge hcN
  have hc1 := hc N
  let L := Real.log (N : ℝ)
  let Q := ⌊L ^ (13 / 32 : ℝ)⌋₊
  let R := ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊
  change 72 * (C_p + 1) / (κ * ε) ≤ L ^ (1 / 15 : ℝ) at hlargeD
  obtain ⟨hQ2, hQR, -, hQup, -, -, hRup, hRlow, h36, -, -, -⟩ := hcut
  change 2 ≤ Q at hQ2
  have hL2000 : 2000 ≤ L := by linarith only [hlarge, abs_nonneg Kβ, abs_nonneg Y₀]
  have hL1 : 1 ≤ L := by linarith only [hL2000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN1 : 1 ≤ N := by
    by_contra hn
    have : N = 0 := by omega
    subst this
    simp [L] at hL0
  have hc0 : 0 < (c N) := zero_lt_one.trans_le hc1
  have hcL : (c N) ≤ L := hcN.trans ((Real.rpow_le_rpow_of_exponent_le hL1
    (by norm_num : (2 / 15 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
  have hR2 : 2 ≤ R := hQ2.trans hQR
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hQhalf : (Q : ℝ) ≤ L ^ (1 / 2 : ℝ) :=
    hQup.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hQL : (Q : ℝ) ≤ L := hQhalf.trans ((Real.rpow_le_rpow_of_exponent_le hL1
    (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hpoly' : 1 + Real.log L ≤ L ^ (1 / 64 : ℝ) := by
    simpa only [one_mul, pow_one] using hpoly
  have hpoly16' : 16 * (1 + Real.log L) ≤ L ^ (1 / 2 : ℝ) := by
    simpa only [pow_one] using hpoly16
  obtain ⟨hR8, hlogY, hYY₀, hQY⟩ := deep_cutoff_facts (Y₀ := Y₀)
    (by linarith only [hL2000]) hc1 hcL hpoly16' hR1 hRlow
    (by linarith only [hlarge, le_abs_self Y₀, abs_nonneg Kβ]) hQhalf
  have hNL : L ^ 18 ≤ (N : ℝ) := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    calc
      _ ≤ ((N : ℝ) ^ (1 / 36 : ℝ)) ^ 18 := pow_le_pow_left₀ hL0.le hLX 18
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      _ ≤ N := (Real.rpow_le_rpow_of_exponent_le hN1R
        (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hD := deep_inverse_energy_mass_le (Q := Q) hCp hCs hCq hKup hdeep (hY₀ _ hYY₀).2
    (by linarith only [hL2000]) hc1 hcL hQL hQY hR8 hNL
    (by field_simp) hlogY (by
      change Kβ ≤ L
      linarith only [hlarge, le_abs_self Kβ, abs_nonneg Y₀])
  have hc7 : (c N) ^ 7 ≤ L ^ (14 / 15 : ℝ) := by
    convert pow_le_rpow_mul hL0 hc0.le hcN 7 using 1; norm_num
  have hlogQ : 1 + Real.log (Q : ℝ) ≤ L ^ (1 / 64 : ℝ) := by
    have h := Real.log_le_log hQ0 hQL
    linarith only [h, hpoly']
  have hQterm : (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 ≤ L ^ (14 / 15 : ℝ) := by
    have h₁ := pow_le_rpow_mul hL0 (Nat.cast_nonneg Q) hQup 2
    have h₂ := pow_le_rpow_mul hL0
      (by linarith only [Real.log_natCast_nonneg Q] : 0 ≤ 1 + Real.log (Q : ℝ)) hlogQ 2
    exact (mul_le_rpow_add hL0 h₁ (sq_nonneg _) h₂).trans
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hDsmall : 8 * ((C_p + 1) / L) *
      ((8 * (c N) ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) / κ) ≤ ε := by
    calc
      _ ≤ 72 * (C_p + 1) / κ * (L ^ (14 / 15 : ℝ) / L) := by
        have h := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right
            (show 8 * (c N) ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 ≤
              9 * L ^ (14 / 15 : ℝ) by linarith only [hc7, hQterm]) hκ.le)
          (show 0 ≤ 8 * ((C_p + 1) / L) by positivity)
        exact h.trans_eq (by ring)
      _ = 72 * (C_p + 1) / κ / L ^ (1 / 15 : ℝ) := by
        have he : L ^ (14 / 15 : ℝ) * L ^ (1 / 15 : ℝ) = L := by
          rw [← Real.rpow_add hL0]; norm_num
        field_simp
        nlinarith only [he]
      _ ≤ ε := by
        rw [div_le_iff₀ (by positivity)]
        have he : 72 * (C_p + 1) / (κ * ε) = (72 * (C_p + 1) / κ) / ε := by ring
        rw [he] at hlargeD
        exact (div_le_iff₀ hε).mp hlargeD |>.trans_eq (mul_comm _ _)
  exact hD.trans hDsmall


/-- All first-band, second-band, and prefix Schur costs are paid; only the literal collar cost remains. -/
theorem eventually_critical_schur_pairing_except_collar
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {κ_P : ℝ} (hκP : 0 < κ_P) :
    ∀ᶠ N : ℕ in atTop,
      let Q := ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊
      let r := fun m => Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N
      ∀ s : Finset ℕ, s ⊆ Icc 1 Q → ∀ M : ℕ, M ≤ N →
      ∀ u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N,
      ∀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        8 * (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 /
          completedConductorEnergy tiltedUnitSpline (c N) m) ≤
        ‖u₀‖ ^ 2 + (Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
          (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ 5) *
            (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
          48 * (∑ m ∈ s, topCollarDualSeventhMass M N (r m) /
            completedConductorEnergy tiltedUnitSpline (c N) m) *
              topCollarSeventhMass M N (primeHorizonExtension w) := by
  have hLlim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_critical_low_packet_residual_budget hc hR hcrit,
    eventually_critical_deep_residual_le hc hcrit (by norm_num : (0 : ℝ) < 1 / 96),
    eventually_critical_deep_residual_payment, hLlim.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hLlim).eventually_ge_atTop 768,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 3 / 4) (48 / κ_P))]
    with N hfull hdeep htop hL1 hlarge hprefix
  dsimp only [Function.comp_def] at hL1 hlarge hprefix
  intro Q r s hs M hMN u₀ hu₀ u₁ w
  let L := Real.log (N : ℝ)
  let X := ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊
  let E := fun m => completedConductorEnergy tiltedUnitSpline (c N) m
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hE : ∀ m ∈ Icc 1 Q, 0 < E m := by
    intro m hm
    have hfloor := spectralFloor_conductor_energy_ge (hc N) (mem_Icc.mp hm).1
    have hpos : 0 < tiltedSplineSpectralFloorConstant / (2 * c N ^ 7) :=
      div_pos tiltedSplineSpectralFloorConstant_pos (by have := hc N; positivity)
    change 0 < completedConductorEnergy tiltedUnitSpline (c N) m
    linarith only [hfloor, hpos]
  have hΨ : (∑ m ∈ s, ‖r m‖ ^ 2 / E m) ≤ L ^ (1 / 4 : ℝ) :=
    (sum_le_sum_of_subset_of_nonneg hs (fun m hm _ => div_nonneg (sq_nonneg _) (hE m hm).le)).trans hfull
  have hD : (∑ m ∈ s, deepMass (X : ℝ) (r m) / E m) ≤ 1 / 96 :=
    (sum_le_sum_of_subset_of_nonneg hs (fun m hm _ =>
      div_nonneg (deepMass_nonneg _ _) (hE m hm).le)).trans hdeep
  have hT := (htop 1 le_rfl (Real.one_le_rpow hL1 (by norm_num : (0 : ℝ) ≤ 1 / 8))).2 u₀ hu₀
  have hpair := pairing_sum_le_deep_prefix_weighted_collar (X := (X : ℝ))
    hMN (fun m hm => hE m (hs hm)) u₀ u₁ w hΨ hD le_rfl
  change 48 * L ^ (1 / 4 : ℝ) *
    (∑ n ∈ topRows N (X : ℝ), primeHorizonExtension u₀ n ^ 2) ≤ (1 / 2 : ℝ) * ‖u₀‖ ^ 2 at hT
  have hsecond : 24 * L ^ (1 / 4 : ℝ) ≤ L ^ (1 / 2 : ℝ) / 32 := by
    have he : L ^ (1 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have h := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hL0.le (1 / 4 : ℝ))
    nlinarith only [h, he]
  have ht0 : 0 < (1 + Real.log L) ^ 5 := by
    have := Real.log_nonneg hL1
    positivity
  have hpre : 48 * L ^ (1 / 4 : ℝ) ≤ κ_P * L / (1 + Real.log L) ^ 5 := by
    have h := mul_le_mul_of_nonneg_right hprefix
      (show 0 ≤ κ_P * L ^ (1 / 4 : ℝ) by positivity)
    have he : ((48 / κ_P) * (1 + Real.log L) ^ 5) * (κ_P * L ^ (1 / 4 : ℝ)) =
        48 * L ^ (1 / 4 : ℝ) * (1 + Real.log L) ^ 5 := by field_simp
    have hpowers : L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [he] at h
    apply (le_div_iff₀ ht0).mpr
    calc
      _ ≤ L ^ (3 / 4 : ℝ) * (κ_P * L ^ (1 / 4 : ℝ)) := h
      _ = κ_P * L := by rw [← mul_assoc, mul_comm _ κ_P, mul_assoc, hpowers]
  have hsecond' := mul_le_mul_of_nonneg_right hsecond (sq_nonneg ‖u₁‖)
  have hpre' := mul_le_mul_of_nonneg_right hpre
    (show 0 ≤ ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 from sum_nonneg fun _ _ => sq_nonneg _)
  linarith only [hpair, hT, hsecond', hpre']

#print axioms eventually_critical_deep_residual_le
#print axioms eventually_critical_schur_pairing_except_collar

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
