import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheDeepRowPairingClosesTheEighthRootSchur

/-!
# Deep rows pay the first band at the critical overlap

Through conductor `(log N)^(13/32)`, the deep inverse-energy residual tends
to zero even at `c = (log N)^(1/8)`. The first band's top rows have mass
`O((log N)^(-1/2))`, which pays the full `O((log N)^(1/4))` residual budget.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

/-- At the critical exponent, deep residual mass still tends to zero through
`(log N)^(13/32)`, while the first band's terminal mass pays the full residual. -/
theorem eventually_critical_deep_residual_payment :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
      (∑ m ∈ Icc 1 ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊,
        deepMass (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ)
          (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N) /
          completedConductorEnergy tiltedUnitSpline c m) ≤ 1 / 96 ∧
      ∀ u ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N,
        48 * Real.log (N : ℝ) ^ (1 / 4 : ℝ) *
          (∑ n ∈ topRows N (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ),
            primeHorizonExtension u n ^ 2) ≤ (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
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
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hLlim).eventually_ge_atTop
      (6912 * (C_p + 1) / κ),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hLlim).eventually_ge_atTop 960,
    hLlim.eventually_ge_atTop (2000 + |Kβ| + 2 * |Y₀|)]
    with N hcut hLX hpoly hpoly16 hlargeD hlargeT hlarge
  dsimp only [Function.comp_def] at hpoly hpoly16 hlargeD hlargeT hlarge
  intro c hc1 hc
  let L := Real.log (N : ℝ)
  let Q := ⌊L ^ (13 / 32 : ℝ)⌋₊
  let R := ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊
  change 6912 * (C_p + 1) / κ ≤ L ^ (1 / 8 : ℝ) at hlargeD
  change 960 ≤ L ^ (1 / 4 : ℝ) at hlargeT
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
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcL : c ≤ L := hc.trans ((Real.rpow_le_rpow_of_exponent_le hL1
    (by norm_num : (1 / 8 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
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
  have hc7 : c ^ 7 ≤ L ^ (7 / 8 : ℝ) := by
    convert pow_le_rpow_mul hL0 hc0.le hc 7 using 1 <;> norm_num
  have hlogQ : 1 + Real.log (Q : ℝ) ≤ L ^ (1 / 64 : ℝ) := by
    have h := Real.log_le_log hQ0 hQL
    linarith only [h, hpoly']
  have hQterm : (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 ≤ L ^ (7 / 8 : ℝ) := by
    have h₁ := pow_le_rpow_mul hL0 (Nat.cast_nonneg Q) hQup 2
    have h₂ := pow_le_rpow_mul hL0
      (by linarith only [Real.log_natCast_nonneg Q] : 0 ≤ 1 + Real.log (Q : ℝ)) hlogQ 2
    exact (mul_le_rpow_add hL0 h₁ (sq_nonneg _) h₂).trans
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hDsmall : 8 * ((C_p + 1) / L) *
      ((8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) / κ) ≤ 1 / 96 := by
    calc
      _ ≤ 72 * (C_p + 1) / κ * (L ^ (7 / 8 : ℝ) / L) := by
        have h := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right
            (show 8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 ≤
              9 * L ^ (7 / 8 : ℝ) by linarith only [hc7, hQterm]) hκ.le)
          (show 0 ≤ 8 * ((C_p + 1) / L) by positivity)
        exact h.trans_eq (by ring)
      _ = 72 * (C_p + 1) / κ / L ^ (1 / 8 : ℝ) := by
        have he : L ^ (7 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L := by
          rw [← Real.rpow_add hL0]; norm_num
        field_simp
        nlinarith only [he]
      _ ≤ 1 / 96 := by
        rw [div_le_iff₀ (by positivity)]
        have he : 6912 * (C_p + 1) / κ = 96 * (72 * (C_p + 1) / κ) := by ring
        linarith only [hlargeD, he]
  refine ⟨hD.trans hDsmall, ?_⟩
  intro u hu
  obtain ⟨-, -, -, -, hR6, -, -, -, -, -, -, -⟩ :=
    rpow_horizon_N_bounds_one_ninth hN1 hR2 hc1 hL2000 hLX hcL h36
  have h18 : 18 * (1 + Real.log (R : ℝ)) ≤ L := by
    linarith only [h36, Real.log_natCast_nonneg R]
  have htop := sum_topRows_sq_le hR2 hR1 (sq_add_one_mul_le_of_pow_six_le hR2 hR6) h18 hu
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hhalf1 : 1 ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hnum : 2 * (Real.log (2 * (R : ℝ)) + 3) ≤ 10 * L ^ (1 / 2 : ℝ) := by
    rw [Real.log_mul (by norm_num) (by linarith only [hR1])]
    linarith only [hRup, hlog2, hhalf1]
  have hr : 48 * L ^ (1 / 4 : ℝ) * (2 * (Real.log (2 * (R : ℝ)) + 3) / L) ≤ 1 / 2 := by
    calc
      _ ≤ 480 * (L ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) / L) := by
        have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hL0.le)
          (show 0 ≤ 48 * L ^ (1 / 4 : ℝ) by positivity)
        exact h.trans_eq (by ring)
      _ = 480 / L ^ (1 / 4 : ℝ) := by
        have he : L ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) = L := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
        field_simp
        nlinarith only [he]
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith only [hlargeT]
  calc
    _ ≤ 48 * L ^ (1 / 4 : ℝ) *
        (2 * (Real.log (2 * (R : ℝ)) + 3) / L * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left htop (by positivity)
    _ ≤ (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
