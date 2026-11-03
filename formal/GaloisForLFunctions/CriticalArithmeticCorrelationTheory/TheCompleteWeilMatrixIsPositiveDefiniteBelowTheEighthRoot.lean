import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheDeepRowPairingClosesTheEighthRootSchur

/-!
# The complete Weil matrix is positive definite below the eighth root

For every `0 < α < 1/8`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
`completeWeilMatrix tiltedUnitSpline c N` is positive definite.

Split `x = y + u₀ + u₁ + w` along `V_{Q₁} ⊂ V_{R₀} ⊂ V_{R₁}` (`Q₁ = ⌊L^{α+1/4}⌋`,
`R₀ = ⌊exp √L⌋`, `R₁ = ⌊N^{θ₁}⌋`, `L = log N`). The conductor block `y` has the polylogarithmic
floor `⟨W'y, y⟩ ≥ (1/4) Σ E_m a_m²` (`W' = W − κ/(2c⁷)`), the complement keeps block reserves
`1`, `√L/32`, `3bk/(16c⁷)` (`exists_complement_block_reserves_below_one_eighth`), and the Schur
coupling is paid row by row: the deep rows `n R₀ ≤ N` see only `O(m(1 + log m)²/L)` of the
residual `r_m`, the top rows only `O(√L/L)` of `u₀` (`spectralFloor_posDef_of_blocks`,
`deep_inverse_energy_mass_le`, `schur_scalars_one_eighth`).

* `eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_eighth`
* `eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_eighth`
* `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_eighth`
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

/-- **Positive definiteness of `spectralFloorWeilMatrix c N` below `1 / 8`.** For every
`0 < α < 1 / 8`, eventually in `N`, `spectralFloorWeilMatrix c N` is positive definite uniformly
across `1 ≤ c ≤ (log N)^α`. -/
theorem eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_eighth
    {α : ℝ} (hα : 0 < α) (hα_lt : α < oneEighthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (spectralFloorWeilMatrix c N).PosDef := by
  have hα8 : α < 1 / 8 := hα_lt
  obtain ⟨θ₁, b, hθ₁, hθ₁_4096, hb, hb8, hcompN⟩ :=
    exists_complement_block_reserves_below_one_eighth hα hα8
  obtain ⟨K_inv, hK_inv, hinv⟩ := exists_tiltedUnitSpline_quadratic_inv_energy_residual_sum_le
  obtain ⟨C_p, C_s, C_q, K_up, hCp, hCs, hCq, hKup, hdeep⟩ :=
    exists_deepMass_conductorResidual_le contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_sh, hC_sh, hsh⟩ := exists_tiltedUnitSpline_conductor_uniform_affineShellCorrection_linear_log_rate
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (hsh 2 (by norm_num) 4)
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hκ₀ : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
  have hq : 0 < α + 1 / 4 := by linarith only [hα]
  have hq_hi : α + 1 / 4 ≤ 1 / 2 := by linarith only [hα8]
  have hαq : α + 2 * (α + 1 / 4) < 1 := by linarith only [hα8]
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℝ, ν = (1 - 8 * α) / 64 := ⟨_, rfl⟩
  have hν : 0 < ν := by rw [hνdef]; linarith only [hα8]
  have hν8 : 64 * ν ≤ 1 - 8 * α := by rw [hνdef]; linarith only
  obtain ⟨kv, hkvdef⟩ : ∃ kv : ℕ, kv = ⌈1 / ν⌉₊ + 1 := ⟨_, rfl⟩
  have hkv : 1 ≤ kv := by omega
  have hkvν : 1 / (kv : ℝ) ≤ ν := by
    have hceil := Nat.le_ceil (1 / ν)
    have hk0 : (0 : ℝ) < kv := by exact_mod_cast hkv
    rw [div_le_iff₀ hk0]
    have h1 : (1 / ν) + 1 ≤ (kv : ℝ) := by rw [hkvdef]; push_cast; linarith only [hceil]
    have h2 : ν * (1 / ν) = 1 := mul_one_div_cancel hν.ne'
    nlinarith only [h1, h2, hν]
  obtain ⟨Kβ, hKβ⟩ : ∃ Kβ : ℝ, Kβ = C_s + 4 + 162 +
      32 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) ^ 2 +
      2048 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) ^ 2 + C_q +
      46875 * K_up + 2457600 + 6 * (65536 * C_sh ^ 2) := ⟨_, rfl⟩
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_tiltedUnitSpline_polylog_conductorSubspace_energy_ge hα hα_lt hq hαq,
    hcompN, hinv (α + 1 / 4) hq.le kv hkv,
    eventually_three_cutoff_bounds_one_ninth hq hq_hi hθ₁ hθ₁_4096,
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1 hν 1),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1
      (by norm_num : (0 : ℝ) < 1 / 2) 16),
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop
      (5120 * K_inv + 2048 * explicitConductorCutoffConstant * K_inv / (3 * b * θ₁) +
        9216 * (C_p + 1) / tiltedSplineSpectralFloorConstant),
    hLlim.eventually_ge_atTop (2000 + |Kβ| + 2 * |Y₀|)] with
      N hlowN hcompN' hinvN hcut hLX hpolyν hpoly16 hν_big hL_big
  dsimp only [Function.comp_def] at hpolyν hpoly16 hν_big hL_big
  intro c hc1 hcup
  obtain ⟨hQ2, hQR₀, hR₀R₁, hQ_le, -, -, hH₀_ub, hlogR₀_lb, h36_R₀, -, -, -⟩ := hcut
  have hKβL : Kβ ≤ Real.log (N : ℝ) := by
    linarith only [hL_big, le_abs_self Kβ, abs_nonneg Y₀]
  have hY₀L : 2 * Y₀ ≤ Real.log (N : ℝ) := by
    linarith only [hL_big, le_abs_self Y₀, abs_nonneg Kβ]
  have hL2000 : 2000 ≤ Real.log (N : ℝ) := by
    linarith only [hL_big, abs_nonneg Y₀, abs_nonneg Kβ]
  have hL1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hL2000]
  have hL0 : 0 < Real.log (N : ℝ) := by linarith only [hL2000]
  have hN1 : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    subst this; simp at hL0
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcL : c ≤ Real.log (N : ℝ) := hcup.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα8] : α ≤ 1))
  have hlogL0 : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg hL1
  have hpolyν1 : 1 + Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) ^ ν := by
    simpa only [one_mul, pow_one] using hpolyν
  have hpoly16' : 16 * (1 + Real.log (Real.log (N : ℝ))) ≤ Real.log (N : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [pow_one] using hpoly16
  have hVc : 1 + Real.log c ≤ Real.log (N : ℝ) ^ ν := by
    have := Real.log_le_log hc0 hcL; linarith only [this, hpolyν1]
  have hR₀2 : 2 ≤ ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ := hQ2.trans hQR₀
  obtain ⟨-, hwidth, -, -, hR₀6, -, -, -, -, -, -, -⟩ :=
    rpow_horizon_N_bounds_one_ninth hN1 hR₀2 hc1 hL2000 hLX hcL h36_R₀
  -- `L¹⁸ ≤ N`
  have hNL : Real.log (N : ℝ) ^ 18 ≤ N := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    calc Real.log (N : ℝ) ^ 18 ≤ ((N : ℝ) ^ (1 / 36 : ℝ)) ^ 18 := pow_le_pow_left₀ hL0.le hLX 18
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      _ ≤ N := by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num : (1 / 2 : ℝ) ≤ 1)
  -- the conductor cutoff
  have hQ1 : (1 : ℝ) ≤ (⌊Real.log (N : ℝ) ^ (α + 1 / 4)⌋₊ : ℝ) := by
    exact_mod_cast (show 1 ≤ ⌊Real.log (N : ℝ) ^ (α + 1 / 4)⌋₊ by omega)
  have hQh : (⌊Real.log (N : ℝ) ^ (α + 1 / 4)⌋₊ : ℝ) ≤ Real.log (N : ℝ) ^ (1 / 2 : ℝ) :=
    hQ_le.trans (Real.rpow_le_rpow_of_exponent_le hL1 hq_hi)
  have hQL : (⌊Real.log (N : ℝ) ^ (α + 1 / 4)⌋₊ : ℝ) ≤ Real.log N :=
    hQ_le.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hq_hi] : α + 1 / 4 ≤ 1))
  have hlQ : 1 + Real.log (⌊Real.log (N : ℝ) ^ (α + 1 / 4)⌋₊ : ℝ) ≤ Real.log (N : ℝ) ^ ν := by
    have := Real.log_le_log (by linarith only [hQ1]) hQL; linarith only [this, hpolyν1]
  -- the deep rows `n R₀ ≤ N`
  have hR₀1 : (1 : ℝ) ≤ (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ) := by
    exact_mod_cast (show 1 ≤ ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ by omega)
  obtain ⟨hR₀L8, hlogY, hYY₀, hQY⟩ := deep_cutoff_facts (by linarith only [hL2000]) hc1 hcL
    hpoly16' hR₀1 hlogR₀_lb hY₀L hQh
  have hΨD := deep_inverse_energy_mass_le (Q := ⌊Real.log (N : ℝ) ^ (α + 1 / 4)⌋₊) hCp hCs hCq hKup
    hdeep (hY₀ _ hYY₀).2 (by linarith only [hL2000]) hc1 hcL hQL hQY hR₀L8 hNL
    (by field_simp) hlogY (hKβ ▸ hKβL)
  -- the full residual mass
  have hΨ := (hinvN c hc1 hwidth ⌊Real.log (N : ℝ) ^ (α + 1 / 4)⌋₊ hQ_le).trans
    (pole_rate_le (K := K_inv * (c ^ 7 + (⌊Real.log (N : ℝ) ^ (α + 1 / 4)⌋₊ : ℝ) ^ 2 *
      (1 + Real.log (⌊Real.log (N : ℝ) ^ (α + 1 / 4)⌋₊ : ℝ)) ^ 2)) (by positivity) hc1 hcL hL1 hkv
      hkvν (le_trans (pow_le_pow_right₀ hL1 (by norm_num)) hNL))
  obtain ⟨ha, hb', hc'⟩ := schur_scalars_one_eighth hα hν hν8 hL1 hc1 hcup hVc hQ1 hQ_le hlQ hR₀1
    hH₀_ub hK_inv.le hCp hκ₀ hb hθ₁ hD hν_big
  have hRNX := sq_add_one_mul_le_of_pow_six_le hR₀2 hR₀6
  have h18_R₀ : 18 * (1 + Real.log (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ)) ≤
      Real.log (N : ℝ) := by
    have := Real.log_natCast_nonneg ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊
    linarith only [h36_R₀, this]
  refine spectralFloor_posDef_of_blocks hc1 hQR₀ hR₀R₁ (hlowN c hc1 hcup)
    (μ₀ := 1) (μ₁ := Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32)
    (μ_S := 3 * b * (θ₁ * Real.log (N : ℝ) / (2 * explicitConductorCutoffConstant)) / (16 * c ^ 7))
    (fun hu₀ hu₀' hu₁ hu₁' hw => by
      have h := hcompN' c hc1 hcup hu₀ hu₀' hu₁ hu₁' hw
      linarith only [h])
    (fun hu => sum_topRows_sq_le hR₀2 hR₀1 hRNX h18_R₀ hu)
    hΨ hΨD hc' ha hb'

/-- **Uniform `c⁻⁷` spectral floor below `1 / 8`.** Throughout `1 ≤ c ≤ (log N)^α`
(`0 < α < 1 / 8`), the complete Weil quadratic form of `tiltedUnitSpline` dominates
`(tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2` for every horizon vector `x`. -/
theorem eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_eighth
    {α : ℝ} (hα : 0 < α) (hα_lt : α < oneEighthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 ≤
          completeWeilEnergy tiltedUnitSpline c N x := by
  filter_upwards [eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_eighth
    hα hα_lt] with N hpos c hc hcup x
  have hA := spectralFloorWeilMatrix_isHermitian c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hpos c hc hcup)
  have hnonneg : 0 ≤ ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) x, x⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [spectralFloorWeilMatrix_inner] at hnonneg
  linarith only [hnonneg]

/-- **All-vector positivity of the complete Weil matrix below `1 / 8`.** For every
`0 < α < 1 / 8`, eventually in `N`, `completeWeilMatrix tiltedUnitSpline c N` is positive definite
uniformly across `1 ≤ c ≤ (log N)^α`. -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_eighth
    {α : ℝ} (hα : 0 < α) (hα_lt : α < oneEighthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_eighth
    hα hα_lt] with N hfloor c hc hcup
  refine posDef_of_inner_pos_on_ne_zero (completeWeilMatrix_isHermitian tiltedUnitSpline c N)
    fun x hx_ne => ?_
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hpos : 0 < (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 :=
    mul_pos (div_pos tiltedSplineSpectralFloorConstant_pos (by positivity))
      (sq_pos_of_pos (norm_pos_iff.mpr hx_ne))
  exact hpos.trans_le (hfloor c hc hcup x)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
