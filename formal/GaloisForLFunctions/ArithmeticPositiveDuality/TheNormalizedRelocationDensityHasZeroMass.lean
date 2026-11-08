import GaloisForLFunctions.ArithmeticPositiveDuality.NormalizedRelocationHasASignedDensity
import GaloisForLFunctions.RHTower.PrimeDeletionResidueQuantization
import GaloisForLFunctions.RHTower.ZetaPoleSplit

/-!
# The normalized relocation density is integrable and has zero mass

The uniform Bernoulli estimate gives inverse-square decay. Its Mellin transform
therefore extends to `Re s>-1`. Multiplying by the donor quartic and using the
entire pole unit of zeta extends the rational identity across all donor zeros.
At zero, the normalized numerator forces the total density mass to vanish.
-/

noncomputable section
set_option autoImplicit false

open Complex MeasureTheory Filter Topology Set Asymptotics
open RHTower GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Mellin transform of the real quartic density. -/
def quartetDensityMellin (γ₁ γ₂ c : ℝ) : ℂ → ℂ :=
  halfPlaneMellin (fun Y => (quartetDensity γ₁ γ₂ c Y : ℂ))

theorem intervalIntegrable_quartetDensity {γ₁ γ₂ : ℝ}
    (hγ₁ : γ₁ ≠ 0) (hγ₂ : γ₂ ≠ 0) (c : ℝ) {y : ℝ} (hy : 1 ≤ y) :
    IntervalIntegrable (fun Y => (quartetDensity γ₁ γ₂ c Y : ℂ)) volume 1 y := by
  have hglobal := integrableOn_quartetDensity hγ₁ hγ₂ c (s := 2) (by norm_num)
  have hlocal : IntervalIntegrable
      (fun Y : ℝ => (Y : ℂ) ^ (-(2 : ℂ)) * (quartetDensity γ₁ γ₂ c Y : ℂ)) volume 1 y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
      (hglobal.mono_set (fun _ hY => hY.1))
  have hp := hlocal.mul_continuousOn
    (show ContinuousOn (fun Y : ℝ => (Y : ℂ) ^ 2) (uIcc 1 y) by fun_prop)
  apply (intervalIntegrable_congr ?_).mp hp
  intro Y hY
  rw [uIoc_of_le hy] at hY
  have hYc : (Y : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hY.1).ne'
  change ((Y : ℂ) ^ (-(2 : ℂ)) * (quartetDensity γ₁ γ₂ c Y : ℂ)) * (Y : ℂ) ^ 2 = _
  rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  field_simp [hYc]

theorem quartetDensity_isBigO_inverse_square {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (c : ℝ) :
    (fun Y : ℝ => (quartetDensity γ₁ γ₂ c Y : ℂ)) =O[atTop]
      (fun Y : ℝ => Y ^ (-(2 : ℝ))) := by
  obtain ⟨A, X, _, hX, hb⟩ := exists_quartetDensity_inverse_square_bound hγ₁ hγ₂ hz₁ hz₂ c
  apply IsBigO.of_bound A
  filter_upwards [eventually_ge_atTop X] with Y hY
  have hY0 : 0 ≤ Y := (zero_le_one.trans hX).trans hY
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hY0 _),
    Real.rpow_neg hY0, Real.rpow_two]
  simpa only [div_eq_mul_inv] using hb Y hY

/-- The density is Mellin integrable throughout `Re s>-1`. -/
theorem integrableOn_quartetDensity_mellin_extended {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (c : ℝ)
    {s : ℂ} (hs : -1 < s.re) :
    IntegrableOn (fun Y : ℝ => (quartetDensity γ₁ γ₂ c Y : ℂ) * (Y : ℂ) ^ (-s)) (Ioi 1) := by
  have hf := fun y hy => intervalIntegrable_quartetDensity hγ₁.ne' (hγ₁.trans hγ₂).ne' c (y := y) hy
  have hO := quartetDensity_isBigO_inverse_square hγ₁ hγ₂ hz₁ hz₂ c
  have hs' : (-2 : ℝ) < (s - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hs]
  simpa only [sub_add_cancel] using PrimeDeletion.integrableOn_mul_cpow hf hO hs'

/-- In particular, the unweighted density is absolutely integrable. -/
theorem integrableOn_quartetDensity_unweighted {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (c : ℝ) :
    IntegrableOn (fun Y => (quartetDensity γ₁ γ₂ c Y : ℂ)) (Ioi 1) := by
  simpa only [neg_zero, Complex.cpow_zero, mul_one] using
    integrableOn_quartetDensity_mellin_extended hγ₁ hγ₂ hz₁ hz₂ c (s := 0) (by norm_num)

/-- The convergent Mellin integral is holomorphic across the donor line. -/
theorem differentiableAt_quartetDensityMellin {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (c : ℝ)
    {s : ℂ} (hs : -1 < s.re) : DifferentiableAt ℂ (quartetDensityMellin γ₁ γ₂ c) s := by
  have hf := fun y hy => intervalIntegrable_quartetDensity hγ₁.ne' (hγ₁.trans hγ₂).ne' c (y := y) hy
  have hO := quartetDensity_isBigO_inverse_square hγ₁ hγ₂ hz₁ hz₂ c
  have hs' : (-2 : ℝ) < (s - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have h := (PrimeDeletion.differentiableAt_integral_cpow hf hO hs').comp s
    (differentiableAt_id.sub_const (1 : ℂ))
  unfold quartetDensityMellin halfPlaneMellin
  simpa only [Function.comp_def, sub_add_cancel, id_eq] using h

/-- The rational Mellin identity continues after clearing its donor denominator. -/
theorem quartetDensityMellin_cleared_identity {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (c : ℝ)
    {s : ℂ} (hs : -1 < s.re) :
    zeroRelocationDen γ₁ γ₂ s * quartetDensityMellin γ₁ γ₂ c s =
      (c : ℂ) * s * zetaPoleUnit s := by
  let U : Set ℂ := {z | -1 < z.re}
  let F : ℂ → ℂ := fun z => zeroRelocationDen γ₁ γ₂ z * quartetDensityMellin γ₁ γ₂ c z
  let G : ℂ → ℂ := fun z => (c : ℂ) * z * zetaPoleUnit z
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hd : DifferentiableAt ℂ (zeroRelocationDen γ₁ γ₂) z := by
      unfold zeroRelocationDen
      fun_prop
    exact (hd.mul (differentiableAt_quartetDensityMellin hγ₁ hγ₂ hz₁ hz₂ c hz)).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ G U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z _
    exact (((differentiableAt_id.const_mul (c : ℂ)).mul
      (differentiable_zetaPoleUnit z))).differentiableWithinAt
  have hfg : F =ᶠ[𝓝 (2 : ℂ)] G := by
    have hright : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hright.mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hzre : 1 < z.re := hz
    have hz1 : z ≠ 1 := by intro he; rw [he] at hzre; norm_num at hzre
    have hd := zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ (s := z) (by linarith only [hzre])
    have hm := mellin_quartetDensity hγ₁ hγ₂ c hzre
    rw [← zeroRelocationDen_eq_pair_product] at hm
    have hM : quartetDensityMellin γ₁ γ₂ c z =
        riemannZeta z * (c : ℂ) * z * (z - 1) / zeroRelocationDen γ₁ γ₂ z := by
      simpa only [quartetDensityMellin, halfPlaneMellin, mul_comm] using hm
    dsimp only [F, G]
    rw [hM, zetaPoleUnit_of_ne hz1]
    field_simp [hd]
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt (-1)).isPreconnected
    (by norm_num [U] : (2 : ℂ) ∈ U) hfg hs

/-- Endpoint normalization forces the absolutely integrable density to have total mass zero. -/
theorem quartetDensity_totalMass_eq_zero {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (c : ℝ) :
    (∫ Y in Ioi (1 : ℝ), (quartetDensity γ₁ γ₂ c Y : ℂ)) = 0 := by
  have h := quartetDensityMellin_cleared_identity hγ₁ hγ₂ hz₁ hz₂ c (s := 0) (by norm_num)
  have hd := zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ (s := 0) (by norm_num)
  simp only [mul_zero, zero_mul] at h
  have hM := (mul_eq_zero.mp h).resolve_left hd
  simpa only [quartetDensityMellin, halfPlaneMellin, neg_zero, Complex.cpow_zero, mul_one] using hM

theorem integral_quartetDensity_eq_zero {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (c : ℝ) :
    (∫ Y in Ioi (1 : ℝ), quartetDensity γ₁ γ₂ c Y) = 0 := by
  have h := quartetDensity_totalMass_eq_zero hγ₁ hγ₂ hz₁ hz₂ c
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The inverse first moment records the finite value left by the canceled zeta pole. -/
theorem quartetDensityMellin_one {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (c : ℝ) :
    quartetDensityMellin γ₁ γ₂ c 1 = (c : ℂ) / zeroRelocationDen γ₁ γ₂ 1 := by
  have h := quartetDensityMellin_cleared_identity hγ₁ hγ₂ hz₁ hz₂ c (s := 1) (by norm_num)
  have hd := zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ (s := 1) (by norm_num)
  apply (eq_div_iff hd).mpr
  simpa only [zetaPoleUnit_one, mul_one, mul_comm] using h

theorem quartetDensityMellin_one_re (γ₁ γ₂ c : ℝ) :
    (quartetDensityMellin γ₁ γ₂ c 1).re =
      ∫ Y in Ioi (1 : ℝ), quartetDensity γ₁ γ₂ c Y / Y := by
  unfold quartetDensityMellin halfPlaneMellin
  simp only [Complex.cpow_neg_one, ← div_eq_mul_inv, ← Complex.ofReal_div]
  rw [integral_complex_ofReal, Complex.ofReal_re]

/-- Although its total mass vanishes, the normalized correction has strictly negative inverse moment. -/
theorem normalizedRelocation_inverse_moment_neg {γ₁ γ₂ : ℝ}
    (hγ₁ : 1 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) :
    (∫ Y in Ioi (1 : ℝ), quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) Y / Y) < 0 := by
  rw [← quartetDensityMellin_one_re,
    quartetDensityMellin_one (lt_trans zero_lt_one hγ₁) hγ₂ hz₁ hz₂,
    ← normalizedRelocation_deriv_one hγ₁ (hγ₁.trans hγ₂)]
  exact normalizedRelocation_deriv_one_neg hγ₁ (hγ₁.trans hγ₂)

/-- Positive and negative bands have fixed width inside every sufficiently large cell. -/
theorem eventually_quartetDensity_sign_bands {γ₁ γ₂ c : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0) (hc : c < 0) :
    ∀ᶠ N : ℕ in atTop,
      (∀ θ ∈ Icc (0 : ℝ) (1 / 12), -c / 48 ≤
        (N : ℝ) ^ 2 * quartetDensity γ₁ γ₂ c ((N : ℝ) + θ)) ∧
      (∀ θ ∈ Icc (1 / 3 : ℝ) (2 / 3),
        (N : ℝ) ^ 2 * quartetDensity γ₁ γ₂ c ((N : ℝ) + θ) ≤ c / 48) := by
  obtain ⟨C, _, hb⟩ := exists_uniform_quartetDensity_cell_remainder hγ₁ hγ₂ hz₁ hz₂ c
  have hlim : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
  have hε : 0 < -c / 144 := by linarith only [hc]
  filter_upwards [hb, hlim.eventually (Iio_mem_nhds hε)] with N hN hsmall
  constructor
  · intro θ hθ
    have hB : 1 / 12 ≤ unitCellBernoulli θ := by
      dsimp only [unitCellBernoulli]
      nlinarith only [hθ.2, sq_nonneg θ]
    have hθ1 : θ < 1 := lt_of_le_of_lt hθ.2 (by norm_num)
    have herr := (hN θ hθ.1 hθ1).trans_lt hsmall
    have hlow := (abs_lt.mp herr).1
    have hmul := mul_le_mul_of_nonpos_left hB hc.le
    linarith only [hlow, hmul, hc]
  · intro θ hθ
    have hB : unitCellBernoulli θ ≤ -1 / 18 := by
      have hp := mul_nonneg (sub_nonneg.mpr hθ.1) (sub_nonneg.mpr hθ.2)
      dsimp only [unitCellBernoulli]
      nlinarith only [hp]
    have hθ0 : 0 ≤ θ := le_trans (by norm_num) hθ.1
    have hθ1 : θ < 1 := lt_of_le_of_lt hθ.2 (by norm_num)
    have herr := (hN θ hθ0 hθ1).trans_lt hsmall
    have hhigh := (abs_lt.mp herr).2
    have hmul := mul_le_mul_of_nonpos_left hB hc.le
    linarith only [hhigh, hmul]

/-- Unconditionally, actual donor zeros produce a nontrivial integrable correction
with zero total mass and both signs in every sufficiently large unit interval. -/
theorem exists_integrable_signed_quartet_density :
    ∃ γ₁ γ₂ : ℝ, 1 < γ₁ ∧ γ₁ < γ₂ ∧
      riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0 ∧
      IntegrableOn
        (fun Y => (quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) Y : ℂ)) (Ioi 1) ∧
      (∫ Y in Ioi (1 : ℝ), quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) Y) = 0 ∧
      (∫ Y in Ioi (1 : ℝ), quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) Y / Y) < 0 ∧
      ∀ᶠ N : ℕ in atTop,
        0 < quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) N ∧
          quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂) ((N : ℝ) + 1 / 2) < 0 := by
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hz₁, hz₂⟩ := exists_two_critical_donor_ordinates
  have h₁ : 0 < γ₁ := lt_trans zero_lt_one hγ₁
  exact ⟨γ₁, γ₂, hγ₁, hγ₂, hz₁, hz₂,
    integrableOn_quartetDensity_unweighted h₁ hγ₂ hz₁ hz₂ _,
    integral_quartetDensity_eq_zero h₁ hγ₂ hz₁ hz₂ _,
    normalizedRelocation_inverse_moment_neg hγ₁ hγ₂ hz₁ hz₂,
    eventually_normalizedRelocationDensity_opposite_signs hγ₁ hγ₂ hz₁ hz₂⟩

#print axioms integrableOn_quartetDensity_unweighted
#print axioms quartetDensityMellin_cleared_identity
#print axioms quartetDensity_totalMass_eq_zero
#print axioms normalizedRelocation_inverse_moment_neg
#print axioms eventually_quartetDensity_sign_bands
#print axioms exists_integrable_signed_quartet_density

end GaloisForLFunctions.ArithmeticPositiveDuality
