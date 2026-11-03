import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.CoreCauchyAnalyticContinuation

/-!
# Scattering remainders of the actual resonant core

The exponentially small Eisenstein field tail and the Cauchy kernel's full
moment strip retain the exact outgoing charge with a sharp power remainder.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology
open GaloisForLFunctions RenormalizedIntersectionTheory
open MayerScatteringCore MayerQuadraticCone MayerCauchyMellinSymbol

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem exp_cusp_le_inverse_square {a : ℝ} (ha : 0 < a) :
    Real.exp (-(2 * Real.pi * a)) ≤ (Real.pi ^ 2)⁻¹ * a ^ (-2 : ℝ) := by
  have hp : 0 < Real.pi * a := mul_pos Real.pi_pos ha
  have hbase : Real.pi * a ≤ Real.exp (Real.pi * a) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hi : Real.exp (-(Real.pi * a)) ≤ (Real.pi * a)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hp hbase
  calc
    _ = Real.exp (-(Real.pi * a)) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    _ ≤ ((Real.pi * a)⁻¹) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le hi 2
    _ = _ := by rw [Real.rpow_neg ha.le, Real.rpow_two]; field_simp

private theorem normalized_tail_second_power {w : ℂ} {a : ℝ} (ha : 1 ≤ a) :
    ‖normalizedTail w a‖ ≤
      (_root_.RHTower.tailConst ((w - 1) / 2) / (‖Gammaℝ w‖ * Real.pi ^ 2)) *
        a ^ (-w.re / 2 - 2) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hT := _root_.RHTower.norm_cuspTailPart_le_exp ((w - 1) / 2) 0
    (Y := a) (by linarith only [ha])
  have hC := _root_.RHTower.tailConst_nonneg ((w - 1) / 2)
  rw [normalizedTail, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ha0,
    show (-w / 2).re = -w.re / 2 by simp]
  calc
    _ ≤ (a ^ (-w.re / 2) / ‖Gammaℝ w‖) *
        (_root_.RHTower.tailConst ((w - 1) / 2) * Real.exp (-(2 * Real.pi * a))) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (a ^ (-w.re / 2) / ‖Gammaℝ w‖) *
        (_root_.RHTower.tailConst ((w - 1) / 2) * ((Real.pi ^ 2)⁻¹ * a ^ (-2 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (exp_cusp_le_inverse_square ha0) hC) (by positivity)
    _ = _ := by
      rw [show -w.re / 2 - 2 = -w.re / 2 + (-2) by ring, Real.rpow_add ha0]
      ring

/-- Subtracting the outgoing field charge permits every power strictly inside
its Cauchy moment strip, uniformly over the positive physical axis. -/
theorem fieldCore_scattering_remainder_bound {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w = 0) {δ : ℝ} (hδ : 0 < δ) (hδw : δ < w.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0,
      ‖fieldCore w a + scatteringCoefficient w * (a : ℂ) ^ (-1 : ℂ)‖ ≤
        C * a ^ (-1 - δ) := by
  let K : ℝ := (2 / (Real.pi * w.re) + 1 / (1 - w.re)) / ‖Gammaℝ w‖
  let D : ℝ := _root_.RHTower.tailConst ((w - 1) / 2) / (‖Gammaℝ w‖ * Real.pi ^ 2)
  have hwgap : 0 < 1 - w.re := sub_pos.mpr hw1
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hD : 0 ≤ D := div_nonneg (_root_.RHTower.tailConst_nonneg _) (by positivity)
  refine ⟨K + ‖scatteringCoefficient w‖ + D, by positivity, fun a ha => ?_⟩
  by_cases ha1 : 1 ≤ a
  · have he : fieldCore w a + scatteringCoefficient w * (a : ℂ) ^ (-1 : ℂ) =
        normalizedTail w a := by
      rw [fieldCore_eq_tail hw him ha, hz, zero_mul, sub_zero, sub_add_cancel]
    rw [he]
    calc
      _ ≤ D * a ^ (-w.re / 2 - 2) := normalized_tail_second_power ha1
      _ ≤ D * a ^ (-1 - δ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ha1 (by linarith only [hw, hw1, hδw])) hD
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hK, norm_nonneg (scatteringCoefficient w)])
        (Real.rpow_pos_of_pos ha _).le
  · have ha1' : a ≤ 1 := (lt_of_not_ge ha1).le
    have hf := fieldCore_resonant_endpoint_bound hw hw1 him hz ha
    have hP : ‖scatteringCoefficient w * (a : ℂ) ^ (-1 : ℂ)‖ =
        ‖scatteringCoefficient w‖ * a ^ (-1 : ℝ) := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha]
      norm_num
    have hpow : a ^ (-1 : ℝ) ≤ a ^ (-1 - δ) :=
      Real.rpow_le_rpow_of_exponent_ge ha ha1' (by linarith only [hδ])
    calc
      _ ≤ ‖fieldCore w a‖ + ‖scatteringCoefficient w * (a : ℂ) ^ (-1 : ℂ)‖ := norm_add_le _ _
      _ ≤ K / a + ‖scatteringCoefficient w‖ * a ^ (-1 : ℝ) := by
        rw [hP]
        exact add_le_add (by simpa only [K, div_mul_eq_div_div] using hf) le_rfl
      _ = (K + ‖scatteringCoefficient w‖) * a ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        ring
      _ ≤ (K + ‖scatteringCoefficient w‖) * a ^ (-1 - δ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD)
        (Real.rpow_pos_of_pos ha _).le

#print axioms fieldCore_scattering_remainder_bound


private theorem cauchy_power_mass_integrable {w : ℂ} (hw : 0 < w.re) {r : ℝ}
    (hr : -1 < r) (hrw : r < w.re + 1) :
    IntegrableOn (fun t : ℝ => ‖cauchyKernel w t‖ * t ^ (r - 1)) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((r : ℂ) - 1) • cauchyKernel w t‖)
      (Ioi 0) := (cauchyKernel_hasMellin hw (u := (r : ℂ))
    (by simpa only [Complex.ofReal_re] using hr)
    (by simpa only [Complex.ofReal_re] using hrw)).1.norm
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  change ‖(t : ℂ) ^ ((r : ℂ) - 1) * cauchyKernel w t‖ =
    ‖cauchyKernel w t‖ * t ^ (r - 1)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  ring

private theorem cauchy_field_scattering_remainder_bound {w : ℂ}
    (hw : 0 < w.re) (hw1 : w.re < 1) (him : 0 < w.im) (hz : riemannZeta w = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδw : δ < w.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0,
      ‖_root_.RHTower.positiveMellinConvolution (cauchyKernel w) (fieldCore w) a +
        (2 * riemannZeta (w - 1) / (w - 1)) * (a : ℂ) ^ (-1 : ℂ)‖ ≤
      C * a ^ (-1 - δ) := by
  obtain ⟨C, hC, hb⟩ := fieldCore_scattering_remainder_bound hw hw1 him hz hδ hδw
  let r : ℝ := 1 + δ
  have hM := cauchy_power_mass_integrable hw
    (show -1 < r by dsimp only [r]; linarith only [hδ])
    (show r < w.re + 1 by dsimp only [r]; linarith only [hδw])
  let M : ℝ := ∫ t in Ioi (0 : ℝ), ‖cauchyKernel w t‖ * t ^ (r - 1)
  have hM0 : 0 ≤ M := integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (norm_nonneg _) (Real.rpow_pos_of_pos ht _).le)
  refine ⟨C * M, mul_nonneg hC hM0, fun a ha => ?_⟩
  have hc := cauchyKernel_core_integrable hw him ha
  have hp := power_integrable hw (u := 1) (by norm_num)
    (by simp; linarith only [hw]) ha
  let F : ℝ → ℂ := fun t => cauchyKernel w t *
    (fieldCore w (a / t) + scatteringCoefficient w * ((a / t : ℝ) : ℂ) ^ (-1 : ℂ)) /
      (t : ℂ)
  have hi : IntegrableOn F (Ioi 0) := by
    apply (hc.add (hp.const_mul (scatteringCoefficient w))).congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only [F, Pi.add_apply]
    ring
  have he : (∫ t in Ioi (0 : ℝ), F t) =
      _root_.RHTower.positiveMellinConvolution (cauchyKernel w) (fieldCore w) a +
        (2 * riemannZeta (w - 1) / (w - 1)) * (a : ℂ) ^ (-1 : ℂ) := by
    have hf : ∀ t : ℝ, F t = cauchyKernel w t * fieldCore w (a / t) / (t : ℂ) +
        scatteringCoefficient w *
          (cauchyKernel w t * ((a / t : ℝ) : ℂ) ^ (-1 : ℂ) / (t : ℂ)) := by
      intro t
      dsimp only [F]
      ring
    simp_rw [hf]
    rw [integral_add hc (hp.const_mul _), integral_const_mul]
    change _root_.RHTower.positiveMellinConvolution (cauchyKernel w) (fieldCore w) a +
      scatteringCoefficient w *
        _root_.RHTower.positiveMellinConvolution (cauchyKernel w)
          (fun x : ℝ => (x : ℂ) ^ (-1 : ℂ)) a = _
    rw [power_convolution hw (u := 1) (by norm_num) (by simp; linarith only [hw]) ha,
      mul_left_comm (scatteringCoefficient w), scatteringCoefficient_mul_symbol_one hw him]
    ring
  have hbound (t : ℝ) (ht : 0 < t) : ‖F t‖ ≤
      (C * a ^ (-r)) * (‖cauchyKernel w t‖ * t ^ (r - 1)) := by
    have htC : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hf := hb (a / t) (div_pos ha ht)
    have hr : -1 - δ = -r := by dsimp only [r]; ring
    rw [hr] at hf
    have hpow : (a / t) ^ (-r) / t = a ^ (-r) * t ^ (r - 1) := by
      rw [Real.div_rpow ha.le ht.le, Real.rpow_neg ht.le, div_inv_eq_mul,
        Real.rpow_sub ht, Real.rpow_one]
      ring
    dsimp only [F]
    rw [norm_div, norm_mul, htC]
    calc
      _ ≤ (‖cauchyKernel w t‖ * (C * (a / t) ^ (-r))) / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf (norm_nonneg _)) ht.le
      _ = (C * ‖cauchyKernel w t‖) * ((a / t) ^ (-r) / t) := by ring
      _ = _ := by rw [hpow]; ring
  rw [← he]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), (C * a ^ (-r)) *
        (‖cauchyKernel w t‖ * t ^ (r - 1)) :=
      setIntegral_mono_on hi.norm (hM.const_mul _) measurableSet_Ioi hbound
    _ = _ := by
      rw [integral_const_mul]
      change (C * a ^ (-r)) * M = _
      rw [show -r = -1 - δ by dsimp only [r]; ring]
      ring

/-- The actual resonant PM core retains its nonzero outgoing charge with every
remainder exponent strictly below the Cauchy moment boundary. -/
theorem mayerPeriodCore_scattering_remainder_bound (s : upperMayerResonances)
    {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 2 * s.1.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0,
      ‖mayerPeriodCore s.1 a +
        (2 * riemannZeta (2 * s.1 - 1) / (2 * s.1 - 1)) * (a : ℂ) ^ (-1 : ℂ)‖ ≤
      C * a ^ (-1 - δ) := by
  have hw : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  have hw1 : (2 * s.1).re < 1 := by simp; linarith only [s.2.2.2.1]
  have him : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  have hz := (isMayerScatteringResonance_iff_zeta_zero s.2.2.1 s.2.2.2.1).mp s.2.2
  exact cauchy_field_scattering_remainder_bound hw hw1 him hz hδ (by simpa using hδs)

#print axioms mayerPeriodCore_scattering_remainder_bound


/-- Inversion transfers the sharp outgoing remainder to the lower cusp, with
an error exponent arbitrarily close to one. -/
theorem mayerPeriodCore_scattering_lower_bound (s : upperMayerResonances)
    {ε : ℝ} (hε : 0 < ε) (hεs : ε < 2 * s.1.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0,
      ‖mayerPeriodCore s.1 a + (2 * riemannZeta (2 * s.1 - 1) / (2 * s.1 - 1)) *
        (a : ℂ) ^ (1 - 2 * s.1)‖ ≤ C * a ^ (1 - ε) := by
  let δ : ℝ := 2 * s.1.re - ε
  have hδ : 0 < δ := sub_pos.mpr hεs
  have hδs : δ < 2 * s.1.re := by dsimp only [δ]; linarith only [hε]
  obtain ⟨C, hC, hb⟩ := mayerPeriodCore_scattering_remainder_bound s hδ hδs
  refine ⟨C, hC, fun a ha => ?_⟩
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hcore := lewisModularInversion_mayerPeriodCore s.2.2.1 s.2.1 ha
  rw [lewisModularInversion] at hcore
  have hp : (a : ℂ) ^ (-(2 * s.1)) * (((1 / a : ℝ) : ℂ) ^ (-1 : ℂ)) =
      (a : ℂ) ^ (1 - 2 * s.1) := by
    rw [Complex.cpow_neg_one, Complex.ofReal_div, Complex.ofReal_one, one_div, inv_inv]
    calc
      _ = (a : ℂ) ^ (-(2 * s.1)) * (a : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (a : ℂ) ^ (-(2 * s.1) + 1) := (Complex.cpow_add _ _ haC).symm
      _ = _ := by congr 1; ring
  have he : mayerPeriodCore s.1 a + (2 * riemannZeta (2 * s.1 - 1) / (2 * s.1 - 1)) *
      (a : ℂ) ^ (1 - 2 * s.1) =
      (a : ℂ) ^ (-(2 * s.1)) *
        (mayerPeriodCore s.1 (1 / a) + (2 * riemannZeta (2 * s.1 - 1) / (2 * s.1 - 1)) *
          (((1 / a : ℝ) : ℂ) ^ (-1 : ℂ))) := by
    rw [mul_add, mul_left_comm ((a : ℂ) ^ (-(2 * s.1))), hp, one_div, hcore]
  have hr : (1 / a) ^ (-1 - δ) = a ^ (1 + δ) := by
    rw [one_div, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    congr 1
    ring
  rw [he, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha,
    Complex.neg_re, show (2 * s.1).re = 2 * s.1.re by simp]
  calc
    _ ≤ a ^ (-(2 * s.1.re)) * (C * (1 / a) ^ (-1 - δ)) :=
      mul_le_mul_of_nonneg_left (hb _ (one_div_pos.mpr ha)) (Real.rpow_pos_of_pos ha _).le
    _ = C * (a ^ (-(2 * s.1.re)) * a ^ (1 + δ)) := by rw [hr]; ring
    _ = _ := by
      rw [← Real.rpow_add ha]
      congr 2
      dsimp only [δ]
      ring

#print axioms mayerPeriodCore_scattering_lower_bound

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
