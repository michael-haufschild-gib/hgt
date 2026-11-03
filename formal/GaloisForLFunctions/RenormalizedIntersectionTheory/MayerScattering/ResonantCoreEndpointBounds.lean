import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.PhysicalCoreSpectralBounds
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds

/-!
# Uniform decay at both endpoints of a resonant Mayer core

At a zeta zero, the scaled theta ray has zero Mellin mass. Removing this term before
estimating the theta correlation gives outgoing `a⁻¹` decay. The absolute first Cauchy
moment preserves it. Gamma cancellation and the two-sided zero-free region give a uniform
polynomial-exponential spectral factor; modular inversion supplies the small endpoint.
-/

set_option autoImplicit false

noncomputable section
open Complex Set MeasureTheory
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerThetaRay MayerThetaProduct MayerThetaCore MayerScatteringCore


namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem thetaSum_split {t : ℝ} (ht : 0 < t) :
    thetaSum t = 1 + 2 * ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) := by
  let f : ℤ → ℝ := fun n => Real.exp (-Real.pi * t * (n : ℝ) ^ 2)
  have hf : Summable f := summable_thetaSum ht
  have hp : Summable (fun n : ℕ => f (n : ℤ)) :=
    hf.comp_injective (fun m n h => by omega)
  have hn : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hf.comp_injective (fun m n h => by omega)
  have hhead := (hp.sum_add_tsum_nat_add 1).symm
  have he (n : ℕ) : f (-((n : ℤ) + 1)) =
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) := by
    dsimp [f]
    push_cast
    congr 1
    ring
  have he' (n : ℕ) : f ((n + 1 : ℕ) : ℤ) =
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) := by
    dsimp [f]
    push_cast
    congr 1
    ring
  change (∑' n : ℤ, f n) = _
  rw [tsum_of_nat_of_neg_add_one hp hn, hhead]
  simp only [Finset.sum_range_one, he, he']
  have hz : f 0 = 1 := by simp [f]
  rw [Nat.cast_zero, hz]
  ring

private theorem thetaSum_geometric_bound {t : ℝ} (ht : 0 < t) :
    thetaSum t - 1 ≤ 2 / (Real.pi * t) := by
  have hf := HurwitzKernelBounds.F_nat_zero_le (a := 1) zero_le_one ht
  have he : HurwitzKernelBounds.F_nat 0 1 t =
      ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) := by
    simp only [HurwitzKernelBounds.F_nat, HurwitzKernelBounds.f_nat, pow_zero, one_mul]
  rw [he, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun n => (Real.exp_pos _).le)] at hf
  have hv : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hden : 0 < Real.exp (Real.pi * t) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr hv)
  have hfrac : Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t)) =
      1 / (Real.exp (Real.pi * t) - 1) := by
    rw [show -Real.pi * t = -(Real.pi * t) by ring, Real.exp_neg]
    field_simp
  have hb : Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t)) ≤
      1 / (Real.pi * t) := by
    rw [hfrac]
    exact one_div_le_one_div_of_le hv (by linarith only [Real.add_one_le_exp (Real.pi * t)])
  rw [thetaSum_split ht]
  norm_num only [one_pow, mul_one] at hf
  have hh := hf.trans hb
  calc
    _ = 2 * (∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t)) := by ring
    _ ≤ 2 * (1 / (Real.pi * t)) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring


private theorem thetaSum_le_gaussian_integral {t : ℝ} (ht : 0 < t) :
    thetaSum t ≤ 1 + (Real.sqrt t)⁻¹ := by
  rw [thetaSum_split ht]
  have h := GaloisForLFunctions.HTGeometry.tsum_exp_neg_sq_succ_le ht
  have he : 2 * (1 / (2 * Real.sqrt t)) = (Real.sqrt t)⁻¹ := by ring
  linarith

private theorem thetaRay_real {t : ℝ} (ht : 0 < t) :
    thetaRay t = (((thetaSum t - 1 - (Real.sqrt t)⁻¹) / 2 : ℝ) : ℂ) := by
  rw [thetaRay]
  have hp : (t : ℂ) ^ (-1 / 2 : ℂ) = (((Real.sqrt t)⁻¹ : ℝ) : ℂ) := by
    rw [show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring, Complex.cpow_neg,
      Real.sqrt_eq_rpow, Complex.ofReal_inv, Complex.ofReal_cpow ht.le]
    norm_num
  rw [hp]
  push_cast
  rfl

/-- At the small endpoint, removing the constant term gains a square-root factor. -/
theorem thetaRay_add_half_norm_le {t : ℝ} (ht : 0 < t) :
    ‖thetaRay t + 1 / 2‖ ≤ min (1 / 2 : ℝ) (Real.sqrt t / Real.pi) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hi : 0 < t⁻¹ := inv_pos.mpr ht
  have hθ : thetaSum t = (Real.sqrt t)⁻¹ * thetaSum t⁻¹ := by
    simpa only [← Real.sqrt_eq_rpow] using thetaSum_inv ht
  have he : thetaRay t + 1 / 2 =
      (((Real.sqrt t)⁻¹ * (thetaSum t⁻¹ - 1) / 2 : ℝ) : ℂ) := by
    rw [thetaRay_real ht, hθ]
    push_cast
    ring
  have hn : 0 ≤ (Real.sqrt t)⁻¹ * (thetaSum t⁻¹ - 1) / 2 :=
    div_nonneg (mul_nonneg (inv_nonneg.mpr hs.le) (sub_nonneg.mpr (one_le_thetaSum hi)))
      (by norm_num)
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  apply le_min
  · have hg := thetaSum_le_gaussian_integral hi
    rw [Real.sqrt_inv, inv_inv] at hg
    have hh := mul_le_mul_of_nonneg_left (show thetaSum t⁻¹ - 1 ≤ Real.sqrt t by linarith)
      (inv_nonneg.mpr hs.le)
    rw [inv_mul_cancel₀ hs.ne'] at hh
    linarith only [hh]
  · have hh := mul_le_mul_of_nonneg_left (thetaSum_geometric_bound hi)
      (inv_nonneg.mpr hs.le)
    calc
      _ ≤ (Real.sqrt t)⁻¹ * (2 / (Real.pi * t⁻¹)) / 2 :=
        div_le_div_of_nonneg_right hh (by norm_num)
      _ = _ := by
        field_simp [hs.ne', ht.ne', Real.pi_ne_zero]
        nlinarith only [Real.sq_sqrt ht.le]


private theorem thetaRay_scaled_mellin_zero {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (hz : riemannZeta w = 0) {a : ℝ} (ha : 0 < a) :
    HasMellin (fun t : ℝ => thetaRay (a ^ 2 * t)) (w / 2) 0 := by
  have hm := thetaRay_hasMellin (u := w / 2) (by simp; linarith) (by simp; linarith)
  have he : 2 * (w / 2) = w := by ring
  rw [he, hz, mul_zero] at hm
  refine ⟨(MellinConvergent.comp_mul_left (sq_pos_of_pos ha)).mpr hm.1, ?_⟩
  rw [mellin_comp_mul_left _ _ (sq_pos_of_pos ha), hm.2, smul_zero]

/-- At a zeta zero, the scaled ray has zero Mellin mass. Adding one half to the
other ray exposes its small-endpoint cancellation inside the actual core integral. -/
theorem fieldCore_zero_theta_integral {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w = 0) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (w / 2 - 1) * (thetaRay t + 1 / 2) * thetaRay (a ^ 2 * t)) (Ioi 0) ∧
    fieldCore w a = 2 / Gammaℝ w * ∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (w / 2 - 1) * (thetaRay t + 1 / 2) * thetaRay (a ^ 2 * t) := by
  have hm := thetaRay_scaled_mellin_zero hw hw1 hz ha
  have hs : IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (w / 2 - 1) * thetaRay (a ^ 2 * t)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hm.1
  have ho : IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (w / 2 - 1) * thetaRay t * thetaRay (a ^ 2 * t)) (Ioi 0) := by
    simpa only [MellinConvergent, thetaProduct, smul_eq_mul, mul_assoc] using
      (core_theta_hasMellin hw (by linarith : w.re < 2) him ha).1
  have he (t : ℝ) :
      (t : ℂ) ^ (w / 2 - 1) * (thetaRay t + 1 / 2) * thetaRay (a ^ 2 * t) =
      (t : ℂ) ^ (w / 2 - 1) * thetaRay t * thetaRay (a ^ 2 * t) +
        (1 / 2 : ℂ) * ((t : ℂ) ^ (w / 2 - 1) * thetaRay (a ^ 2 * t)) := by ring
  constructor
  · exact (ho.add (hs.const_mul (1 / 2 : ℂ))).congr (Filter.Eventually.of_forall fun t => (he t).symm)
  · rw [core_theta_integral hw (by linarith : w.re < 2) him ha]
    congr 1
    simp_rw [he]
    rw [integral_add ho (hs.const_mul (1 / 2 : ℂ)), integral_const_mul]
    have hzero : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w / 2 - 1) * thetaRay (a ^ 2 * t)) = 0 := by
      simpa only [mellin, smul_eq_mul] using hm.2
    rw [hzero, mul_zero, add_zero]


private theorem scaled_thetaRay_norm_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ‖thetaRay (a ^ 2 * t)‖ ≤ (Real.sqrt t)⁻¹ / (2 * a) := by
  have hb := (thetaRay_norm_le (mul_pos (sq_pos_of_pos ha) ht)).trans (min_le_right _ _)
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le, mul_inv_rev] at hb
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hb

private theorem corrected_theta_integrand_small {w : ℂ} {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) :
    ‖(t : ℂ) ^ (w / 2 - 1) * (thetaRay t + 1 / 2) * thetaRay (a ^ 2 * t)‖ ≤
      (1 / (2 * Real.pi * a)) * t ^ (w.re / 2 - 1) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (w / 2 - 1).re = w.re / 2 - 1 by simp]
  calc
    _ ≤ (t ^ (w.re / 2 - 1) * (Real.sqrt t / Real.pi)) * ((Real.sqrt t)⁻¹ / (2 * a)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        ((thetaRay_add_half_norm_le ht).trans (min_le_right _ _))
        (Real.rpow_pos_of_pos ht _).le) (scaled_thetaRay_norm_le ha ht)
        (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

private theorem corrected_theta_integrand_large {w : ℂ} {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) :
    ‖(t : ℂ) ^ (w / 2 - 1) * (thetaRay t + 1 / 2) * thetaRay (a ^ 2 * t)‖ ≤
      (1 / (4 * a)) * t ^ (w.re / 2 - 3 / 2) := by
  have hp : t ^ (w.re / 2 - 1) * (Real.sqrt t)⁻¹ = t ^ (w.re / 2 - 3 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    congr 1
    ring
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (w / 2 - 1).re = w.re / 2 - 1 by simp]
  calc
    _ ≤ (t ^ (w.re / 2 - 1) * (1 / 2)) * ((Real.sqrt t)⁻¹ / (2 * a)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        ((thetaRay_add_half_norm_le ht).trans (min_le_left _ _))
        (Real.rpow_pos_of_pos ht _).le) (scaled_thetaRay_norm_le ha ht)
        (norm_nonneg _) (by positivity)
    _ = (1 / (4 * a)) * (t ^ (w.re / 2 - 1) * (Real.sqrt t)⁻¹) := by ring
    _ = _ := by rw [hp]

/-- A resonant field has an outgoing `a⁻¹` bound with an explicit spectral factor. The zero Mellin
mass removes the incoming term before absolute values are taken. -/
theorem fieldCore_resonant_endpoint_bound {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w = 0) {a : ℝ} (ha : 0 < a) :
    ‖fieldCore w a‖ ≤ (2 / (Real.pi * w.re) + 1 / (1 - w.re)) / (‖Gammaℝ w‖ * a) := by
  obtain ⟨hi, he⟩ := fieldCore_zero_theta_integral hw hw1 him hz ha
  have hin : IntegrableOn (fun t : ℝ =>
      ‖(t : ℂ) ^ (w / 2 - 1) * (thetaRay t + 1 / 2) * thetaRay (a ^ 2 * t)‖) (Ioi 0) := hi.norm
  have hlo : -1 < w.re / 2 - 1 := by linarith
  have hhi : w.re / 2 - 3 / 2 < -1 := by linarith
  have hp0 : IntegrableOn (fun t : ℝ => t ^ (w.re / 2 - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' hlo).1
  have hp1 := integrableOn_Ioi_rpow_of_lt hhi (show (0 : ℝ) < 1 by norm_num)
  have hsmall : (∫ t in Ioc (0 : ℝ) 1,
      ‖(t : ℂ) ^ (w / 2 - 1) * (thetaRay t + 1 / 2) * thetaRay (a ^ 2 * t)‖) ≤
      (1 / (2 * Real.pi * a)) * ∫ t in Ioc (0 : ℝ) 1, t ^ (w.re / 2 - 1) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hin.mono_set Ioc_subset_Ioi_self) (hp0.const_mul _)
      measurableSet_Ioc fun t ht => corrected_theta_integrand_small ha ht.1
  have hlarge : (∫ t in Ioi (1 : ℝ),
      ‖(t : ℂ) ^ (w / 2 - 1) * (thetaRay t + 1 / 2) * thetaRay (a ^ 2 * t)‖) ≤
      (1 / (4 * a)) * ∫ t in Ioi (1 : ℝ), t ^ (w.re / 2 - 3 / 2) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hin.mono_set (Ioi_subset_Ioi zero_le_one)) (hp1.const_mul _)
      measurableSet_Ioi fun t ht => corrected_theta_integrand_large ha (zero_lt_one.trans ht)
  have hv0 : (∫ t in Ioc (0 : ℝ) 1, t ^ (w.re / 2 - 1)) = 2 / w.re := by
    rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl hlo), Real.one_rpow,
      Real.zero_rpow (by linarith : w.re / 2 - 1 + 1 ≠ 0)]
    field_simp [hw.ne']
    ring
  have hv1 : (∫ t in Ioi (1 : ℝ), t ^ (w.re / 2 - 3 / 2)) = 2 / (1 - w.re) := by
    rw [integral_Ioi_rpow_of_lt hhi zero_lt_one, Real.one_rpow]
    rw [show w.re / 2 - 3 / 2 + 1 = -(1 - w.re) / 2 by ring]
    field_simp [show 1 - w.re ≠ 0 by linarith]
  have hsum : (∫ t in Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (w / 2 - 1) * (thetaRay t + 1 / 2) * thetaRay (a ^ 2 * t)‖) ≤
      (1 / (Real.pi * w.re) + 1 / (2 * (1 - w.re))) / a := by
    rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hin.mono_set Ioc_subset_Ioi_self) (hin.mono_set (Ioi_subset_Ioi zero_le_one))]
    calc
      _ ≤ (1 / (2 * Real.pi * a)) * (∫ t in Ioc (0 : ℝ) 1, t ^ (w.re / 2 - 1)) +
          (1 / (4 * a)) * (∫ t in Ioi (1 : ℝ), t ^ (w.re / 2 - 3 / 2)) := add_le_add hsmall hlarge
      _ = _ := by rw [hv0, hv1]; field_simp; ring
  have hG : ‖Gammaℝ w‖ ≠ 0 := norm_ne_zero_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos hw)
  rw [he, norm_mul, norm_div, Complex.norm_ofNat]
  calc
    _ ≤ (2 / ‖Gammaℝ w‖) *
        ((1 / (Real.pi * w.re) + 1 / (2 * (1 - w.re))) / a) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans hsum) (by positivity)
    _ = _ := by field_simp

#print axioms fieldCore_resonant_endpoint_bound

private theorem cauchy_first_mass_integrable {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => ‖MayerQuadraticCone.cauchyKernel w t‖) (Ioi 0) := by
  have hm := (MayerCauchyMellinSymbol.cauchyKernel_hasMellin (w := w) (u := 1)
    hw (by norm_num) (by simp; linarith)).1
  simp only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul] at hm
  exact hm.norm

private theorem cauchy_first_mass_integrand {w : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖MayerQuadraticCone.cauchyKernel w t‖ =
      ‖MayerQuadraticCone.averagingFactor w‖⁻¹ *
        (t * (1 + t ^ 2) ^ (-(w.re + 2) / 2)) := by
  rw [MayerQuadraticCone.cauchyKernel, MayerQuadraticCone.cauchyWeight,
    norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  have hre : (-((w + 2) / 2)).re = -(w.re + 2) / 2 := by simp; ring
  rw [hre, mul_assoc]

/-- The absolute first Mellin moment retains only one reciprocal strip distance. -/
theorem cauchy_first_mass_le {w : ℂ} (hw : 0 < w.re) :
    (∫ t in Ioi (0 : ℝ), ‖MayerQuadraticCone.cauchyKernel w t‖) ≤
      (1 / 2 + 1 / w.re) / ‖MayerQuadraticCone.averagingFactor w‖ := by
  let B : ℝ := ‖MayerQuadraticCone.averagingFactor w‖⁻¹
  let f : ℝ → ℝ := fun t => ‖MayerQuadraticCone.cauchyKernel w t‖
  have hi : IntegrableOn f (Ioi 0) := cauchy_first_mass_integrable hw
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : f t ≤ B * t ^ (1 : ℝ) := by
    rw [show f t = B * (t * (1 + t ^ 2) ^ (-(w.re + 2) / 2)) from
      cauchy_first_mass_integrand ht.1, Real.rpow_one]
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos
      (by nlinarith only [sq_nonneg t] : 1 ≤ 1 + t ^ 2)
      (by linarith : -(w.re + 2) / 2 ≤ 0)
    exact mul_le_mul_of_nonneg_left
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow ht.1.le) hB
  have hl (t : ℝ) (ht : 1 < t) : f t ≤ B * t ^ (-w.re - 1) := by
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [show f t = B * (t * (1 + t ^ 2) ^ (-(w.re + 2) / 2)) from
      cauchy_first_mass_integrand ht0]
    apply mul_le_mul_of_nonneg_left _ hB
    have hpow := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ht0)
      (show t ^ 2 ≤ 1 + t ^ 2 by linarith) (show -(w.re + 2) / 2 ≤ 0 by linarith)
    calc
      _ ≤ t * (t ^ 2) ^ (-(w.re + 2) / 2) := mul_le_mul_of_nonneg_left hpow ht0.le
      _ = t ^ (1 : ℝ) * t ^ ((2 : ℝ) * (-(w.re + 2) / 2)) := by
        rw [Real.rpow_one, ← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]
        norm_num
      _ = _ := by rw [← Real.rpow_add ht0]; congr 1; ring
  have hp0 : IntegrableOn (fun t : ℝ => t ^ (1 : ℝ)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 1)).1
  have hp1 := integrableOn_Ioi_rpow_of_lt (by linarith : -w.re - 1 < -1) zero_lt_one
  have hv0 : (∫ t in Ioc (0 : ℝ) 1, t ^ (1 : ℝ)) = 1 / 2 := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by norm_num))]
    norm_num
  have hv1 : (∫ t in Ioi (1 : ℝ), t ^ (-w.re - 1)) = 1 / w.re := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -w.re - 1 < -1) zero_lt_one, Real.one_rpow]
    have he : -w.re - 1 + 1 = -w.re := by ring
    rw [he]
    ring
  have hsmall : (∫ t in Ioc (0 : ℝ) 1, f t) ≤ B * (1 / 2) := by
    calc
      _ ≤ ∫ t in Ioc (0 : ℝ) 1, B * t ^ (1 : ℝ) :=
        setIntegral_mono_on (hi.mono_set Ioc_subset_Ioi_self) (hp0.const_mul B) measurableSet_Ioc hs
      _ = _ := by rw [integral_const_mul, hv0]
  have hlarge : (∫ t in Ioi (1 : ℝ), f t) ≤ B * (1 / w.re) := by
    calc
      _ ≤ ∫ t in Ioi (1 : ℝ), B * t ^ (-w.re - 1) :=
        setIntegral_mono_on (hi.mono_set (Ioi_subset_Ioi zero_le_one)) (hp1.const_mul B)
          measurableSet_Ioi hl
      _ = _ := by rw [integral_const_mul, hv1]
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hsplit
  change (∫ t in Ioi (0 : ℝ), f t) ≤ _
  rw [hsplit]
  calc
    _ ≤ B * (1 / 2) + B * (1 / w.re) := add_le_add hsmall hlarge
    _ = _ := by dsimp [B]; ring

/-- The actual Cauchy transform preserves the resonance's `a⁻¹` endpoint decay. -/
theorem cauchyCore_resonant_endpoint_bound {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w = 0) {a : ℝ} (ha : 0 < a) :
    ‖_root_.RHTower.positiveMellinConvolution (MayerQuadraticCone.cauchyKernel w)
        (fieldCore w) a‖ ≤
      ((2 / (Real.pi * w.re) + 1 / (1 - w.re)) * (1 / 2 + 1 / w.re) /
        (‖Gammaℝ w‖ * ‖MayerQuadraticCone.averagingFactor w‖)) / a := by
  let D : ℝ := (2 / (Real.pi * w.re) + 1 / (1 - w.re)) / ‖Gammaℝ w‖
  have hD : 0 ≤ D := by
    have hr : 0 < 1 - w.re := by linarith
    dsimp [D]
    positivity
  have hmass := cauchy_first_mass_integrable hw
  have hcore := MayerScatteringCore.cauchyKernel_core_integrable hw him ha
  have hpoint (t : ℝ) (ht : 0 < t) :
      ‖MayerQuadraticCone.cauchyKernel w t * fieldCore w (a / t) / (t : ℂ)‖ ≤
        (D / a) * ‖MayerQuadraticCone.cauchyKernel w t‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    have hf : ‖fieldCore w (a / t)‖ ≤ (D / a) * t := by
      convert fieldCore_resonant_endpoint_bound hw hw1 him hz (div_pos ha ht) using 1
      dsimp [D]
      field_simp
    calc
      _ ≤ (‖MayerQuadraticCone.cauchyKernel w t‖ * ((D / a) * t)) / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf (norm_nonneg _)) ht.le
      _ = _ := by field_simp
  change ‖∫ t in Ioi (0 : ℝ),
    MayerQuadraticCone.cauchyKernel w t * fieldCore w (a / t) / (t : ℂ)‖ ≤ _
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ),
        ‖MayerQuadraticCone.cauchyKernel w t * fieldCore w (a / t) / (t : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), (D / a) * ‖MayerQuadraticCone.cauchyKernel w t‖ :=
      setIntegral_mono_on hcore.norm (hmass.const_mul _) measurableSet_Ioi hpoint
    _ = (D / a) * ∫ t in Ioi (0 : ℝ), ‖MayerQuadraticCone.cauchyKernel w t‖ := by
      rw [integral_const_mul]
    _ ≤ (D / a) * ((1 / 2 + 1 / w.re) / ‖MayerQuadraticCone.averagingFactor w‖) :=
      mul_le_mul_of_nonneg_left (cauchy_first_mass_le hw) (by positivity)
    _ = _ := by dsimp [D]; ring

#print axioms cauchy_first_mass_le

private theorem endpoint_inv_gammaR_averaging_norm {w : ℂ} (hw : 0 < w.re) :
    1 / (‖Gammaℝ w‖ * ‖MayerQuadraticCone.averagingFactor w‖) =
      ‖w‖ * Real.pi ^ ((w.re - 1) / 2) / ‖Gamma ((w + 1) / 2)‖ := by
  have h := congrArg norm (gammaR_mul_averagingFactor hw)
  rw [norm_mul, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos] at h
  have hre : ((1 - w) / 2).re = (1 - w.re) / 2 := by simp
  rw [hre] at h
  rw [h]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  rw [← Real.rpow_neg Real.pi_pos.le, show -((1 - w.re) * (2 : ℝ)⁻¹) = (w.re - 1) * (2 : ℝ)⁻¹ by ring]
  ring

private theorem cauchyCore_resonant_gamma_bound {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w = 0) {a : ℝ} (ha : 0 < a) :
    ‖_root_.RHTower.positiveMellinConvolution (MayerQuadraticCone.cauchyKernel w)
        (fieldCore w) a‖ ≤
      ((2 / (Real.pi * w.re) + 1 / (1 - w.re)) * (1 / 2 + 1 / w.re) *
        ‖w‖ * Real.pi ^ ((w.re - 1) / 2) / ‖Gamma ((w + 1) / 2)‖) / a := by
  calc
    _ ≤ ((2 / (Real.pi * w.re) + 1 / (1 - w.re)) * (1 / 2 + 1 / w.re) /
        (‖Gammaℝ w‖ * ‖MayerQuadraticCone.averagingFactor w‖)) / a :=
      cauchyCore_resonant_endpoint_bound hw hw1 him hz ha
    _ = ((2 / (Real.pi * w.re) + 1 / (1 - w.re)) * (1 / 2 + 1 / w.re) *
        (1 / (‖Gammaℝ w‖ * ‖MayerQuadraticCone.averagingFactor w‖))) / a := by ring
    _ = _ := by rw [endpoint_inv_gammaR_averaging_norm hw]; ring

private theorem upperMayer_right_reciprocal_bound (s : upperMayerResonances) :
    1 / (1 - 2 * s.1.re) ≤ 116 * s.1.im := by
  have h := (upperMayerResonance_reciprocal_bound (reflectUpperResonance s)).2
  have hre : (reflectUpperResonance s).1.re = 1 / 2 - s.1.re := by
    simp [reflectUpperResonance_coe, riemannMayerReflect]
  have him : (reflectUpperResonance s).1.im = s.1.im := by
    simp [reflectUpperResonance_coe, riemannMayerReflect]
  rw [hre, him, show 2 * (1 / 2 - s.1.re) = 1 - 2 * s.1.re by ring] at h
  exact h

private theorem upperMayerCore_outgoing_growth_bound :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : upperMayerResonances, ∀ a > 0,
      ‖mayerPeriodCore s.1 a‖ ≤
        (C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)) / a := by
  obtain ⟨C, N, hC, hgamma⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_inv_Gamma_strip (1 / 2) 1
  refine ⟨54288 * C, N + 3, by positivity, fun s a ha => ?_⟩
  obtain ⟨hy, hedge⟩ := upperMayerResonance_reciprocal_bound s
  have hright := upperMayer_right_reciprocal_bound s
  have hx : 0 < s.1.re := s.2.2.1
  have hx1 : s.1.re < 1 / 2 := s.2.2.2.1
  have hy0 : 0 < s.1.im := s.2.1
  have hr : 0 < 2 * s.1.re := by linarith
  have hr1 : 0 < 1 - 2 * s.1.re := by linarith
  have hfirst : 2 / (Real.pi * (2 * s.1.re)) ≤ 1 / (2 * s.1.re) := by
    have hpi : (2 : ℝ) / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
    simpa only [div_div] using div_le_div_of_nonneg_right hpi hr.le
  have hS : 2 / (Real.pi * (2 * s.1.re)) + 1 / (1 - 2 * s.1.re) ≤
      232 * (1 + s.1.im) := by linarith only [hfirst, hedge, hright]
  have hT : 1 / 2 + 1 / (2 * s.1.re) ≤ 117 * (1 + s.1.im) := by
    linarith only [hedge, hy0]
  have hnorm : ‖2 * s.1‖ ≤ 2 * (1 + s.1.im) := by
    have hs : ‖s.1‖ ≤ s.1.re + s.1.im := by
      calc
        _ = ‖(s.1.re : ℂ) + (s.1.im : ℂ) * I‖ := by rw [Complex.re_add_im]
        _ ≤ ‖(s.1.re : ℂ)‖ + ‖(s.1.im : ℂ) * I‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul, Complex.norm_real, Complex.norm_real,
          Complex.norm_I, mul_one, Real.norm_of_nonneg hx.le, Real.norm_of_nonneg hy0.le]
    rw [norm_mul, Complex.norm_ofNat]
    linarith only [hs, hx1]
  have hpi : Real.pi ^ ((2 * s.1.re - 1) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hgim : (s.1 + 1 / 2).im = s.1.im := by simp
  have hG := hgamma (s.1 + 1 / 2) (by simp; linarith) (by simp; linarith)
    (by simpa only [hgim, abs_of_pos hy0] using (show 1 ≤ s.1.im by linarith))
  rw [hgim, abs_of_pos hy0, norm_inv] at hG
  have hG' : ‖Gamma (s.1 + 1 / 2)‖⁻¹ ≤
      C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2) :=
    hG.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0.le (by linarith) N) hC)
      (Real.exp_pos _).le)
  have hm : (2 / (Real.pi * (2 * s.1.re)) + 1 / (1 - 2 * s.1.re)) *
      (1 / 2 + 1 / (2 * s.1.re)) * ‖2 * s.1‖ * Real.pi ^ ((2 * s.1.re - 1) / 2) /
      ‖Gamma (s.1 + 1 / 2)‖ ≤
        (54288 * C) * (1 + s.1.im) ^ (N + 3) * Real.exp (Real.pi * s.1.im / 2) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (232 * (1 + s.1.im)) * (117 * (1 + s.1.im)) * (2 * (1 + s.1.im)) * 1 *
          (C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)) := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul (mul_le_mul hS hT (by positivity) (by positivity)) hnorm
              (norm_nonneg _) (by positivity)
          · exact hpi
          · exact Real.rpow_nonneg Real.pi_pos.le _
          · positivity
        · exact hG'
        · positivity
        · positivity
      _ = _ := by rw [pow_add]; ring
  have hw : 0 < (2 * s.1).re := by simp; linarith
  have hw1 : (2 * s.1).re < 1 := by simp; linarith
  have him : 0 < (2 * s.1).im := by simp; linarith
  have hz : riemannZeta (2 * s.1) = 0 :=
    (isMayerScatteringResonance_iff_zeta_zero hx hx1).mp s.2.2
  have hb := cauchyCore_resonant_gamma_bound hw hw1 him hz ha
  change ‖mayerPeriodCore s.1 a‖ ≤ _ at hb
  rw [show (2 * s.1).re = 2 * s.1.re by simp,
    show (2 * s.1 + 1) / 2 = s.1 + 1 / 2 by ring] at hb
  exact hb.trans (div_le_div_of_nonneg_right hm ha.le)

/-- At every actual resonance, one uniform spectral factor controls both physical endpoints.
The zero Mellin mass gives `a⁻¹` at infinity; modular inversion gives `a^(1−2 Re s)` at zero. -/
theorem upperMayerCore_two_endpoint_growth_bound :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : upperMayerResonances, ∀ a > 0,
      ‖mayerPeriodCore s.1 a‖ ≤
        (C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)) *
          min a⁻¹ (a ^ (1 - 2 * s.1.re)) := by
  obtain ⟨C, N, hC, hb⟩ := upperMayerCore_outgoing_growth_bound
  refine ⟨C, N, hC, fun s a ha => ?_⟩
  have hy := s.2.1
  have hK : 0 ≤ C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2) := by positivity
  rw [mul_min_of_nonneg _ _ hK]
  refine le_min (by simpa only [div_eq_mul_inv] using hb s a ha) ?_
  have hi := lewisModularInversion_mayerPeriodCore s.2.2.1 s.2.1 ha
  change (a : ℂ) ^ (-(2 * s.1)) * mayerPeriodCore s.1 a⁻¹ = mayerPeriodCore s.1 a at hi
  rw [← hi, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha,
    show (-(2 * s.1)).re = -(2 * s.1.re) by simp]
  have hp : a ^ (-(2 * s.1.re)) * a = a ^ (1 - 2 * s.1.re) := by
    calc
      _ = a ^ (-(2 * s.1.re)) * a ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ha]; congr 1; ring
  calc
    _ ≤ a ^ (-(2 * s.1.re)) *
        ((C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)) / a⁻¹) :=
      mul_le_mul_of_nonneg_left (hb s a⁻¹ (inv_pos.mpr ha)) (Real.rpow_pos_of_pos ha _).le
    _ = _ := by rw [div_inv_eq_mul, mul_left_comm, hp]

#print axioms upperMayerCore_two_endpoint_growth_bound

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
