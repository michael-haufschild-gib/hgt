import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.GaussianPhysicalCoreSynthesis
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.ResonantCoreEndpointBounds

/-!
# Whole-line Haar and Mellin synthesis of Gaussian core sums

The resonant endpoint estimate controls both ends of the positive axis. Its common
Mellin strip permits integration of the actual Gaussian series term by term. Each individual
core has a holomorphic Mellin transform on its larger resonant strip.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology Zeta23
open scoped lp ENNReal ComplexConjugate
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open ArithmeticPolarization SpacingScaleHarmonicAnalysis

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The literal Mellin integrand of an actual upper-resonant core. -/
def physicalMellinCore (s : upperMayerResonances) (u : ℂ) (a : ℝ) : ℂ :=
  (a : ℂ) ^ (u - 1) * mayerPeriodCore s.1 a

private theorem core_haar_square_bound (s : upperMayerResonances) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a > 0, ‖mayerPeriodCore s.1 a‖ ≤ C * min a⁻¹ (a ^ (1 - 2 * s.1.re))) :
    IntegrableOn (fun a : ℝ => ‖mayerPeriodCore s.1 a‖ ^ 2 / a) (Ioi 0) ∧
    (∫ a in Ioi (0 : ℝ), ‖mayerPeriodCore s.1 a‖ ^ 2 / a) ≤
      C ^ 2 * (1 / (2 - 4 * s.1.re) + 1 / 2) := by
  -- The endpoint powers give integrable square-energy majorants on either side of one.
  have hr : -1 < 1 - 4 * s.1.re := by linarith only [s.2.2.2.1]
  have hp0 : IntegrableOn (fun a : ℝ => a ^ (1 - 4 * s.1.re)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' hr).1
  have hp1 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) zero_lt_one
  have hm : Measurable (fun a : ℝ => ‖mayerPeriodCore s.1 a‖ ^ 2 / a) :=
    ((mayerPeriodCore_measurable s.2.1).norm.pow_const 2).div measurable_id
  have hs (a : ℝ) (ha : 0 < a) :
      ‖mayerPeriodCore s.1 a‖ ^ 2 / a ≤ C ^ 2 * a ^ (1 - 4 * s.1.re) := by
    have hf := (hb a ha).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
    have hp : (a ^ (1 - 2 * s.1.re)) ^ 2 / a = a ^ (1 - 4 * s.1.re) := by
      rw [← Real.rpow_natCast (a ^ (1 - 2 * s.1.re)) 2, ← Real.rpow_mul ha.le,
        div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add ha]
      congr 1
      norm_num
      ring
    calc
      _ ≤ (C * a ^ (1 - 2 * s.1.re)) ^ 2 / a :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hf 2) ha.le
      _ = _ := by rw [mul_pow, mul_div_assoc, hp]
  have hl (a : ℝ) (ha : 0 < a) :
      ‖mayerPeriodCore s.1 a‖ ^ 2 / a ≤ C ^ 2 * a ^ (-3 : ℝ) := by
    have hf := (hb a ha).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
    have hp : (a⁻¹) ^ 2 / a = a ^ (-3 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_natCast (a ^ (-1 : ℝ)) 2,
        ← Real.rpow_mul ha.le, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add ha]
      congr 1
      norm_num
    calc
      _ ≤ (C * a⁻¹) ^ 2 / a := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hf 2) ha.le
      _ = _ := by rw [mul_pow, mul_div_assoc, hp]
  have hi0 : IntegrableOn (fun a : ℝ => ‖mayerPeriodCore s.1 a‖ ^ 2 / a) (Ioc 0 1) := by
    apply (hp0.const_mul (C ^ 2)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ha.1.le)]
    exact hs a ha.1
  have hi1 : IntegrableOn (fun a : ℝ => ‖mayerPeriodCore s.1 a‖ ^ 2 / a) (Ioi 1) := by
    apply (hp1.const_mul (C ^ 2)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have ha0 : 0 < a := zero_lt_one.trans ha
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ha0.le)]
    exact hl a ha0
  have hi : IntegrableOn (fun a : ℝ => ‖mayerPeriodCore s.1 a‖ ^ 2 / a) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hi0.union hi1
  refine ⟨hi, ?_⟩
  have hv0 : (∫ a in Ioc (0 : ℝ) 1, a ^ (1 - 4 * s.1.re)) = 1 / (2 - 4 * s.1.re) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr), Real.one_rpow,
      Real.zero_rpow (by linarith only [s.2.2.2.1] : 1 - 4 * s.1.re + 1 ≠ 0)]
    ring
  have hv1 : (∫ a in Ioi (1 : ℝ), a ^ (-3 : ℝ)) = 1 / 2 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
    norm_num
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi0 hi1
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hsplit
  rw [hsplit]
  calc
    _ ≤ (∫ a in Ioc (0 : ℝ) 1, C ^ 2 * a ^ (1 - 4 * s.1.re)) +
        ∫ a in Ioi (1 : ℝ), C ^ 2 * a ^ (-3 : ℝ) := add_le_add
      (setIntegral_mono_on hi0 (hp0.const_mul _) measurableSet_Ioc fun a ha => hs a ha.1)
      (setIntegral_mono_on hi1 (hp1.const_mul _) measurableSet_Ioi fun a ha => hl a (zero_lt_one.trans ha))
    _ = _ := by rw [integral_const_mul, integral_const_mul, hv0, hv1]; ring

/-- Every actual upper-resonant core has finite Haar square energy on the entire positive axis. -/
theorem upperMayerCore_finite_whole_haar_energy (s : upperMayerResonances) :
    IntegrableOn (fun a : ℝ => ‖mayerPeriodCore s.1 a‖ ^ 2 / a) (Ioi 0) := by
  obtain ⟨C, N, hC, hb⟩ := upperMayerCore_two_endpoint_growth_bound
  have hy := s.2.1
  exact (core_haar_square_bound s (by positivity) (hb s)).1

#print axioms upperMayerCore_finite_whole_haar_energy

private theorem wholePhysicalCoreColumn_memLp (s : upperMayerResonances) :
    MemLp (physicalCoreColumnFun s) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : Measurable (physicalCoreColumnFun s) := by
    unfold physicalCoreColumnFun
    exact (mayerPeriodCore_measurable s.2.1).div
      (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  refine (upperMayerCore_finite_whole_haar_energy s).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  rw [physicalCoreColumnFun, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (le_of_lt ha)]

/-- An actual resonance core in whole-line Haar `L²`, represented by division by `√a`. -/
def wholePhysicalCoreColumn (s : upperMayerResonances) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (wholePhysicalCoreColumn_memLp s).toLp (physicalCoreColumnFun s)

private theorem wholePhysicalCoreColumn_norm_sq (s : upperMayerResonances) :
    ‖wholePhysicalCoreColumn s‖ ^ 2 = ∫ a in Ioi (0 : ℝ), ‖mayerPeriodCore s.1 a‖ ^ 2 / a := by
  have hn : ‖wholePhysicalCoreColumn s‖ ^ 2 =
      ∫ a in Ioi (0 : ℝ), ‖wholePhysicalCoreColumn s a‖ ^ 2 := by
    rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable _),
      lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num) (by norm_num)
        (Lp.aestronglyMeasurable _)]
    norm_num [← Real.sqrt_eq_rpow]
    rw [Real.sq_sqrt]
    exact integral_nonneg fun a => sq_nonneg _
  rw [hn]
  apply integral_congr_ae
  filter_upwards [(wholePhysicalCoreColumn_memLp s).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with a ha ha0
  rw [show wholePhysicalCoreColumn s a = physicalCoreColumnFun s a from ha,
    physicalCoreColumnFun, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (le_of_lt ha0)]

private theorem wholePhysicalCoreColumn_norm_le (s : upperMayerResonances) {C : ℝ}
    (hC : 0 ≤ C)
    (hb : ∀ a > 0, ‖mayerPeriodCore s.1 a‖ ≤ C * min a⁻¹ (a ^ (1 - 2 * s.1.re))) :
    ‖wholePhysicalCoreColumn s‖ ≤ 11 * C * (1 + s.1.im) := by
  have hsq := (core_haar_square_bound s hC hb).2
  rw [← wholePhysicalCoreColumn_norm_sq] at hsq
  -- Reflection controls the strip distance occurring in the small-endpoint integral.
  have href := (upperMayerResonance_reciprocal_bound (reflectUpperResonance s)).2
  have hre : (reflectUpperResonance s).1.re = 1 / 2 - s.1.re := by
    simp [reflectUpperResonance_coe, riemannMayerReflect]
  have him : (reflectUpperResonance s).1.im = s.1.im := by
    simp [reflectUpperResonance_coe, riemannMayerReflect]
  rw [hre, him, show 2 * (1 / 2 - s.1.re) = 1 - 2 * s.1.re by ring] at href
  have he : 1 / (2 - 4 * s.1.re) = (1 / (1 - 2 * s.1.re)) / 2 := by
    rw [show 2 - 4 * s.1.re = 2 * (1 - 2 * s.1.re) by ring]
    simp only [div_eq_mul_inv, mul_inv, one_mul, mul_comm]
  have hy := s.2.1
  have hpoly : 1 / (2 - 4 * s.1.re) + 1 / 2 ≤ (11 * (1 + s.1.im)) ^ 2 := by
    rw [he]
    nlinarith only [href, sq_nonneg s.1.im, hy.le]
  have hsq' : ‖wholePhysicalCoreColumn s‖ ^ 2 ≤ (11 * C * (1 + s.1.im)) ^ 2 := by
    calc
      _ ≤ C ^ 2 * (1 / (2 - 4 * s.1.re) + 1 / 2) := hsq
      _ ≤ C ^ 2 * (11 * (1 + s.1.im)) ^ 2 := mul_le_mul_of_nonneg_left hpoly (sq_nonneg C)
      _ = _ := by ring
  have hright : 0 ≤ 11 * C * (1 + s.1.im) := by positivity
  nlinarith only [hsq', norm_nonneg (wholePhysicalCoreColumn s), hright]

private theorem norm_gaussianWholePhysicalColumn_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    Summable (fun s : upperMayerResonances =>
      ‖((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) • wholePhysicalCoreColumn s‖) := by
  obtain ⟨C, N, hC, hb⟩ := upperMayerCore_two_endpoint_growth_bound
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_)
    ((upperMayer_gaussian_growth_summable hε (Real.pi / 2) (N + 1)).mul_left (11 * C * ‖x‖))
  have hy := s.2.1
  have hcoef := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x (upperMayerZero s)
  have hcol := wholePhysicalCoreColumn_norm_le s
    (show 0 ≤ C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2) by positivity) (hb s)
  rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ (Real.exp (-ε * s.1.im ^ 2) * ‖x‖) *
        (11 * (C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)) * (1 + s.1.im)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le) hcol
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [pow_succ, show Real.pi / 2 * s.1.im = Real.pi * s.1.im / 2 by ring]
      ring

/-- Gaussian regularization gives an absolutely convergent series in whole-line Haar `L²`. -/
theorem gaussianWholePhysicalColumn_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    Summable (fun s : upperMayerResonances =>
      ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) • wholePhysicalCoreColumn s) :=
  (norm_gaussianWholePhysicalColumn_summable hε x).of_norm

/-- The whole-line `L²` sum represents the same literal Gaussian core series. -/
theorem gaussianPhysicalCore_eq_wholeLp_tsum {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    (fun a => (∑' s : upperMayerResonances,
      ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) • wholePhysicalCoreColumn s) a)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun a => gaussianPhysicalCore ε x a / (Real.sqrt a : ℂ) := by
  letI := upperMayerResonances_countable
  have hcoe := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr
    (norm_gaussianWholePhysicalColumn_summable hε x))
  have hterm : ∀ᵐ a ∂volume.restrict (Ioi (0 : ℝ)), ∀ s : upperMayerResonances,
      (((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) • wholePhysicalCoreColumn s) a =
        (Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s) *
          (mayerPeriodCore s.1 a / (Real.sqrt a : ℂ)) := by
    apply ae_all_iff.mpr
    intro s
    filter_upwards [Lp.coeFn_smul ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s))
        (wholePhysicalCoreColumn s), (wholePhysicalCoreColumn_memLp s).coeFn_toLp] with a ha hb
    rw [ha]
    change ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) * wholePhysicalCoreColumn s a = _
    rw [show wholePhysicalCoreColumn s a = physicalCoreColumnFun s a from hb]
    rfl
  filter_upwards [hcoe, hterm] with a ha hb
  rw [ha, gaussianPhysicalCore, ← tsum_div_const]
  exact tsum_congr fun s => (hb s).trans (by ring)

/-- The actual Gaussian sum has finite Haar square energy on the whole positive axis. -/
theorem gaussianPhysicalCore_finite_whole_haar_energy {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    IntegrableOn (fun a : ℝ => ‖gaussianPhysicalCore ε x a‖ ^ 2 / a) (Ioi 0) := by
  have hm := (memLp_congr_ae (gaussianPhysicalCore_eq_wholeLp_tsum hε x)).mp (Lp.memLp _)
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt (le_of_lt ha)]

#print axioms gaussianWholePhysicalColumn_summable
#print axioms gaussianPhysicalCore_finite_whole_haar_energy

private theorem physicalMellinCore_aestronglyMeasurable (s : upperMayerResonances) (u : ℂ) :
  AEStronglyMeasurable (physicalMellinCore s u) (volume.restrict (Ioi 0)) := by
  apply AEStronglyMeasurable.mul _ (mayerPeriodCore_measurable s.2.1).aestronglyMeasurable
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
  intro a ha
  exact Or.inl (by simpa using ha)

private theorem physicalMellinCore_small_bound (s : upperMayerResonances) (u : ℂ)
  {C : ℝ} (hC : 0 ≤ C)
  (hb : ∀ a > 0, ‖mayerPeriodCore s.1 a‖ ≤ C * min a⁻¹ (a ^ (1 - 2 * s.1.re)))
  (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) 1) :
    ‖physicalMellinCore s u a‖ ≤ C * a ^ (u.re - 1) := by
  have hc := (hb a ha.1).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
  have hp := Real.rpow_le_one ha.1.le ha.2
    (by linarith only [s.2.2.2.1] : 0 ≤ 1 - 2 * s.1.re)
  have hc' : ‖mayerPeriodCore s.1 a‖ ≤ C :=
    hc.trans (by simpa using mul_le_mul_of_nonneg_left hp hC)
  rw [physicalMellinCore, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha.1,
    Complex.sub_re, Complex.one_re, mul_comm C]
  exact mul_le_mul_of_nonneg_left hc' (Real.rpow_nonneg ha.1.le _)

private theorem physicalMellinCore_large_bound (s : upperMayerResonances) (u : ℂ)
  {C : ℝ} (hC : 0 ≤ C)
  (hb : ∀ a > 0, ‖mayerPeriodCore s.1 a‖ ≤ C * min a⁻¹ (a ^ (1 - 2 * s.1.re)))
  (a : ℝ) (ha : 0 < a) :
    ‖physicalMellinCore s u a‖ ≤ C * a ^ (u.re - 2) := by
  have hc := (hb a ha).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
  rw [physicalMellinCore, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha,
    Complex.sub_re, Complex.one_re]
  calc
    _ ≤ a ^ (u.re - 1) * (C * a⁻¹) :=
      mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg ha.le _)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_neg_one, ← Real.rpow_add ha]
      congr 2
      ring

private theorem physicalMellinCore_bound (s : upperMayerResonances) {u : ℂ}
    (hu0 : 0 < u.re) (hu1 : u.re < 1) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a > 0, ‖mayerPeriodCore s.1 a‖ ≤ C * min a⁻¹ (a ^ (1 - 2 * s.1.re))) :
    IntegrableOn (physicalMellinCore s u) (Ioi 0) ∧
    (∫ a in Ioi (0 : ℝ), ‖physicalMellinCore s u a‖) ≤
      C * (1 / u.re + 1 / (1 - u.re)) := by
  have hp0 : IntegrableOn (fun a : ℝ => a ^ (u.re - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < u.re - 1)).1
  have hp1 : IntegrableOn (fun a : ℝ => a ^ (u.re - 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith only [hu1] : u.re - 2 < -1) zero_lt_one
  have hm := physicalMellinCore_aestronglyMeasurable s u
  have hs := physicalMellinCore_small_bound s u hC hb
  have hl := physicalMellinCore_large_bound s u hC hb
  have hi0 : IntegrableOn (physicalMellinCore s u) (Ioc 0 1) := by
    apply (hp0.const_mul C).mono' (hm.mono_set Ioc_subset_Ioi_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    exact hs a ha
  have hi1 : IntegrableOn (physicalMellinCore s u) (Ioi 1) := by
    apply (hp1.const_mul C).mono' (hm.mono_set (Ioi_subset_Ioi zero_le_one))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact hl a (zero_lt_one.trans ha)
  refine ⟨?_, ?_⟩
  · rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hi0.union hi1
  have hv0 : (∫ a in Ioc (0 : ℝ) 1, a ^ (u.re - 1)) = 1 / u.re := by
    rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : -1 < u.re - 1)), Real.one_rpow,
      Real.zero_rpow (by linarith only [hu0] : u.re - 1 + 1 ≠ 0)]
    simp only [sub_zero, sub_add_cancel]
  have hv1 : (∫ a in Ioi (1 : ℝ), a ^ (u.re - 2)) = 1 / (1 - u.re) := by
    rw [integral_Ioi_rpow_of_lt (by linarith only [hu1]) zero_lt_one, Real.one_rpow]
    rw [show u.re - 2 + 1 = -(1 - u.re) by ring]
    simp only [div_neg, neg_div, neg_neg]
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi0.norm hi1.norm
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hsplit
  rw [hsplit]
  calc
    _ ≤ (∫ a in Ioc (0 : ℝ) 1, C * a ^ (u.re - 1)) +
        ∫ a in Ioi (1 : ℝ), C * a ^ (u.re - 2) := add_le_add
      (setIntegral_mono_on hi0.norm (hp0.const_mul C) measurableSet_Ioc hs)
      (setIntegral_mono_on hi1.norm (hp1.const_mul C) measurableSet_Ioi
        fun a ha => hl a (zero_lt_one.trans ha))
    _ = _ := by rw [integral_const_mul, integral_const_mul, hv0, hv1]; ring

/-- Every actual upper-resonant core has an absolutely convergent Mellin transform
throughout the common strip `0 < Re u < 1`. -/
theorem upperMayerCore_mellinConvergent (s : upperMayerResonances) {u : ℂ}
    (hu0 : 0 < u.re) (hu1 : u.re < 1) : MellinConvergent (mayerPeriodCore s.1) u := by
  obtain ⟨C, N, hC, hb⟩ := upperMayerCore_two_endpoint_growth_bound
  have hy := s.2.1
  exact (physicalMellinCore_bound s hu0 hu1 (by positivity) (hb s)).1

private theorem gaussianPhysicalMellin_norm_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) {u : ℂ} (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    Summable (fun s : upperMayerResonances => ∫ a in Ioi (0 : ℝ),
      ‖((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) * physicalMellinCore s u a‖) := by
  obtain ⟨C, N, hC, hb⟩ := upperMayerCore_two_endpoint_growth_bound
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun s => ?_)
    ((upperMayer_gaussian_growth_summable hε (Real.pi / 2) N).mul_left
      (C * ‖x‖ * (1 / u.re + 1 / (1 - u.re))))
  have hy := s.2.1
  have hstrip : 0 ≤ 1 / u.re + 1 / (1 - u.re) := by positivity
  have hcoef := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x (upperMayerZero s)
  have hcol := (physicalMellinCore_bound s hu0 hu1
    (show 0 ≤ C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2) by positivity) (hb s)).2
  simp_rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    integral_const_mul]
  calc
    _ ≤ (Real.exp (-ε * s.1.im ^ 2) * ‖x‖) *
        (C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2) *
          (1 / u.re + 1 / (1 - u.re))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le) hcol
        (integral_nonneg fun _ => norm_nonneg _) (by positivity)
    _ = _ := by rw [show Real.pi / 2 * s.1.im = Real.pi * s.1.im / 2 by ring]; ring

/-- Mellin transformation commutes with the literal Gaussian core sum on its common strip. -/
theorem gaussianPhysicalCore_hasMellin {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) {u : ℂ} (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    HasMellin (gaussianPhysicalCore ε x) u
      (∑' s : upperMayerResonances,
        (Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s) * mellin (mayerPeriodCore s.1) u) := by
  letI := upperMayerResonances_countable
  let F : upperMayerResonances → ℝ → ℂ := fun s a =>
    ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) * physicalMellinCore s u a
  have hi (s : upperMayerResonances) : Integrable (F s) (volume.restrict (Ioi 0)) :=
    (upperMayerCore_mellinConvergent s hu0 hu1).const_mul _
  have hsum : Summable (fun s => ∫ a in Ioi (0 : ℝ), ‖F s a‖) :=
    gaussianPhysicalMellin_norm_summable hε x hu0 hu1
  -- Summability of the absolute integrals controls the literal infinite sum.
  have htotal : Integrable (fun a => ∑' s, F s a) (volume.restrict (Ioi 0)) := by
    refine ⟨(AEMeasurable.tsum (fun s => (hi s).aemeasurable)).aestronglyMeasurable, ?_⟩
    apply lt_of_le_of_lt (lintegral_mono (fun a => enorm_tsum_le_tsum_enorm))
    rw [lintegral_tsum (fun s => (hi s).1.enorm)]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun s => integral_nonneg fun a => norm_nonneg _) hsum]
    exact ENNReal.ofReal_lt_top
  have heq (a : ℝ) : (∑' s, F s a) = (a : ℂ) ^ (u - 1) * gaussianPhysicalCore ε x a := by
    rw [gaussianPhysicalCore, ← tsum_mul_left]
    exact tsum_congr fun s => by dsimp [F, physicalMellinCore]; ring
  have hswap := hasSum_integral_of_summable_integral_norm hi hsum
  constructor
  · simpa only [heq, MellinConvergent, IntegrableOn, smul_eq_mul] using htotal
  · have hterm (s : upperMayerResonances) : (∫ a in Ioi (0 : ℝ), F s a) =
        (Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s) * mellin (mayerPeriodCore s.1) u := by
      simp only [F, integral_const_mul]
      rfl
    simpa only [hterm, heq, mellin, smul_eq_mul] using hswap.tsum_eq.symm

#print axioms upperMayerCore_mellinConvergent
#print axioms gaussianPhysicalCore_hasMellin

private theorem upperMayerCore_locallyIntegrable (s : upperMayerResonances) :
    LocallyIntegrableOn (mayerPeriodCore s.1) (Ioi 0) := by
  have hc := upperMayerCore_mellinConvergent s (u := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
  have hi := hc.locallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed
    (g := fun a : ℝ => (a : ℂ) ^ (1 / 2 : ℂ))
    (continuousOn_of_forall_continuousAt fun a ha =>
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ha.ne'))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  rw [smul_smul, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
  norm_num

private theorem upperMayerCore_endpoint_isBigO (s : upperMayerResonances) :
    Asymptotics.IsBigO atTop (mayerPeriodCore s.1) (fun a : ℝ => a ^ (-1 : ℝ)) ∧
    Asymptotics.IsBigO (𝓝[>] 0) (mayerPeriodCore s.1)
      (fun a : ℝ => a ^ (-(2 * s.1.re - 1))) := by
  obtain ⟨C, N, hC, hb⟩ := upperMayerCore_two_endpoint_growth_bound
  let K := C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)
  have hy := s.2.1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  constructor
  · apply Asymptotics.IsBigO.of_bound K
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ha _), Real.rpow_neg_one]
    exact (hb s a ha).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hK)
  · apply Asymptotics.IsBigO.of_bound K
    filter_upwards [eventually_mem_nhdsWithin] with a ha
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ha _),
      show -(2 * s.1.re - 1) = 1 - 2 * s.1.re by ring]
    exact (hb s a ha).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK)

/-- The actual period core's Mellin transform is holomorphic on its enlarged resonant strip. -/
theorem upperMayerCore_mellin_differentiableAt (s : upperMayerResonances) {u : ℂ}
    (hu0 : 2 * s.1.re - 1 < u.re) (hu1 : u.re < 1) :
    DifferentiableAt ℂ (mellin (mayerPeriodCore s.1)) u :=
  mellin_differentiableAt_of_isBigO_rpow (upperMayerCore_locallyIntegrable s)
    (upperMayerCore_endpoint_isBigO s).1 hu1 (upperMayerCore_endpoint_isBigO s).2 hu0

#print axioms upperMayerCore_mellin_differentiableAt

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
