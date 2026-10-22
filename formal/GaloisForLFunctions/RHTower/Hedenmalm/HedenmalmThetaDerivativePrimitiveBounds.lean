import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaDerivativeOscillatoryPrimitive
import GaloisForLFunctions.RHTower.ThetaSourceTailRatioCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Uniform weighted bounds for theta derivative primitives

The actual nearest absolute tail bounds every complex oscillatory primitive
throughout the closed natural strip. Moderate derivative ratios and the
complete first-atom envelope prove that this majorant belongs to the
literal reciprocal-density L² carrier, independently of real frequency.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.HedenmalmThetaSource
open GaloisForLFunctions.HTGeometry HedenmalmQuantile HedenmalmPrimeTranslation

def thetaDerivativeAbsoluteIntegrand (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (|x| / 2) * ‖thetaSourceDerivativeFunction n x‖

theorem continuous_thetaDerivativeAbsoluteIntegrand (n : ℕ) :
    Continuous (thetaDerivativeAbsoluteIntegrand n) := by
  exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (|x| / 2))).mul
    (continuous_thetaSourceDerivativeFunction n).norm

theorem thetaDerivativeAbsoluteIntegrand_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ thetaDerivativeAbsoluteIntegrand n x := by
  exact mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem integrable_thetaDerivativeAbsoluteIntegrand (n : ℕ) :
    Integrable (thetaDerivativeAbsoluteIntegrand n) := by
  change Integrable (fun x : ℝ => Real.exp (|x| / 2) *
    ‖thetaSourceDerivativeFunction n x‖)
  simpa [thetaDerivativeAbsoluteIntegrand, thetaSourceDerivativeFunction,
    Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using
    integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource n (1 / 2)

theorem thetaDerivativeAbsoluteIntegrand_neg (n : ℕ) (x : ℝ) :
    thetaDerivativeAbsoluteIntegrand n (-x) = thetaDerivativeAbsoluteIntegrand n x := by
  simp only [thetaDerivativeAbsoluteIntegrand, thetaSourceDerivativeFunction,
    Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_iteratedDeriv_thetaCuspFullSource_neg]

/-- One actual majorant for every real frequency in the closed natural strip. -/
def thetaDerivativeUniformPrimitiveMajorant (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (|x| / 2) * ∫ y in Ioi |x|, thetaDerivativeAbsoluteIntegrand n y

theorem thetaDerivativeUniformPrimitiveMajorant_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ thetaDerivativeUniformPrimitiveMajorant n x := by
  exact mul_nonneg (Real.exp_pos _).le
    (integral_nonneg fun y => thetaDerivativeAbsoluteIntegrand_nonneg n y)

theorem continuous_thetaDerivativeUniformPrimitiveMajorant (n : ℕ) :
    Continuous (thetaDerivativeUniformPrimitiveMajorant n) := by
  have hleftC : Continuous (fun x : ℝ => ∫ y in Iic x,
      (thetaDerivativeAbsoluteIntegrand n y : ℂ)) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_setIntegral_Iic
        (Complex.continuous_ofReal.comp (continuous_thetaDerivativeAbsoluteIntegrand n))
        (integrable_thetaDerivativeAbsoluteIntegrand n).ofReal x).continuousAt
  have hleft : Continuous (fun x : ℝ => ∫ y in Iic x,
      thetaDerivativeAbsoluteIntegrand n y) := by
    simpa only [Function.comp_def, integral_complex_ofReal, Complex.ofReal_re] using
      Complex.continuous_re.comp hleftC
  have hsplit (x : ℝ) : (∫ y in Ioi x, thetaDerivativeAbsoluteIntegrand n y) =
      (∫ y, thetaDerivativeAbsoluteIntegrand n y) -
        ∫ y in Iic x, thetaDerivativeAbsoluteIntegrand n y := by
    have h := HedenmalmFredholmRange.setIntegral_Iic_add_Ioi
      (integrable_thetaDerivativeAbsoluteIntegrand n).ofReal x
    change (∫ y in Iic x, (thetaDerivativeAbsoluteIntegrand n y : ℂ)) +
      (∫ y in Ioi x, (thetaDerivativeAbsoluteIntegrand n y : ℂ)) =
        (∫ y, (thetaDerivativeAbsoluteIntegrand n y : ℂ)) at h
    simp only [integral_complex_ofReal] at h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re] at hr
    linarith
  have hright : Continuous (fun x : ℝ => ∫ y in Ioi x,
      thetaDerivativeAbsoluteIntegrand n y) := by
    have heq : (fun x : ℝ => ∫ y in Ioi x, thetaDerivativeAbsoluteIntegrand n y) =
        fun x => (∫ y, thetaDerivativeAbsoluteIntegrand n y) -
          ∫ y in Iic x, thetaDerivativeAbsoluteIntegrand n y := funext hsplit
    rw [heq]
    exact continuous_const.sub hleft
  exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (|x| / 2))).mul
    (hright.comp continuous_abs)

theorem norm_thetaDerivativeOscillatoryPrimitive_le_majorant (n : ℕ) {z : ℂ}
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) (x : ℝ) :
    ‖thetaDerivativeOscillatoryPrimitive n z x‖ ≤
      thetaDerivativeUniformPrimitiveMajorant n x := by
  have hphase (y : ℝ) : -z.im * y ≤ |y| / 2 := by
    have h := neg_abs_le (z.im * y)
    rw [abs_mul] at h
    nlinarith [abs_nonneg y]
  have houter : Real.exp (z.im * x) ≤ Real.exp (|x| / 2) := by
    apply Real.exp_le_exp.mpr
    have h := le_abs_self (z.im * x)
    rw [abs_mul] at h
    nlinarith [abs_nonneg x]
  have hpoint (y : ℝ) : ‖thetaDerivativeOscillatoryIntegrand n z y‖ ≤
      thetaDerivativeAbsoluteIntegrand n y := by
    rw [thetaDerivativeOscillatoryIntegrand, norm_mul, norm_sourceChar,
      thetaDerivativeAbsoluteIntegrand, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hphase y)) (norm_nonneg _)
  have hmono (s : Set ℝ) (hs : MeasurableSet s) :
      (∫ y in s, ‖thetaDerivativeOscillatoryIntegrand n z y‖) ≤
        ∫ y in s, thetaDerivativeAbsoluteIntegrand n y :=
    setIntegral_mono_on (integrable_thetaDerivativeOscillatoryIntegrand n z).norm.integrableOn
      (integrable_thetaDerivativeAbsoluteIntegrand n).integrableOn hs (fun y _ => hpoint y)
  rcases le_total 0 x with hx | hx
  · rw [thetaDerivativeOscillatoryPrimitive_tail n hzero x, norm_mul, norm_neg,
      norm_exp_neg_I_mul]
    calc
      Real.exp (z.im * x) * ‖∫ y in Ioi x, thetaDerivativeOscillatoryIntegrand n z y‖ ≤
          Real.exp (z.im * x) * ∫ y in Ioi x, ‖thetaDerivativeOscillatoryIntegrand n z y‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_pos _).le
      _ ≤ Real.exp (|x| / 2) * ∫ y in Ioi x, thetaDerivativeAbsoluteIntegrand n y :=
        mul_le_mul houter (hmono _ measurableSet_Ioi)
          (integral_nonneg fun y => norm_nonneg _) (Real.exp_pos _).le
      _ = thetaDerivativeUniformPrimitiveMajorant n x := by
        simp only [thetaDerivativeUniformPrimitiveMajorant, abs_of_nonneg hx]
  · rw [thetaDerivativeOscillatoryPrimitive, norm_mul, norm_exp_neg_I_mul]
    calc
      Real.exp (z.im * x) * ‖∫ y in Iic x, thetaDerivativeOscillatoryIntegrand n z y‖ ≤
          Real.exp (z.im * x) * ∫ y in Iic x, ‖thetaDerivativeOscillatoryIntegrand n z y‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_pos _).le
      _ ≤ Real.exp (|x| / 2) * ∫ y in Iic x, thetaDerivativeAbsoluteIntegrand n y :=
        mul_le_mul houter (hmono _ measurableSet_Iic)
          (integral_nonneg fun y => norm_nonneg _) (Real.exp_pos _).le
      _ = thetaDerivativeUniformPrimitiveMajorant n x := by
        have hneg := integral_comp_neg_Iic x (thetaDerivativeAbsoluteIntegrand n)
        simp only [thetaDerivativeAbsoluteIntegrand_neg] at hneg
        rw [hneg, thetaDerivativeUniformPrimitiveMajorant, abs_of_nonpos hx]

theorem exists_thetaDerivative_source_exponential_bound (n : ℕ) :
    ∃ C K X : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ 1 ≤ X ∧ ∀ x, X ≤ x →
      ‖thetaSourceDerivativeFunction n x‖ ≤
        C * Real.exp (K * x) * thetaCuspFullSource x := by
  obtain ⟨C, d, hmod⟩ := thetaSourceRatio_moderate n
  obtain ⟨X, hX⟩ := eventually_atTop.mp hmod
  refine ⟨|C| * Real.pi ^ d, 2 * (d : ℝ), max 1 X,
    mul_nonneg (abs_nonneg _) (pow_nonneg Real.pi_pos.le _), by positivity, le_max_left _ _, ?_⟩
  intro x hx
  have hbound := (hX x (le_trans (le_max_right _ _) hx)).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (thetaTailScale_pos x).le d))
  have hk := thetaCuspFullSource_pos x
  have hnorm : ‖thetaSourceDerivativeFunction n x‖ ≤
      |C| * thetaCuspSingleAtomReflectionScale 1 x ^ d * thetaCuspFullSource x := by
    rw [thetaSourceDerivativeFunction, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ hk).mp
    simpa only [thetaSourceRatio, abs_div, abs_of_pos hk] using hbound
  have hscale : thetaCuspSingleAtomReflectionScale 1 x ^ d =
      Real.pi ^ d * Real.exp ((2 * (d : ℝ)) * x) := by
    rw [thetaTailScale_eq, mul_pow, ← pow_mul, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [hscale] at hnorm
  simpa only [mul_assoc] using hnorm

theorem exists_thetaDerivativeUniformPrimitiveMajorant_tail_bound (n : ℕ) :
    ∃ C K X : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ 1 ≤ X ∧ ∀ x, X ≤ x →
      thetaDerivativeUniformPrimitiveMajorant n x ≤
        C * Real.exp (K * x) * thetaEnvelope x := by
  obtain ⟨C, K, X, hC, hK, hX, hbound⟩ :=
    exists_thetaDerivative_source_exponential_bound n
  refine ⟨C * thetaEnvelopeUpper, K + 1, max X (K + 2),
    mul_nonneg hC thetaEnvelopeUpper_pos.le, by linarith, hX.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ x := hX.trans hxX
  have hxK : K + 2 ≤ x := (le_max_right _ _).trans hx
  let a : ℝ := Real.pi * Real.exp (2 * x)
  let r : ℝ := a - K - 1 / 2
  let c : ℝ := C * thetaEnvelopeUpper * Real.exp ((K + 1 / 2) * x) * thetaEnvelope x
  have ha : K + 2 ≤ a := by
    have he := Real.add_one_le_exp (2 * x)
    have hp : 1 ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
    have hm := mul_nonneg (Real.exp_pos (2 * x)).le (sub_nonneg.mpr hp)
    dsimp [a]
    nlinarith
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC thetaEnvelopeUpper_pos.le)
      (Real.exp_pos _).le) (thetaEnvelope_pos x).le
  have hdom : IntegrableOn (fun y : ℝ => c * Real.exp (-r * (y - x))) (Ioi x) :=
    (integrableOn_exp_neg_shift hrpos).const_mul c
  have hpoint (y : ℝ) (hy : y ∈ Ioi x) :
      thetaDerivativeAbsoluteIntegrand n y ≤ c * Real.exp (-r * (y - x)) := by
    have hxy : x ≤ y := hy.le
    have hy0 : 0 ≤ y := (by linarith : 0 ≤ x).trans hxy
    have hg := hbound y (hxX.trans hxy)
    have hk := thetaCuspFullSource_le_shift hx1 hxy
    have hcombined : ‖thetaSourceDerivativeFunction n y‖ ≤
        C * Real.exp (K * y) *
          (thetaEnvelopeUpper * thetaEnvelope x * Real.exp (-a * (y - x))) := by
      apply hg.trans
      exact mul_le_mul_of_nonneg_left hk (mul_nonneg hC (Real.exp_pos _).le)
    have hexp : Real.exp (y / 2) * Real.exp (K * y) * Real.exp (-a * (y - x)) =
        Real.exp ((K + 1 / 2) * x) * Real.exp (-r * (y - x)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [r]
      ring
    calc
      thetaDerivativeAbsoluteIntegrand n y =
          Real.exp (y / 2) * ‖thetaSourceDerivativeFunction n y‖ := by
        rw [thetaDerivativeAbsoluteIntegrand, abs_of_nonneg hy0]
      _ ≤ Real.exp (y / 2) * (C * Real.exp (K * y) *
          (thetaEnvelopeUpper * thetaEnvelope x * Real.exp (-a * (y - x)))) :=
        mul_le_mul_of_nonneg_left hcombined (Real.exp_pos _).le
      _ = (C * thetaEnvelopeUpper * thetaEnvelope x) *
          (Real.exp (y / 2) * Real.exp (K * y) * Real.exp (-a * (y - x))) := by ring
      _ = c * Real.exp (-r * (y - x)) := by rw [hexp]; dsimp [c]; ring
  have htail : (∫ y in Ioi x, thetaDerivativeAbsoluteIntegrand n y) ≤ c := by
    calc
      (∫ y in Ioi x, thetaDerivativeAbsoluteIntegrand n y) ≤
          ∫ y in Ioi x, c * Real.exp (-r * (y - x)) :=
        setIntegral_mono_on (integrable_thetaDerivativeAbsoluteIntegrand n).integrableOn
          hdom measurableSet_Ioi hpoint
      _ = c / r := by rw [integral_const_mul, integral_Ioi_exp_neg_shift hrpos]; ring
      _ ≤ c := div_le_self hc hr
  calc
    thetaDerivativeUniformPrimitiveMajorant n x =
        Real.exp (x / 2) * ∫ y in Ioi x, thetaDerivativeAbsoluteIntegrand n y := by
      rw [thetaDerivativeUniformPrimitiveMajorant, abs_of_nonneg (by linarith : 0 ≤ x)]
    _ ≤ Real.exp (x / 2) * c := mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
    _ = (C * thetaEnvelopeUpper) * Real.exp ((K + 1) * x) * thetaEnvelope x := by
      dsimp [c]
      rw [show Real.exp (x / 2) *
          (C * thetaEnvelopeUpper * Real.exp ((K + 1 / 2) * x) * thetaEnvelope x) =
          (C * thetaEnvelopeUpper * thetaEnvelope x) *
            (Real.exp (x / 2) * Real.exp ((K + 1 / 2) * x)) by ring,
        ← Real.exp_add, show x / 2 + (K + 1 / 2) * x = (K + 1) * x by ring]
      ring

theorem integrable_exp_mul_thetaEnvelope_abs {K : ℝ} (hK : 0 ≤ K) :
    Integrable (fun x : ℝ => Real.exp (K * |x|) * thetaEnvelope |x|) := by
  let f : ℝ → ℝ := fun x => Real.exp ((K + 9 / 2) * x) *
    Real.exp (-(Real.pi * Real.exp (2 * x)))
  have hf : Integrable f :=
    integrable_exp_mul_exp_neg_mul_exp_two_mul (by linarith) Real.pi_pos
  have hn : Integrable (fun x : ℝ => f (-x)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hf
  have heq (x : ℝ) : Real.exp (K * |x|) * thetaEnvelope |x| = f |x| := by
    dsimp [f, thetaEnvelope]
    rw [← mul_assoc, ← Real.exp_add]
    rw [show K * |x| + 9 * |x| / 2 = (K + 9 / 2) * |x| by ring]
    simp only [neg_mul]
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (K * |x|) * thetaEnvelope |x|) volume := by
    exact (by dsimp [thetaEnvelope]; fun_prop :
      Continuous (fun x : ℝ => Real.exp (K * |x|) * thetaEnvelope |x|)).aestronglyMeasurable
  apply Integrable.mono' (hf.add hn) hmeas
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (thetaEnvelope_pos _)), heq]
  change f |x| ≤ f x + f (-x)
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have hn0 : 0 ≤ f (-x) := by dsimp [f]; positivity
    linarith
  · rw [abs_of_nonpos hx]
    have hf0 : 0 ≤ f x := by dsimp [f]; positivity
    linarith

/-- The actual majorant has finite reciprocal-density energy, uniformly in frequency. -/
theorem integrable_thetaDerivativeUniformPrimitiveMajorant_energy (n : ℕ) :
    Integrable (thetaPowerWeightedEnergy 1 (thetaDerivativeUniformPrimitiveMajorant n)) := by
  obtain ⟨C, K, X, hC, hK, hX, hbound⟩ :=
    exists_thetaDerivativeUniformPrimitiveMajorant_tail_bound n
  let G : ℝ → ℝ := fun x => (C ^ 2 / thetaEnvelopeLower) *
    (Real.exp ((2 * K) * |x|) * thetaEnvelope |x|)
  have hG : Integrable G :=
    (integrable_exp_mul_thetaEnvelope_abs (by linarith : 0 ≤ 2 * K)).const_mul _
  have hcont : Continuous (thetaPowerWeightedEnergy 1 (thetaDerivativeUniformPrimitiveMajorant n)) :=
    continuous_thetaPowerWeightedEnergy 1 (continuous_thetaDerivativeUniformPrimitiveMajorant n)
  have htail (x : ℝ) (hx : X ≤ |x|) :
      thetaPowerWeightedEnergy 1 (thetaDerivativeUniformPrimitiveMajorant n) x ≤ G x := by
    have hB := hbound |x| hx
    have hBabs : thetaDerivativeUniformPrimitiveMajorant n |x| =
        thetaDerivativeUniformPrimitiveMajorant n x := by
      simp only [thetaDerivativeUniformPrimitiveMajorant, abs_abs]
    rw [hBabs] at hB
    have hkabs : thetaCuspFullSource |x| = thetaCuspFullSource x := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, thetaCuspFullSource_neg]
    have hlow : thetaEnvelopeLower * thetaEnvelope |x| ≤ thetaCuspFullSource x := by
      rw [← hkabs]
      exact thetaCuspFullSource_ge_envelope (by linarith)
    have hnum : thetaDerivativeUniformPrimitiveMajorant n x ^ 2 ≤
        C ^ 2 * Real.exp (K * |x|) ^ 2 * thetaEnvelope |x| ^ 2 := by
      nlinarith [thetaDerivativeUniformPrimitiveMajorant_nonneg n x]
    have hnn : 0 ≤ C ^ 2 * Real.exp (K * |x|) ^ 2 * thetaEnvelope |x| ^ 2 := by positivity
    rw [thetaPowerWeightedEnergy, show -(1 : ℝ) = -1 by rfl, Real.rpow_neg_one,
      ← div_eq_mul_inv]
    calc
      thetaDerivativeUniformPrimitiveMajorant n x ^ 2 / thetaCuspFullSource x ≤
          (C ^ 2 * Real.exp (K * |x|) ^ 2 * thetaEnvelope |x| ^ 2) /
            (thetaEnvelopeLower * thetaEnvelope |x|) :=
        div_le_div₀ hnn hnum (mul_pos thetaEnvelopeLower_pos (thetaEnvelope_pos _)) hlow
      _ = G x := by
        dsimp [G]
        rw [← Real.exp_nat_mul]
        push_cast
        rw [show (2 : ℝ) * (K * |x|) = (2 * K) * |x| by ring]
        field_simp [thetaEnvelopeLower_pos.ne', (thetaEnvelope_pos |x|).ne']
  have hleft : IntegrableOn
      (thetaPowerWeightedEnergy 1 (thetaDerivativeUniformPrimitiveMajorant n)) (Iic (-X)) := by
    refine Integrable.mono' hG.integrableOn
      (hcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (thetaPowerWeightedEnergy_nonneg _ _ _)]
    apply htail
    rw [abs_of_nonpos (by linarith [show x ≤ -X from hx])]
    linarith [show x ≤ -X from hx]
  have hmid : IntegrableOn
      (thetaPowerWeightedEnergy 1 (thetaDerivativeUniformPrimitiveMajorant n)) (Ioc (-X) X) :=
    (hcont.integrableOn_Icc (a := -X) (b := X)).mono_set Ioc_subset_Icc_self
  have hright : IntegrableOn
      (thetaPowerWeightedEnergy 1 (thetaDerivativeUniformPrimitiveMajorant n)) (Ioi X) := by
    refine Integrable.mono' hG.integrableOn
      (hcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (thetaPowerWeightedEnergy_nonneg _ _ _)]
    apply htail
    rw [abs_of_nonneg (by linarith [show X < x from hx])]
    exact (show X < x from hx).le
  have hunion : Iic (-X) ∪ (Ioc (-X) X ∪ Ioi X) = univ := by
    rw [Ioc_union_Ioi_eq_Ioi (by linarith : -X ≤ X), Iic_union_Ioi]
  rw [← integrableOn_univ, ← hunion]
  exact hleft.union (hmid.union hright)

theorem thetaDerivativeUniformPrimitiveMajorant_memLp (n : ℕ) :
    MemLp (thetaDerivativeUniformPrimitiveMajorant n) 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight thetaSource))) := by
  have hm := (memLp_thetaPowerWeightedMeasure_iff 1
    (continuous_thetaDerivativeUniformPrimitiveMajorant n)).mpr
      (integrable_thetaDerivativeUniformPrimitiveMajorant_energy n)
  convert! hm using 1
  unfold thetaPowerWeightedMeasure
  congr 1
  funext x
  simp only [realDensity, sourceWeight, thetaSource_k,
    Real.rpow_neg_one]

theorem thetaDerivativeOscillatoryPrimitive_memLp (n : ℕ) {z : ℂ}
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) :
    MemLp (thetaDerivativeOscillatoryPrimitive n z) 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight thetaSource))) := by
  refine (thetaDerivativeUniformPrimitiveMajorant_memLp n).mono'
    (continuous_thetaDerivativeOscillatoryPrimitive n z).aestronglyMeasurable ?_
  filter_upwards with x
  exact norm_thetaDerivativeOscillatoryPrimitive_le_majorant n hstrip hzero x

/-- The norm of the actual majorant, not an assumed remainder bound. -/
def thetaDerivativePrimitiveUniformNormBound (n : ℕ) : ℝ :=
  ‖(thetaDerivativeUniformPrimitiveMajorant_memLp n).toLp
    (thetaDerivativeUniformPrimitiveMajorant n)‖

theorem thetaDerivativePrimitiveUniformNormBound_nonneg (n : ℕ) :
    0 ≤ thetaDerivativePrimitiveUniformNormBound n := norm_nonneg _

theorem norm_thetaDerivativeOscillatoryPrimitive_toLp_le (n : ℕ) {z : ℂ}
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) :
    ‖(thetaDerivativeOscillatoryPrimitive_memLp n hstrip hzero).toLp
      (thetaDerivativeOscillatoryPrimitive n z)‖ ≤ thetaDerivativePrimitiveUniformNormBound n := by
  rw [thetaDerivativePrimitiveUniformNormBound, Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono (thetaDerivativeUniformPrimitiveMajorant_memLp n).2.ne
    (eLpNorm_mono_ae_real (ae_of_all _ fun x =>
      norm_thetaDerivativeOscillatoryPrimitive_le_majorant n hstrip hzero x))

end RHTower.HedenmalmThetaSource
