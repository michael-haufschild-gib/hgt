import GaloisForLFunctions.RHTower.ZetaBinomialHalfKaramataLaw
import GaloisForLFunctions.HTGeometry.WeightedPortmanteau

/-!
# Exponential un-tilting for the positive zeta half

This module turns the compact Gamma-half scaling law into an unconditional sharp
harmonic-window asymptotic.  The continuous reciprocal weight is handled on the
compactified space; null-frontier convergence then recovers the cutoff.

This is a real-axis Tauberian consequence, not analytic continuation.  The
harmonic-window asymptotic alone does not determine the ordinary coefficient
summatory law: that stronger conclusion needs Kato's complex-boundary input.
-/

open ArithmeticFunction Complex Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ArithmeticFunction.zeta ComplexOrder ENNReal NNReal

noncomputable section

namespace RHTower

def zetaBinomialHalfReciprocalCompactLogWeight (x : ℝ) :
    C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun y => -Real.log (max (y : ℝ) (Real.exp (-x) / 2)), by
    apply Continuous.neg
    apply Continuous.log (continuous_subtype_val.max continuous_const)
    intro y
    exact ne_of_gt (lt_of_lt_of_le (by positivity : 0 < Real.exp (-x) / 2)
      (le_max_right _ _))⟩

theorem exp_zetaBinomialHalfReciprocalCompactLogWeight_of_mem_expTailSet
    {x : ℝ} {y : Icc (0 : ℝ) 1}
    (hy : y ∈ GaloisForLFunctions.HTGeometry.expTailSet x) :
    Real.exp (zetaBinomialHalfReciprocalCompactLogWeight x y) = ((y : ℝ))⁻¹ := by
  have hxy : Real.exp (-x) ≤ (y : ℝ) := hy
  have hmax : max (y : ℝ) (Real.exp (-x) / 2) = (y : ℝ) := by
    rw [max_eq_left]
    have hexp : 0 < Real.exp (-x) := Real.exp_pos _
    linarith
  have hypos : 0 < (y : ℝ) := (Real.exp_pos (-x)).trans_le hxy
  rw [zetaBinomialHalfReciprocalCompactLogWeight, ContinuousMap.coe_mk, hmax,
    Real.exp_neg, Real.exp_log hypos]

theorem tendsto_setIntegral_reciprocal_zetaBinomialHalfKaramataCompactLaw (x : ℝ) :
    Tendsto
      (fun t : ℝ => ∫ y in GaloisForLFunctions.HTGeometry.expTailSet x,
        Real.exp (zetaBinomialHalfReciprocalCompactLogWeight x y)
          ∂(zetaBinomialHalfKaramataCompactLaw t : Measure (Icc (0 : ℝ) 1)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y in GaloisForLFunctions.HTGeometry.expTailSet x,
        Real.exp (zetaBinomialHalfReciprocalCompactLogWeight x y)
          ∂(gammaHalfCompactLaw : Measure (Icc (0 : ℝ) 1)))) := by
  apply GaloisForLFunctions.HTGeometry.tendsto_setIntegral_exp_of_null_frontier
    tendsto_zetaBinomialHalfKaramataCompactLaw
    (zetaBinomialHalfReciprocalCompactLogWeight x)
    (GaloisForLFunctions.HTGeometry.measurableSet_expTailSet x)
  simpa [gammaHalfCompactLaw] using expPush_gammaMeasure_half_frontier_expTailSet x

theorem setIntegral_reciprocal_zetaBinomialHalfKaramataCompactLaw_eq
    (t x : ℝ) :
    (∫ y in GaloisForLFunctions.HTGeometry.expTailSet x,
        Real.exp (zetaBinomialHalfReciprocalCompactLogWeight x y)
          ∂(zetaBinomialHalfKaramataCompactLaw t : Measure (Icc (0 : ℝ) 1))) =
      ∫ z in Iic x, Real.exp z ∂(zetaBinomialHalfKaramataLaw t) := by
  rw [zetaBinomialHalfKaramataCompactLaw,
    GaloisForLFunctions.HTGeometry.expPushProb_toMeasure,
    GaloisForLFunctions.HTGeometry.expPush]
  rw [setIntegral_map
    (μ := zetaBinomialHalfKaramataLaw t)
    (g := GaloisForLFunctions.HTGeometry.expProj)
    (f := fun y => Real.exp (zetaBinomialHalfReciprocalCompactLogWeight x y))
    (GaloisForLFunctions.HTGeometry.measurableSet_expTailSet x)
    ((Real.continuous_exp.comp
      (zetaBinomialHalfReciprocalCompactLogWeight x).continuous).aestronglyMeasurable)
    GaloisForLFunctions.HTGeometry.measurable_expProj.aemeasurable]
  rw [setIntegral_congr_set
    (GaloisForLFunctions.HTGeometry.preimage_expTailSet_ae
      (zetaBinomialHalfKaramataLaw t)
      (zetaBinomialHalfKaramataLaw_Iio_zero t) x)]
  apply setIntegral_congr_ae measurableSet_Iic
  filter_upwards [GaloisForLFunctions.HTGeometry.ae_nonneg_of_Iio_zero
    (zetaBinomialHalfKaramataLaw_Iio_zero t)] with z hz hzle
  rw [exp_zetaBinomialHalfReciprocalCompactLogWeight_of_mem_expTailSet]
  · rw [GaloisForLFunctions.HTGeometry.coe_expProj_of_nonneg hz]
    rw [← Real.exp_neg]
    ring_nf
  · change Real.exp (-x) ≤
      (GaloisForLFunctions.HTGeometry.expProj z : ℝ)
    rw [GaloisForLFunctions.HTGeometry.coe_expProj_of_nonneg hz,
      Real.exp_le_exp]
    change z ≤ x at hzle
    linarith

theorem tendsto_setIntegral_exp_zetaBinomialHalfKaramataLaw (x : ℝ) :
    Tendsto
      (fun t : ℝ => ∫ z in Iic x, Real.exp z
        ∂(zetaBinomialHalfKaramataLaw t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z in Iic x, Real.exp z ∂(gammaMeasure (1 / 2) 1))) := by
  have h := tendsto_setIntegral_reciprocal_zetaBinomialHalfKaramataCompactLaw x
  have hzero := setIntegral_reciprocal_zetaBinomialHalfKaramataCompactLaw_eq 0 x
  simp only [zetaBinomialHalfKaramataCompactLaw,
    zetaBinomialHalfKaramataLaw, lt_self_iff_false, ↓reduceIte] at hzero
  convert h using 1
  · funext t
    exact (setIntegral_reciprocal_zetaBinomialHalfKaramataCompactLaw_eq t x).symm
  · exact congrArg nhds hzero.symm

/-- Harmonic zeta-half mass below a scaled logarithmic cutoff. -/
def zetaBinomialHalfHarmonicWindow (t x : ℝ) : ℝ :=
  ∑' n : ℕ, if zetaBinomialHalfKaramataLogCoordinate t n ≤ x then
    zetaBinomialHalfReal n * (n : ℝ) ^ (-1 : ℝ) else 0

theorem integrableOn_exp_zetaBinomialHalfKaramataLawRaw
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    IntegrableOn Real.exp (Iic x) (zetaBinomialHalfKaramataLawRaw t) := by
  letI := isProbabilityMeasure_zetaBinomialHalfKaramataLawRaw ht
  refine Integrable.mono' (integrable_const (Real.exp x))
    Real.continuous_exp.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr hz

/-- Exact cancellation of the exponential tilt on a sharp logarithmic window. -/
theorem setIntegral_exp_zetaBinomialHalfKaramataLawRaw_eq_harmonicWindow
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ z in Iic x, Real.exp z ∂(zetaBinomialHalfKaramataLawRaw t)) =
      zetaBinomialHalfHarmonicWindow t x / zetaBinomialHalfDirichletMass t := by
  rw [← integral_indicator measurableSet_Iic]
  rw [zetaBinomialHalfKaramataLawRaw,
    GaloisForLFunctions.HTGeometry.integral_weightedPointLaw _ _
      ((integrableOn_exp_zetaBinomialHalfKaramataLawRaw ht x).integrable_indicator
        measurableSet_Iic)]
  rw [zetaBinomialHalfHarmonicWindow, ← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [ENNReal.toReal_ofReal (zetaBinomialHalfKaramataWeight_nonneg ht n)]
  rw [zetaBinomialHalfKaramataWeight, div_mul_eq_mul_div]
  congr 1
  by_cases hnx : zetaBinomialHalfKaramataLogCoordinate t n ≤ x
  · have hmem : zetaBinomialHalfKaramataLogCoordinate t n ∈ Iic x := hnx
    rw [if_pos hnx, Set.indicator_of_mem hmem]
    by_cases hn : n = 0
    · subst n
      simp
    · rw [zetaBinomialHalfKaramataLogCoordinate]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hexp : Real.exp (t * Real.log n) = (n : ℝ) ^ t := by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        ring
      rw [hexp, mul_assoc, ← Real.rpow_add hnpos]
      congr 2
      ring
  · have hmem : zetaBinomialHalfKaramataLogCoordinate t n ∉ Iic x := hnx
    rw [if_neg hnx, Set.indicator_of_notMem hmem]
    simp

theorem tendsto_zetaBinomialHalfHarmonicWindow_div_mass (x : ℝ) :
    Tendsto
      (fun t : ℝ => zetaBinomialHalfHarmonicWindow t x /
        zetaBinomialHalfDirichletMass t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z in Iic x, Real.exp z ∂(gammaMeasure (1 / 2) 1))) := by
  refine (tendsto_setIntegral_exp_zetaBinomialHalfKaramataLaw x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [zetaBinomialHalfKaramataLaw, if_pos ht,
    setIntegral_exp_zetaBinomialHalfKaramataLawRaw_eq_harmonicWindow ht]

/-- **Unconditional harmonic Karamata window law for the positive zeta half.** -/
theorem tendsto_sqrt_mul_zetaBinomialHalfHarmonicWindow (x : ℝ) :
    Tendsto
      (fun t : ℝ => Real.sqrt t * zetaBinomialHalfHarmonicWindow t x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z in Iic x, Real.exp z ∂(gammaMeasure (1 / 2) 1))) := by
  have hprod := tendsto_sqrt_mul_zetaBinomialHalfDirichletMass.mul
    (tendsto_zetaBinomialHalfHarmonicWindow_div_mass x)
  have hprod' : Tendsto
      (fun t : ℝ =>
        (Real.sqrt t * zetaBinomialHalfDirichletMass t) *
          (zetaBinomialHalfHarmonicWindow t x /
            zetaBinomialHalfDirichletMass t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z in Iic x, Real.exp z ∂(gammaMeasure (1 / 2) 1))) := by
    simpa only [one_mul] using hprod
  refine hprod'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hM : zetaBinomialHalfDirichletMass t ≠ 0 :=
    (zetaBinomialHalfDirichletMass_pos ht).ne'
  field_simp

theorem setIntegral_exp_gammaMeasure_half {x : ℝ} (hx : 0 ≤ x) :
    (∫ z in Iic x, Real.exp z ∂(gammaMeasure (1 / 2) 1)) =
      2 * Real.sqrt x / Real.sqrt Real.pi := by
  unfold gammaMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (show Measurable (gammaPDF (1 / 2) 1) by
      exact (measurable_gammaPDFReal (1 / 2) 1).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun z => by
      rw [gammaPDF]
      exact ENNReal.ofReal_lt_top)) Real.exp measurableSet_Iic]
  rw [show (fun z : ℝ =>
      (gammaPDF (1 / 2) 1 z).toReal • Real.exp z) =
      (Ici 0).indicator (fun z : ℝ =>
        (Real.sqrt Real.pi)⁻¹ * z ^ (-(1 / 2 : ℝ))) by
    funext z
    rw [gammaPDF_eq]
    by_cases hz : 0 ≤ z
    · have hzmem : z ∈ Ici (0 : ℝ) := hz
      rw [if_pos hz, indicator_of_mem hzmem]
      rw [ENNReal.toReal_ofReal]
      · rw [Real.Gamma_one_half_eq]
        norm_num
        have hexpcancel : Real.exp (-z) * Real.exp z = 1 := by
          rw [← Real.exp_add]
          simp
        rw [mul_assoc, hexpcancel, mul_one]
      · positivity
    · have hzmem : z ∉ Ici (0 : ℝ) := hz
      rw [if_neg hz, indicator_of_notMem hzmem]
      simp]
  rw [setIntegral_indicator measurableSet_Ici]
  have hinter : Iic x ∩ Ici (0 : ℝ) = Icc 0 x := by
    ext z
    simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_Icc]
    tauto
  rw [hinter, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx]
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ)))]
  rw [Real.zero_rpow (by norm_num : (-(1 / 2 : ℝ)) + 1 ≠ 0)]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  field_simp

theorem tendsto_sqrt_mul_zetaBinomialHalfHarmonicWindow_explicit
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto
      (fun t : ℝ => Real.sqrt t * zetaBinomialHalfHarmonicWindow t x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (2 * Real.sqrt x / Real.sqrt Real.pi)) := by
  have h := tendsto_sqrt_mul_zetaBinomialHalfHarmonicWindow x
  rw [setIntegral_exp_gammaMeasure_half hx] at h
  exact h

end RHTower
