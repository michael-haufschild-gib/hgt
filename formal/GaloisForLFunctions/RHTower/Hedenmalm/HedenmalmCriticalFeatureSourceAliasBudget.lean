import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSharpLatticeCharge

/-!
# Source-facing alias budget for the full HCF height lattice

The sharp Poisson theorem gives more than a pointwise domination constant.  After periodizing the
real HCF profile, its exact zero mode is `2π` and its complete nonzero-mode ripple is at most
`37 / 200`.  Pairing against any integrable signed source therefore separates the zero mode with an
explicit `L¹` error.  The final theorem instantiates this for the positive-displacement continued
pole--Gamma source on a compact height window.

This identifies the quantitative debt honestly: nonzero height aliases are cheap, while the zero
mode and the signed `L¹` mass of the continued source still require arithmetic cancellation.
-/

open Complex MeasureTheory Set
open RHTower.RealBoundaryDivisor
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Full integer periodization of the real HCF boundary profile. -/
def criticalFeatureRealBoundaryPeriodization (x : ℝ) : ℝ :=
  ∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n)

theorem criticalFeatureRealBoundaryPeriodization_nonnegative (x : ℝ) :
    0 ≤ criticalFeatureRealBoundaryPeriodization x := by
  rw [criticalFeatureRealBoundaryPeriodization]
  exact tsum_nonneg fun n => by
    unfold criticalFeatureRealBoundaryWeight
    positivity

theorem criticalFeatureRealBoundaryPeriodization_le_nine (x : ℝ) :
    criticalFeatureRealBoundaryPeriodization x ≤ 9 := by
  rw [criticalFeatureRealBoundaryPeriodization]
  exact (tsum_criticalFeatureRealBoundaryWeight_le_fourierEnvelope x).trans
    criticalFeatureFourierLatticeEnvelope_le_nine

theorem abs_criticalFeatureRealBoundaryPeriodization_sub_two_pi_le (x : ℝ) :
    |criticalFeatureRealBoundaryPeriodization x - 2 * Real.pi| ≤ (37 : ℝ) / 200 := by
  simpa only [criticalFeatureRealBoundaryPeriodization] using
    abs_tsum_criticalFeatureRealBoundaryWeight_sub_two_pi_le_thirtySeven_twoHundred x

/-- The Poisson representation makes continuity of the physical periodization explicit. -/
theorem continuous_criticalFeatureRealBoundaryPeriodization :
    Continuous criticalFeatureRealBoundaryPeriodization := by
  let Q : ℝ → ℂ := fun x =>
    ∑' n : ℤ, (criticalFeatureFourierMode n : ℂ) *
      fourier n (x : UnitAddCircle)
  have hQ : Continuous Q := by
    refine continuous_tsum (u := criticalFeatureFourierMode)
      (fun n => ?_) summable_criticalFeatureFourierMode (fun n x => ?_)
    · fun_prop
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (criticalFeatureFourierMode_nonnegative n),
        fourier_apply, Circle.norm_coe, mul_one]
  have heq : criticalFeatureRealBoundaryPeriodization = fun x => (Q x).re := by
    funext x
    have hphysical := summable_criticalFeatureRealBoundaryWeight_lattice x
    have hcoe := Complex.ofRealCLM.map_tsum hphysical
    have hpois := poisson_criticalFeatureRealBoundaryWeight x
    have hcomplex :
        ((criticalFeatureRealBoundaryPeriodization x : ℝ) : ℂ) = Q x := by
      rw [criticalFeatureRealBoundaryPeriodization]
      change
        (((∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n) : ℝ)) : ℂ) =
          ∑' n : ℤ, (criticalFeatureFourierMode n : ℂ) *
            fourier n (x : UnitAddCircle)
      exact hcoe.trans hpois
    exact congrArg Complex.re hcomplex
  rw [heq]
  exact Complex.continuous_re.comp hQ

/-- Pairing the periodized HCF profile against any integrable signed source loses at most the
`37/200` nonzero-mode envelope.  This is valid for an arbitrary measure, so restricted compact
height windows are immediate instances. -/
theorem abs_integral_criticalFeatureRealBoundaryPeriodization_mul_sub_zeroMode_le
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    |(∫ x, criticalFeatureRealBoundaryPeriodization x * g x ∂μ) -
        2 * Real.pi * ∫ x, g x ∂μ| ≤
      (37 : ℝ) / 200 * ∫ x, |g x| ∂μ := by
  let r : ℝ → ℝ := fun x => criticalFeatureRealBoundaryPeriodization x - 2 * Real.pi
  have hrcont : Continuous r :=
    continuous_criticalFeatureRealBoundaryPeriodization.sub continuous_const
  have hrbound : ∀ x, |r x| ≤ (37 : ℝ) / 200 :=
    abs_criticalFeatureRealBoundaryPeriodization_sub_two_pi_le
  have hrg : Integrable (fun x => r x * g x) μ := by
    have h := hg.bdd_mul hrcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hrbound)
    exact h
  have hPg : Integrable
      (fun x => criticalFeatureRealBoundaryPeriodization x * g x) μ := by
    have hbound : ∀ x, ‖criticalFeatureRealBoundaryPeriodization x‖ ≤ (9 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg
        (criticalFeatureRealBoundaryPeriodization_nonnegative x)]
      exact criticalFeatureRealBoundaryPeriodization_le_nine x
    have h := hg.bdd_mul
      continuous_criticalFeatureRealBoundaryPeriodization.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
    exact h
  have hrewrite :
      (∫ x, criticalFeatureRealBoundaryPeriodization x * g x ∂μ) -
          2 * Real.pi * ∫ x, g x ∂μ =
        ∫ x, r x * g x ∂μ := by
    rw [← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_sub hPg (hg.const_mul (2 * Real.pi))]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    dsimp [r]
    ring
  rw [hrewrite]
  calc
    |∫ x, r x * g x ∂μ| ≤ ∫ x, |r x * g x| ∂μ := by
      simpa [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := μ)
          (f := fun x => r x * g x))
    _ ≤ ∫ x, ((37 : ℝ) / 200) * |g x| ∂μ := by
      apply MeasureTheory.integral_mono hrg.abs (hg.abs.const_mul ((37 : ℝ) / 200))
      intro x
      change |r x * g x| ≤ (37 : ℝ) / 200 * |g x|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hrbound x) (abs_nonneg _)
    _ = (37 : ℝ) / 200 * ∫ x, |g x| ∂μ := by
      rw [MeasureTheory.integral_const_mul]

/-- Full-periodization positive-shift pole--Gamma observable on a compact height interval. -/
def criticalFeatureFullLatticePoleGammaObservable
    (A B eta : ℝ) : ℝ :=
  ∫ x in Icc A B,
    criticalFeatureRealBoundaryPeriodization x *
      criticalFeaturePositiveShiftPoleGammaDensity eta x

/-- Exact zero-frequency part of the same compact source observable. -/
def criticalFeaturePoleGammaZeroModeObservable
    (A B eta : ℝ) : ℝ :=
  2 * Real.pi * ∫ x in Icc A B,
    criticalFeaturePositiveShiftPoleGammaDensity eta x

/-- On a zero-free displaced horizontal segment the continued source density is continuous, hence
integrable.  The premise is only a regularity condition for the finite-displacement observable. -/
theorem integrableOn_criticalFeaturePositiveShiftPoleGammaDensity_of_noZero
    {A B eta : ℝ} (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hzero : ∀ x ∈ Icc A B,
      XiC ((x : ℂ) + (eta : ℂ) * I) ≠ 0) :
    IntegrableOn (criticalFeaturePositiveShiftPoleGammaDensity eta) (Icc A B) := by
  have hpath : Continuous (fun x : ℝ => (x : ℂ) + (eta : ℂ) * I) := by
    fun_prop
  have hlog : ContinuousOn
      (fun x : ℝ => logDeriv XiC ((x : ℂ) + (eta : ℂ) * I)) (Icc A B) := by
    intro x hx
    have hA : AnalyticAt ℂ (logDeriv XiC)
        ((x : ℂ) + (eta : ℂ) * I) := by
      rw [show logDeriv XiC = fun w => deriv XiC w / XiC w from rfl]
      exact (XiC_analytic _ (Set.mem_univ _)).deriv.div
        (XiC_analytic _ (Set.mem_univ _)) (hzero x hx)
    have hcomp : ContinuousAt
        ((logDeriv XiC) ∘ fun y : ℝ => (y : ℂ) + (eta : ℂ) * I) x :=
      ContinuousAt.comp (g := logDeriv XiC)
        (f := fun y : ℝ => (y : ℂ) + (eta : ℂ) * I)
        hA.continuousAt hpath.continuousAt
    change ContinuousWithinAt
      ((logDeriv XiC) ∘ fun y : ℝ => (y : ℂ) + (eta : ℂ) * I) (Icc A B) x
    exact hcomp.continuousWithinAt
  have hboundary : ContinuousOn (boundaryDensity XiC eta) (Icc A B) := by
    unfold boundaryDensity
    exact continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hlog)
  have heq : EqOn (boundaryDensity XiC eta)
      (criticalFeaturePositiveShiftPoleGammaDensity eta) (Icc A B) := by
    intro x hx
    have hneg : XiC ((x : ℂ) - (eta : ℂ) * I) ≠ 0 := by
      have hc := XiC_ne_zero_conj (hzero x hx)
      have hcoord :
          (starRingEnd ℂ) ((x : ℂ) + (eta : ℂ) * I) =
            (x : ℂ) - (eta : ℂ) * I := by
        simp
        ring
      rw [hcoord] at hc
      exact hc
    exact boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity
      heta0 hetaHalf hneg
  exact (hboundary.congr heq.symm).integrableOn_Icc

/-- Source specialization of the sharp alias budget.  Integrability is now the only regularity
premise; no zero set or divisor trace occurs in either observable. -/
theorem abs_criticalFeatureFullLatticePoleGammaObservable_sub_zeroMode_le
    (A B eta : ℝ)
    (hsource : IntegrableOn
      (criticalFeaturePositiveShiftPoleGammaDensity eta) (Icc A B)) :
    |criticalFeatureFullLatticePoleGammaObservable A B eta -
        criticalFeaturePoleGammaZeroModeObservable A B eta| ≤
      (37 : ℝ) / 200 *
        ∫ x in Icc A B, |criticalFeaturePositiveShiftPoleGammaDensity eta x| := by
  simpa [criticalFeatureFullLatticePoleGammaObservable,
    criticalFeaturePoleGammaZeroModeObservable] using
    abs_integral_criticalFeatureRealBoundaryPeriodization_mul_sub_zeroMode_le
      (volume.restrict (Icc A B)) hsource

/-- Fully discharged alias estimate on every zero-free subcritical displacement line. -/
theorem abs_criticalFeatureFullLatticePoleGammaObservable_sub_zeroMode_le_of_noZero
    {A B eta : ℝ} (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hzero : ∀ x ∈ Icc A B,
      XiC ((x : ℂ) + (eta : ℂ) * I) ≠ 0) :
    |criticalFeatureFullLatticePoleGammaObservable A B eta -
        criticalFeaturePoleGammaZeroModeObservable A B eta| ≤
      (37 : ℝ) / 200 *
        ∫ x in Icc A B, |criticalFeaturePositiveShiftPoleGammaDensity eta x| := by
  exact abs_criticalFeatureFullLatticePoleGammaObservable_sub_zeroMode_le A B eta
    (integrableOn_criticalFeaturePositiveShiftPoleGammaDensity_of_noZero
      heta0 hetaHalf hzero)

end

end RHTower
