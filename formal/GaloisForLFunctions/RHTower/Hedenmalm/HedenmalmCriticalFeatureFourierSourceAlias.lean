import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSourceAliasBudget
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import GaloisForLFunctions.HTGeometry.HarmonicLogEquidistribution
import GaloisForLFunctions.HTGeometry.IntegerTorusHomomorphism
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Phase-preserving Fourier scalarization of the HCF source alias

The existing `37 / 200` alias budget takes the pointwise absolute value of the complete nonzero
Poisson ripple before pairing it with the signed pole--Gamma source.  This module retains every
Fourier phase through the sole Lebesgue scalarization.  The full-periodization error is exactly an
absolutely summable series of source Fourier coefficients, with the zero mode removed.

No Xi zero or divisor copy occurs in the new observable.  Consequently a source-side
fixed-frequency explicit-formula estimate can now cancel aliases before divisor scalarization.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Fourier coefficient of an integrable real source against the physical HCF integer character. -/
def criticalFeatureSourceFourierCoefficient
    (μ : Measure ℝ) (g : ℝ → ℝ) (n : ℤ) : ℂ :=
  ∫ x, fourier n (x : UnitAddCircle) * (g x : ℂ) ∂μ

private theorem integrable_criticalFeatureFourierTerm
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) (n : ℤ) :
    Integrable (fun (x : ℝ) =>
      (criticalFeatureFourierMode n : ℂ) *
        fourier n (x : UnitAddCircle) * (g x : ℂ)) μ := by
  have hgC : Integrable (fun (x : ℝ) => (g x : ℂ)) μ := hg.ofReal
  apply hgC.bdd_mul
  · fun_prop
  · filter_upwards with x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (criticalFeatureFourierMode_nonnegative n),
      fourier_apply, Circle.norm_coe, mul_one]

private theorem integral_norm_criticalFeatureFourierTerm
    (μ : Measure ℝ) {g : ℝ → ℝ} (_hg : Integrable g μ) (n : ℤ) :
    (∫ x : ℝ, ‖(criticalFeatureFourierMode n : ℂ) *
        fourier n (x : UnitAddCircle) * (g x : ℂ)‖ ∂μ) =
      criticalFeatureFourierMode n * ∫ x, |g x| ∂μ := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (criticalFeatureFourierMode_nonnegative n),
    fourier_apply, Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs]
  ring

private theorem summable_integral_norm_criticalFeatureFourierTerm
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    Summable fun n : ℤ =>
      ∫ x : ℝ, ‖(criticalFeatureFourierMode n : ℂ) *
        fourier n (x : UnitAddCircle) * (g x : ℂ)‖ ∂μ := by
  have h := summable_criticalFeatureFourierMode.mul_right
    (∫ x, |g x| ∂μ)
  exact h.congr fun n =>
    (integral_norm_criticalFeatureFourierTerm μ hg n).symm

/-- Exact all-mode Fourier scalarization of the full HCF periodization against a signed source. -/
theorem ofReal_integral_criticalFeatureRealBoundaryPeriodization_mul_eq_tsum_fourier
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    ((∫ x, criticalFeatureRealBoundaryPeriodization x * g x ∂μ : ℝ) : ℂ) =
      ∑' n : ℤ, (criticalFeatureFourierMode n : ℂ) *
        criticalFeatureSourceFourierCoefficient μ g n := by
  let F : ℤ → ℝ → ℂ := fun n x =>
    (criticalFeatureFourierMode n : ℂ) *
      fourier n (x : UnitAddCircle) * (g x : ℂ)
  have hFint : ∀ n, Integrable (F n) μ :=
    fun n => integrable_criticalFeatureFourierTerm μ hg n
  have hFsum : Summable fun n => ∫ x, ‖F n x‖ ∂μ :=
    summable_integral_norm_criticalFeatureFourierTerm μ hg
  have hpoint (x : ℝ) :
      ((criticalFeatureRealBoundaryPeriodization x : ℝ) : ℂ) =
        ∑' n : ℤ, (criticalFeatureFourierMode n : ℂ) *
          fourier n (x : UnitAddCircle) := by
    have hphysical := summable_criticalFeatureRealBoundaryWeight_lattice x
    have hcoe := Complex.ofRealCLM.map_tsum hphysical
    change
      (((∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n) : ℝ)) : ℂ) =
        ∑' n : ℤ, (criticalFeatureRealBoundaryWeight 0 (x + n) : ℂ) at hcoe
    have hpois := poisson_criticalFeatureRealBoundaryWeight x
    rw [criticalFeatureRealBoundaryPeriodization]
    change
      (((∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n) : ℝ)) : ℂ) = _
    exact hcoe.trans (by
      simpa only [criticalFeatureFourierMode] using hpois)
  have hPg : Integrable
      (fun x => criticalFeatureRealBoundaryPeriodization x * g x) μ := by
    have hbound : ∀ x,
        ‖criticalFeatureRealBoundaryPeriodization x‖ ≤ (9 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg
        (criticalFeatureRealBoundaryPeriodization_nonnegative x)]
      exact criticalFeatureRealBoundaryPeriodization_le_nine x
    exact hg.bdd_mul
      continuous_criticalFeatureRealBoundaryPeriodization.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  calc
    ((∫ x, criticalFeatureRealBoundaryPeriodization x * g x ∂μ : ℝ) : ℂ) =
        ∫ x, ((criticalFeatureRealBoundaryPeriodization x * g x : ℝ) : ℂ) ∂μ := by
      exact (Complex.ofRealCLM.integral_comp_comm hPg).symm
    _ = ∫ x, ∑' n : ℤ, F n x ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      dsimp only [F]
      calc
        ((criticalFeatureRealBoundaryPeriodization x * g x : ℝ) : ℂ) =
            ((criticalFeatureRealBoundaryPeriodization x : ℝ) : ℂ) * (g x : ℂ) := by
          norm_cast
        _ = (∑' n : ℤ, (criticalFeatureFourierMode n : ℂ) *
            fourier n (x : UnitAddCircle)) * (g x : ℂ) := by rw [hpoint x]
        _ = ∑' n : ℤ, (criticalFeatureFourierMode n : ℂ) *
            fourier n (x : UnitAddCircle) * (g x : ℂ) := by
          rw [← tsum_mul_right]
    _ = ∑' n : ℤ, ∫ x, F n x ∂μ :=
      (MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFsum).tsum_eq.symm
    _ = ∑' n : ℤ, (criticalFeatureFourierMode n : ℂ) *
        criticalFeatureSourceFourierCoefficient μ g n := by
      apply tsum_congr
      intro n
      dsimp only [F, criticalFeatureSourceFourierCoefficient]
      simp_rw [mul_assoc]
      rw [MeasureTheory.integral_const_mul]

/-- Exact all-mode scalarization after translating the complete HCF height lattice by a real
phase.  Translation appears only as the corresponding unit-circle character. -/
theorem ofReal_integral_criticalFeatureRealBoundaryPeriodization_add_mul_eq_tsum_fourier_phase
    (θ : ℝ) (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    ((∫ x, criticalFeatureRealBoundaryPeriodization (x + θ) * g x ∂μ : ℝ) : ℂ) =
      ∑' n : ℤ, ((criticalFeatureFourierMode n : ℂ) *
        criticalFeatureSourceFourierCoefficient μ g n) *
          fourier n (θ : UnitAddCircle) := by
  let F : ℤ → ℝ → ℂ := fun n x =>
    (criticalFeatureFourierMode n : ℂ) *
      fourier n ((x + θ : ℝ) : UnitAddCircle) * (g x : ℂ)
  have hFint : ∀ n, Integrable (F n) μ := by
    intro n
    have hgC : Integrable (fun (x : ℝ) => (g x : ℂ)) μ := hg.ofReal
    apply hgC.bdd_mul
    · fun_prop
    · filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (criticalFeatureFourierMode_nonnegative n),
        fourier_apply, Circle.norm_coe, mul_one]
  have hFnorm (n : ℤ) :
      (∫ x : ℝ, ‖F n x‖ ∂μ) =
        criticalFeatureFourierMode n * ∫ x, |g x| ∂μ := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    dsimp only [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (criticalFeatureFourierMode_nonnegative n),
      fourier_apply, Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hFsum : Summable fun n => ∫ x, ‖F n x‖ ∂μ := by
    have h := summable_criticalFeatureFourierMode.mul_right
      (∫ x, |g x| ∂μ)
    exact h.congr fun n => (hFnorm n).symm
  have hpoint (x : ℝ) :
      ((criticalFeatureRealBoundaryPeriodization (x + θ) : ℝ) : ℂ) =
        ∑' n : ℤ, (criticalFeatureFourierMode n : ℂ) *
          fourier n ((x + θ : ℝ) : UnitAddCircle) := by
    have hphysical := summable_criticalFeatureRealBoundaryWeight_lattice (x + θ)
    have hcoe := Complex.ofRealCLM.map_tsum hphysical
    change
      (((∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + θ + n) : ℝ)) : ℂ) =
        ∑' n : ℤ, (criticalFeatureRealBoundaryWeight 0 (x + θ + n) : ℂ) at hcoe
    have hpois := poisson_criticalFeatureRealBoundaryWeight (x + θ)
    rw [criticalFeatureRealBoundaryPeriodization]
    change
      (((∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + θ + n) : ℝ)) : ℂ) = _
    exact hcoe.trans (by
      simpa only [criticalFeatureFourierMode] using hpois)
  have hPg : Integrable
      (fun x => criticalFeatureRealBoundaryPeriodization (x + θ) * g x) μ := by
    have hbound : ∀ x,
        ‖criticalFeatureRealBoundaryPeriodization (x + θ)‖ ≤ (9 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg
        (criticalFeatureRealBoundaryPeriodization_nonnegative (x + θ))]
      exact criticalFeatureRealBoundaryPeriodization_le_nine (x + θ)
    exact hg.bdd_mul
      (continuous_criticalFeatureRealBoundaryPeriodization.comp
        (continuous_id.add continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  calc
    ((∫ x, criticalFeatureRealBoundaryPeriodization (x + θ) * g x ∂μ : ℝ) : ℂ) =
        ∫ x, ((criticalFeatureRealBoundaryPeriodization (x + θ) * g x : ℝ) : ℂ) ∂μ := by
      exact (Complex.ofRealCLM.integral_comp_comm hPg).symm
    _ = ∫ x, ∑' n : ℤ, F n x ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      dsimp only [F]
      calc
        ((criticalFeatureRealBoundaryPeriodization (x + θ) * g x : ℝ) : ℂ) =
            ((criticalFeatureRealBoundaryPeriodization (x + θ) : ℝ) : ℂ) * (g x : ℂ) := by
          norm_cast
        _ = (∑' n : ℤ, (criticalFeatureFourierMode n : ℂ) *
            fourier n ((x + θ : ℝ) : UnitAddCircle)) * (g x : ℂ) := by
          rw [hpoint x]
        _ = ∑' n : ℤ, (criticalFeatureFourierMode n : ℂ) *
            fourier n ((x + θ : ℝ) : UnitAddCircle) * (g x : ℂ) := by
          rw [← tsum_mul_right]
    _ = ∑' n : ℤ, ∫ x, F n x ∂μ :=
      (MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFsum).tsum_eq.symm
    _ = ∑' n : ℤ, ((criticalFeatureFourierMode n : ℂ) *
        criticalFeatureSourceFourierCoefficient μ g n) *
          fourier n (θ : UnitAddCircle) := by
      apply tsum_congr
      intro n
      dsimp only [F, criticalFeatureSourceFourierCoefficient]
      have hadd (x : ℝ) :
          fourier n ((x + θ : ℝ) : UnitAddCircle) =
            fourier n (x : UnitAddCircle) * fourier n (θ : UnitAddCircle) := by
        rw [show ((x + θ : ℝ) : UnitAddCircle) =
            (x : UnitAddCircle) + (θ : UnitAddCircle) by
          exact map_add
            (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) x θ]
        exact GaloisForLFunctions.HTGeometry.fourier_point_add n _ _
      calc
        (∫ x : ℝ, (criticalFeatureFourierMode n : ℂ) *
            fourier n ((x + θ : ℝ) : UnitAddCircle) * (g x : ℂ) ∂μ) =
            ∫ x : ℝ, ((criticalFeatureFourierMode n : ℂ) *
              fourier n (θ : UnitAddCircle)) *
                (fourier n (x : UnitAddCircle) * (g x : ℂ)) ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [hadd]
          ring
        _ = ((criticalFeatureFourierMode n : ℂ) *
              fourier n (θ : UnitAddCircle)) *
                ∫ x : ℝ, fourier n (x : UnitAddCircle) * (g x : ℂ) ∂μ := by
          rw [MeasureTheory.integral_const_mul]
        _ = ((criticalFeatureFourierMode n : ℂ) *
            (∫ x : ℝ, fourier n (x : UnitAddCircle) * (g x : ℂ) ∂μ)) *
              fourier n (θ : UnitAddCircle) := by ring

/-- Phase-preserving nonzero-frequency source alias. -/
def criticalFeatureSourceNonzeroFourierAlias
    (μ : Measure ℝ) (g : ℝ → ℝ) : ℂ :=
  ∑' n : ℤ, if n = 0 then 0 else
    (criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n

private theorem criticalFeatureSourceFourierCoefficient_zero
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    criticalFeatureSourceFourierCoefficient μ g 0 =
      ((∫ x, g x ∂μ : ℝ) : ℂ) := by
  rw [criticalFeatureSourceFourierCoefficient]
  have hcoe := Complex.ofRealCLM.integral_comp_comm hg
  change (∫ x : ℝ, (g x : ℂ) ∂μ) = ((∫ x, g x ∂μ : ℝ) : ℂ) at hcoe
  simpa using hcoe

theorem summable_criticalFeatureWeightedSourceFourierCoefficient
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    Summable fun n : ℤ => (criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n := by
  let F : ℤ → ℝ → ℂ := fun n x =>
    (criticalFeatureFourierMode n : ℂ) *
      fourier n (x : UnitAddCircle) * (g x : ℂ)
  have hFsum : Summable fun n => ∫ x, ‖F n x‖ ∂μ :=
    summable_integral_norm_criticalFeatureFourierTerm μ hg
  have hintegral : Summable fun n => ∫ x, F n x ∂μ := by
    exact Summable.of_norm_bounded hFsum fun n =>
      MeasureTheory.norm_integral_le_integral_norm (f := F n)
  exact hintegral.congr fun n => by
    dsimp only [F, criticalFeatureSourceFourierCoefficient]
    simp_rw [mul_assoc]
    rw [MeasureTheory.integral_const_mul]

/-- Exact replacement for the `37 / 200 * L¹` estimate: the full-periodization error is the
complete nonzero Fourier alias, with all source phases retained. -/
theorem ofReal_integral_criticalFeatureRealBoundaryPeriodization_mul_sub_zeroMode_eq_alias
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    (((∫ x, criticalFeatureRealBoundaryPeriodization x * g x ∂μ) -
        2 * Real.pi * ∫ x, g x ∂μ : ℝ) : ℂ) =
      criticalFeatureSourceNonzeroFourierAlias μ g := by
  let a : ℤ → ℂ := fun n =>
    (criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n
  let z : ℤ → ℂ := fun n => if n = 0 then a n else 0
  let r : ℤ → ℂ := fun n => if n = 0 then 0 else a n
  have ha : Summable a :=
    summable_criticalFeatureWeightedSourceFourierCoefficient μ hg
  have hz : Summable z := by
    exact Summable.of_norm_bounded ha.norm fun n => by
      dsimp only [z]
      split_ifs <;> simp
  have hr : Summable r := by
    have hsub := ha.sub hz
    exact hsub.congr fun n => by
      dsimp only [a, z, r]
      split_ifs <;> ring
  have hsplit : (∑' n, a n) = (∑' n, z n) + ∑' n, r n := by
    rw [← (hz.tsum_add hr)]
    apply tsum_congr
    intro n
    dsimp only [z, r]
    split_ifs <;> ring
  have hzsum : (∑' n, z n) = a 0 := by
    dsimp only [z]
    exact tsum_ite_eq 0 a
  push_cast
  rw [ofReal_integral_criticalFeatureRealBoundaryPeriodization_mul_eq_tsum_fourier μ hg]
  change (∑' n, a n) - (2 : ℂ) * (Real.pi : ℂ) *
      ((∫ x, g x ∂μ : ℝ) : ℂ) = _
  have ha0 : a 0 = (2 : ℂ) * (Real.pi : ℂ) *
      ((∫ x, g x ∂μ : ℝ) : ℂ) := by
    dsimp only [a]
    rw [criticalFeatureSourceFourierCoefficient_zero μ hg]
    simp [criticalFeatureFourierMode]
  rw [hsplit, hzsum, ha0]
  change _ = ∑' n, if n = 0 then 0 else
    (criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n
  rw [show (∑' n, r n) = ∑' n, if n = 0 then 0 else
      (criticalFeatureFourierMode n : ℂ) *
        criticalFeatureSourceFourierCoefficient μ g n by rfl]
  ring

/-- Nonzero-frequency source alias after translating the complete HCF height lattice by a circle
phase.  Translation changes only Fourier phases; source coefficients remain untouched. -/
def criticalFeatureSourceNonzeroFourierAliasAtPhase
    (θ : UnitAddCircle) (μ : Measure ℝ) (g : ℝ → ℝ) : ℂ :=
  ∑' n : ℤ, if n = 0 then 0 else
    ((criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n) * fourier n θ

/-- Physical translated scalarization with its exact zero mode removed.  The remainder is exactly
the phase-twisted source alias, without taking an absolute value or selecting any Xi divisor. -/
theorem ofReal_integral_criticalFeatureRealBoundaryPeriodization_add_mul_sub_zeroMode_eq_aliasAtPhase
    (θ : ℝ) (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    (((∫ x, criticalFeatureRealBoundaryPeriodization (x + θ) * g x ∂μ) -
        2 * Real.pi * ∫ x, g x ∂μ : ℝ) : ℂ) =
      criticalFeatureSourceNonzeroFourierAliasAtPhase
        (θ : UnitAddCircle) μ g := by
  let a : ℤ → ℂ := fun n =>
    (criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n
  let p : ℤ → ℂ := fun n => a n * fourier n (θ : UnitAddCircle)
  let z : ℤ → ℂ := fun n => if n = 0 then p n else 0
  let r : ℤ → ℂ := fun n => if n = 0 then 0 else p n
  have ha : Summable a :=
    summable_criticalFeatureWeightedSourceFourierCoefficient μ hg
  have hp : Summable p := by
    apply Summable.of_norm_bounded ha.norm
    intro n
    dsimp only [p]
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have hz : Summable z := by
    exact Summable.of_norm_bounded hp.norm fun n => by
      dsimp only [z]
      split_ifs <;> simp
  have hr : Summable r := by
    have hsub := hp.sub hz
    exact hsub.congr fun n => by
      dsimp only [z, r]
      split_ifs <;> ring
  have hsplit : (∑' n, p n) = (∑' n, z n) + ∑' n, r n := by
    rw [← hz.tsum_add hr]
    apply tsum_congr
    intro n
    dsimp only [z, r]
    split_ifs <;> ring
  have hzsum : (∑' n, z n) = p 0 := by
    dsimp only [z]
    exact tsum_ite_eq 0 p
  push_cast
  rw [ofReal_integral_criticalFeatureRealBoundaryPeriodization_add_mul_eq_tsum_fourier_phase
    θ μ hg]
  change (∑' n, p n) - (2 : ℂ) * (Real.pi : ℂ) *
      ((∫ x, g x ∂μ : ℝ) : ℂ) = _
  have hp0 : p 0 = (2 : ℂ) * (Real.pi : ℂ) *
      ((∫ x, g x ∂μ : ℝ) : ℂ) := by
    dsimp only [p, a]
    rw [criticalFeatureSourceFourierCoefficient_zero μ hg]
    simp [criticalFeatureFourierMode]
  rw [hsplit, hzsum, hp0]
  change _ = ∑' n, if n = 0 then 0 else
    ((criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n) *
        fourier n (θ : UnitAddCircle)
  rw [show (∑' n, r n) = ∑' n, if n = 0 then 0 else
      ((criticalFeatureFourierMode n : ℂ) *
        criticalFeatureSourceFourierCoefficient μ g n) *
          fourier n (θ : UnitAddCircle) by rfl]
  ring

/-- The unshifted phase recovers the original phase-preserving source alias exactly. -/
theorem criticalFeatureSourceNonzeroFourierAliasAtPhase_zero
    (μ : Measure ℝ) (g : ℝ → ℝ) :
    criticalFeatureSourceNonzeroFourierAliasAtPhase 0 μ g =
      criticalFeatureSourceNonzeroFourierAlias μ g := by
  unfold criticalFeatureSourceNonzeroFourierAliasAtPhase
    criticalFeatureSourceNonzeroFourierAlias
  apply tsum_congr
  intro n
  split_ifs <;> simp

/-- Absolute summability gives a continuous source-alias function of translation phase. -/
theorem continuous_criticalFeatureSourceNonzeroFourierAliasAtPhase
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    Continuous (fun θ : UnitAddCircle =>
      criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g) := by
  let a : ℤ → ℂ := fun n =>
    (criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n
  have ha : Summable a :=
    summable_criticalFeatureWeightedSourceFourierCoefficient μ hg
  unfold criticalFeatureSourceNonzeroFourierAliasAtPhase
  change Continuous (fun θ : UnitAddCircle =>
    ∑' n : ℤ, if n = 0 then 0 else a n * fourier n θ)
  refine continuous_tsum (u := fun n : ℤ => ‖a n‖) (fun n => ?_)
    ha.norm (fun n θ => ?_)
  · split_ifs
    · exact continuous_zero
    · fun_prop
  · split_ifs
    · simp
    · simp [fourier_apply]

/-- Haar translation kills every nonzero HCF Fourier alias exactly.  This is a pre-divisor,
zero-independent de-aliasing identity; it uses only absolute summability of the source pairing. -/
theorem integral_criticalFeatureSourceNonzeroFourierAliasAtPhase_eq_zero
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    (∫ θ : UnitAddCircle,
        criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g
      ∂GaloisForLFunctions.unitCircleHaar) = 0 := by
  let a : ℤ → ℂ := fun n =>
    (criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n
  let F : ℤ → UnitAddCircle → ℂ := fun n θ =>
    if n = 0 then 0 else a n * fourier n θ
  have ha : Summable a :=
    summable_criticalFeatureWeightedSourceFourierCoefficient μ hg
  have hFint : ∀ n, Integrable (F n) GaloisForLFunctions.unitCircleHaar := by
    intro n
    dsimp only [F]
    split_ifs
    · rw [← integrableOn_univ]
      exact continuous_zero.continuousOn.integrableOn_compact isCompact_univ
    · rw [← integrableOn_univ]
      have hc : Continuous (fun θ : UnitAddCircle => a n * fourier n θ) := by
        fun_prop
      exact hc.continuousOn.integrableOn_compact isCompact_univ
  have hFnorm (n : ℤ) :
      (∫ θ : UnitAddCircle, ‖F n θ‖
        ∂GaloisForLFunctions.unitCircleHaar) =
        if n = 0 then 0 else ‖a n‖ := by
    dsimp only [F]
    split_ifs
    · simp
    · simp [fourier_apply]
  have hFsum : Summable fun n =>
      ∫ θ : UnitAddCircle, ‖F n θ‖
        ∂GaloisForLFunctions.unitCircleHaar := by
    exact Summable.of_norm_bounded ha.norm fun n => by
      rw [hFnorm]
      split_ifs <;> simp
  change (∫ θ : UnitAddCircle, ∑' n : ℤ,
      (if n = 0 then 0 else a n * fourier n θ)
      ∂GaloisForLFunctions.unitCircleHaar) = 0
  rw [(MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFsum).tsum_eq.symm]
  have hzero :
      (fun n : ℤ => ∫ θ : UnitAddCircle, F n θ
        ∂GaloisForLFunctions.unitCircleHaar) = (fun _ => (0 : ℂ)) := by
    funext n
    dsimp only [F]
    split_ifs with hn
    · simp
    · rw [MeasureTheory.integral_const_mul,
        GaloisForLFunctions.integral_fourier_unitCircleHaar, if_neg hn, mul_zero]
  rw [hzero, tsum_zero]

/-- A zero-mean continuous complex reporter has a phase at which its real part is nonpositive. -/
private theorem exists_re_nonpos_of_integral_unitCircleHaar_eq_zero
    (f : UnitAddCircle → ℂ) (hf : Continuous f)
    (hmean : (∫ θ, f θ ∂GaloisForLFunctions.unitCircleHaar) = 0) :
    ∃ θ, (f θ).re ≤ 0 := by
  by_contra hnone
  push Not at hnone
  have hfRe : Continuous (fun θ => (f θ).re) :=
    Complex.continuous_re.comp hf
  have hfInt : Integrable f GaloisForLFunctions.unitCircleHaar := by
    rw [← integrableOn_univ]
    exact hf.continuousOn.integrableOn_compact isCompact_univ
  have hfReInt : Integrable (fun θ => (f θ).re)
      GaloisForLFunctions.unitCircleHaar := by
    rw [← integrableOn_univ]
    exact hfRe.continuousOn.integrableOn_compact isCompact_univ
  have hpos : 0 < ∫ θ, (f θ).re ∂GaloisForLFunctions.unitCircleHaar := by
    rw [integral_pos_iff_support_of_nonneg (fun θ => (hnone θ).le) hfReInt]
    haveI : GaloisForLFunctions.unitCircleHaar.IsOpenPosMeasure := by
      show AddCircle.haarAddCircle.IsOpenPosMeasure
      infer_instance
    have hopen : IsOpen {θ : UnitAddCircle | 0 < (f θ).re} :=
      isOpen_lt continuous_const hfRe
    have hsub : {θ : UnitAddCircle | 0 < (f θ).re} ⊆
        Function.support fun θ => (f θ).re :=
      fun θ hθ => ne_of_gt hθ
    exact lt_of_lt_of_le
      (hopen.measure_pos _ ⟨0, hnone 0⟩) (measure_mono hsub)
  have hre := Complex.reCLM.integral_comp_comm hfInt
  have hzero : (∫ θ, (f θ).re ∂GaloisForLFunctions.unitCircleHaar) = 0 := by
    change (∫ θ, Complex.reCLM (f θ) ∂GaloisForLFunctions.unitCircleHaar) =
      Complex.reCLM (∫ θ, f θ ∂GaloisForLFunctions.unitCircleHaar) at hre
    rw [hmean] at hre
    simpa using hre
  linarith

/-- The source Fourier data select a circle phase with no positive real alias contribution. -/
theorem exists_criticalFeatureSourceAliasPhase_re_nonpos
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    ∃ θ : UnitAddCircle,
      (criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g).re ≤ 0 := by
  exact exists_re_nonpos_of_integral_unitCircleHaar_eq_zero
    (fun θ => criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g)
    (continuous_criticalFeatureSourceNonzeroFourierAliasAtPhase μ hg)
    (integral_criticalFeatureSourceNonzeroFourierAliasAtPhase_eq_zero μ hg)

/-- The same zero-mean source alias also attains a phase with nonnegative real part.  This is the
orientation needed when the Plemelj covariance subtracts the physical core observable. -/
theorem exists_criticalFeatureSourceAliasPhase_re_nonneg
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    ∃ θ : UnitAddCircle,
      0 ≤ (criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g).re := by
  let f : UnitAddCircle → ℂ := fun θ =>
    criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g
  have hf : Continuous f :=
    continuous_criticalFeatureSourceNonzeroFourierAliasAtPhase μ hg
  have hfInt : Integrable f GaloisForLFunctions.unitCircleHaar := by
    rw [← integrableOn_univ]
    exact hf.continuousOn.integrableOn_compact isCompact_univ
  have hmean : (∫ θ, f θ ∂GaloisForLFunctions.unitCircleHaar) = 0 :=
    integral_criticalFeatureSourceNonzeroFourierAliasAtPhase_eq_zero μ hg
  have hmeanNeg :
      (∫ θ, -f θ ∂GaloisForLFunctions.unitCircleHaar) = 0 := by
    rw [MeasureTheory.integral_neg, hmean, neg_zero]
  obtain ⟨θ, hθ⟩ :=
    exists_re_nonpos_of_integral_unitCircleHaar_eq_zero
      (fun θ => -f θ) hf.neg hmeanNeg
  refine ⟨θ, ?_⟩
  change 0 ≤ (f θ).re
  simpa using hθ

/-- Real representative form of the source-selected nonpositive phase, ready for translated
lattice receiver geometry. -/
theorem exists_real_criticalFeatureSourceAliasPhase_re_nonpos
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    ∃ θ : ℝ,
      (criticalFeatureSourceNonzeroFourierAliasAtPhase
        (θ : UnitAddCircle) μ g).re ≤ 0 := by
  obtain ⟨ϑ, hϑ⟩ := exists_criticalFeatureSourceAliasPhase_re_nonpos μ hg
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective ϑ
  exact ⟨θ, hϑ⟩

/-- Real representative of a source-selected phase with nonnegative real alias. -/
theorem exists_real_criticalFeatureSourceAliasPhase_re_nonneg
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    ∃ θ : ℝ,
      0 ≤ (criticalFeatureSourceNonzeroFourierAliasAtPhase
        (θ : UnitAddCircle) μ g).re := by
  obtain ⟨ϑ, hϑ⟩ := exists_criticalFeatureSourceAliasPhase_re_nonneg μ hg
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective ϑ
  exact ⟨θ, hϑ⟩

end

end RHTower
