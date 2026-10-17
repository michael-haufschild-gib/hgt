import GaloisForLFunctions.BiScaleUncertainty.NyquistPolarDecomposition
import GaloisForLFunctions.BiScaleUncertainty.FiniteIntegerTrainProducers

/-!
# Explicit Nyquist production for actual sources and diffuse polar escape

Every compact source has an unconditional all-tail producer bound. The actual
smooth diffuse train forces the cell-average producer to diverge while its
integrable residual converges under global uniform correlation convergence.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open scoped BigOperators BoundedContinuousFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

variable {K : ℝ}

def LevyEnergySource.realCorrelation (f : LevyEnergySource K) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup f.correlation f.continuous_correlation 1
    (fun x => by simpa only [Real.norm_eq_abs] using f.abs_correlation_le_one x)

@[simp]
theorem LevyEnergySource.realCorrelation_apply (f : LevyEnergySource K) (x : ℝ) :
    f.realCorrelation x = f.correlation x := rfl

theorem LevyEnergySource.norm_realCorrelation_le_one (f : LevyEnergySource K) :
    ‖f.realCorrelation‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (fun x => by simpa only [Real.norm_eq_abs, realCorrelation_apply] using f.abs_correlation_le_one x)

theorem LevyEnergySource.hasCompactSupport_realCorrelation (f : LevyEnergySource K) :
    HasCompactSupport (⇑f.realCorrelation) := by
  change HasCompactSupport (fun x => autocorr f.source x / autocorr f.source 0)
  have hh := (hasCompactSupport_autocorr f.source.hasCompactSupport).mul_right
    (f' := fun _ => (autocorr f.source 0)⁻¹)
  change HasCompactSupport (fun x => autocorr f.source x * (autocorr f.source 0)⁻¹) at hh
  simpa only [div_eq_mul_inv] using hh

def LevyEnergySource.nyquistProducer (f : LevyEnergySource K) (N : ℕ) : ℝ :=
  nyquistPolarProducer N f.realCorrelation

theorem LevyEnergySource.nyquistProducer_tail_error (f : LevyEnergySource K) (N : ℕ) :
    |nyquistPolarTail N f.realCorrelation - f.nyquistProducer N| ≤ nyquistResidualTailScale N :=
  (nyquistPolarProducer_error_le N f.realCorrelation f.hasCompactSupport_realCorrelation).trans
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left f.norm_realCorrelation_le_one (nyquistResidualTailScale_nonneg N))

theorem LevyEnergySource.nyquistResidual_abs_le (f : LevyEnergySource K) (N : ℕ) :
    |nyquistResidualOperator N f.realCorrelation| ≤ nyquistResidualTailScale N :=
  (nyquistResidualOperator_abs_le_scale N f.realCorrelation).trans
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left f.norm_realCorrelation_le_one (nyquistResidualTailScale_nonneg N))

theorem LevyEnergySource.normalizedPolarMoment_nyquist_decomposition (f : LevyEnergySource K) :
    normalizedPolarMoment f.source =
      f.nyquistProducer 0 + nyquistResidualOperator 0 f.realCorrelation := by
  have hh := nyquistPolarTail_decomposition 0 f.realCorrelation f.hasCompactSupport_realCorrelation
  rw [normalizedPolarMoment_eq_integral]
  simpa only [nyquistPolarTail, nyquistResidualNode_zero, nyquistProducer,
    realCorrelation_apply, correlation, normalizedSourceCorrelation] using hh

theorem LevyEnergySource.normalizedPolarMoment_nyquist_error (f : LevyEnergySource K) :
    |normalizedPolarMoment f.source - f.nyquistProducer 0| ≤ 1 := by
  rw [f.normalizedPolarMoment_nyquist_decomposition, add_sub_cancel_left]
  simpa only [nyquistResidualTailScale, Nat.zero_add, Nat.cast_one, Real.sqrt_one, div_one] using
    f.nyquistResidual_abs_le 0

theorem LevyEnergySource.nyquistProducer_ge_polar_sub_one (f : LevyEnergySource K) :
    normalizedPolarMoment f.source - 1 ≤ f.nyquistProducer 0 := by
  have hh := (abs_le.mp f.normalizedPolarMoment_nyquist_error).2
  linarith

/-- The exact cell-average producer carries the escape of actual smooth diffuse sources. -/
theorem exists_smooth_diffuse_nyquistProducer_escape :
    ∃ (K : ℝ) (f : LevyEnergySource K) (g : ℕ → LevyEnergySource K),
      0 ≤ K ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) (f.source : ℝ → ℝ) ∧
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) ((g n).source : ℝ → ℝ)) ∧
      0 < normalizedPolarMoment f.source ∧
      (∀ n, autocorr (g n).source 0 = ((n : ℝ) + 2) * autocorr f.source 0) ∧
      (∀ n, dist (g n).complexCorrelation f.complexCorrelation = 1 / ((n : ℝ) + 2)) ∧
      (∀ n : ℕ, (((n : ℝ) + 2) / 4) * normalizedPolarMoment f.source - 1 ≤
        (g n).nyquistProducer 0) ∧
      Tendsto (fun n => (g n).nyquistProducer 0) atTop atTop ∧
      Tendsto (fun n => nyquistResidualOperator 0 (g n).realCorrelation) atTop
        (𝓝 (nyquistResidualOperator 0 f.realCorrelation)) ∧
      TendstoUniformly (fun n => (g n).correlation) f.correlation atTop ∧
      Tendsto (fun n => normalizedArchEnergy (g n).source) atTop (𝓝 (normalizedArchEnergy f.source)) ∧
      IsCompact (closure (LevyEnergySource.complexCorrelation '' range g)) ∧
      UniformSignedGridTail (range g) := by
  obtain ⟨K, f, g, hK, hf, hg, hP, hm, hd, hp, hpt, hu, he, hc, ht⟩ :=
    exists_smooth_diffuse_train_polar_escape
  have hq (n : ℕ) : (((n : ℝ) + 2) / 4) * normalizedPolarMoment f.source - 1 ≤
      (g n).nyquistProducer 0 :=
    (sub_le_sub_right (hp n) 1).trans (g n).nyquistProducer_ge_polar_sub_one
  have hqt : Tendsto (fun n => (g n).nyquistProducer 0) atTop atTop := by
    apply tendsto_atTop_mono (f := fun n => normalizedPolarMoment (g n).source + (-1))
    · intro n
      simpa only [sub_eq_add_neg] using (g n).nyquistProducer_ge_polar_sub_one
    · exact tendsto_atTop_add_const_right atTop (-1) hpt
  have hr : Tendsto (fun n => nyquistResidualOperator 0 (g n).realCorrelation) atTop
      (𝓝 (nyquistResidualOperator 0 f.realCorrelation)) :=
    tendsto_nyquistResidualOperator_of_uniform
      (show TendstoUniformly (fun n => ⇑(g n).realCorrelation) (⇑f.realCorrelation) atTop from hu) 0
  exact ⟨K, f, g, hK, hf, hg, hP, hm, hd, hq, hqt, hr, hu, he, hc, ht⟩

end
end GaloisForLFunctions.BiScaleUncertainty
