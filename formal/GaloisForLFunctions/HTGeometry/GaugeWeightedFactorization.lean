import GaloisForLFunctions.HTGeometry.MultiplicativeGaugePerturbation
import GaloisForLFunctions.HTGeometry.RegularizedHerglotzTransform

/-!
# Factorization of the weighted measure under a multiplicative gauge

Changing the exponential parameter from `u₀` to `u₀ + log (1 + h)` multiplies the Nevanlinna
density by `1 + h`.  At the level of measures this is a `withDensity` factorization: the weighted
measure of the perturbed parameter is the weighted measure of `u₀` reweighted by `1 + h`.

This is the measure-side half of the affine reachability hypothesis.  Combined with the parameter
bound on `log (1 + h)`, it says that a uniformly small gauge produces a uniformly small parameter
change whose effect on any linear functional of the measure is exactly linear in the gauge.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

/-- The Nevanlinna density of a multiplicatively gauged parameter factors. -/
theorem nevanlinnaDensity_gauge (u₀ h : ℝ → ℝ) (hbound : ∀ t, |h t| ≤ 1 / 2) (t : ℝ) :
    (Real.toNNReal
        (nevanlinnaWeight t * Real.exp (u₀ t + Real.log (1 + h t))) : ℝ≥0∞) =
      (Real.toNNReal (nevanlinnaWeight t * Real.exp (u₀ t)) : ℝ≥0∞) *
        ENNReal.ofReal (1 + h t) := by
  have hfactor : Real.exp (u₀ t + Real.log (1 + h t)) =
      Real.exp (u₀ t) * (1 + h t) :=
    exp_add_log_one_add (hbound t)
  have hnonneg : 0 ≤ nevanlinnaWeight t * Real.exp (u₀ t) :=
    le_of_lt (mul_pos (nevanlinnaWeight_pos t) (Real.exp_pos _))
  have hassoc : nevanlinnaWeight t * Real.exp (u₀ t + Real.log (1 + h t)) =
      (nevanlinnaWeight t * Real.exp (u₀ t)) * (1 + h t) := by
    rw [hfactor]
    ring
  rw [hassoc]
  show ENNReal.ofReal _ = ENNReal.ofReal _ * ENNReal.ofReal _
  exact ENNReal.ofReal_mul hnonneg

/-- **Multiplicative gauge factorization.**  The Nevanlinna-weighted measure of the gauged
parameter is the weighted measure of the base parameter, reweighted by the gauge. -/
theorem nevanlinnaWeightedMeasure_gauge
    (μ : Measure ℝ) (u₀ h : ℝ → ℝ)
    (hu₀ : Measurable u₀) (hh : Measurable h)
    (hbound : ∀ t, |h t| ≤ 1 / 2) :
    nevanlinnaWeightedMeasure μ (fun t => u₀ t + Real.log (1 + h t)) =
      (nevanlinnaWeightedMeasure μ u₀).withDensity
        (fun t => ENNReal.ofReal (1 + h t)) := by
  have hd0 : Measurable
      (fun t : ℝ => (Real.toNNReal (nevanlinnaWeight t * Real.exp (u₀ t)) : ℝ≥0∞)) := by
    apply Measurable.coe_nnreal_ennreal
    apply Measurable.real_toNNReal
    apply Measurable.mul
    · unfold nevanlinnaWeight
      fun_prop
    · exact Real.measurable_exp.comp hu₀
  have hg : Measurable (fun t : ℝ => ENNReal.ofReal (1 + h t)) := by
    apply ENNReal.measurable_ofReal.comp
    fun_prop
  rw [nevanlinnaWeightedMeasure, nevanlinnaWeightedMeasure,
    ← withDensity_mul _ hd0 hg]
  congr 1
  funext t
  exact nevanlinnaDensity_gauge u₀ h hbound t

/-- **The gauge moves integrals by exactly a linear term.**  Integrating against the gauged measure
adds precisely the pairing of the gauge with the integrand: there is no linearization error. -/
theorem integral_withDensity_one_add (ν : Measure ℝ)
    (h : ℝ → ℝ) (hh : Measurable h) (hbound : ∀ t, |h t| ≤ 1 / 2)
    (g : ℝ → ℂ) (hg : Integrable g ν)
    (hhg : Integrable (fun t => ((h t : ℝ) : ℂ) * g t) ν) :
    ∫ t, g t ∂(ν.withDensity (fun t => ENNReal.ofReal (1 + h t))) =
      ∫ t, g t ∂ν + ∫ t, ((h t : ℝ) : ℂ) * g t ∂ν := by
  have hmeas : Measurable (fun t : ℝ => Real.toNNReal (1 + h t)) := by
    apply Measurable.real_toNNReal
    fun_prop
  have hdens : (fun t : ℝ => ENNReal.ofReal (1 + h t)) =
      fun t : ℝ => ((Real.toNNReal (1 + h t) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hdens, integral_withDensity_eq_integral_smul hmeas]
  rw [← integral_add hg hhg]
  apply integral_congr_ae
  filter_upwards with t
  have hpos : 0 ≤ 1 + h t := le_of_lt (one_add_pos_of_abs_le_half (hbound t))
  rw [NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal _ hpos]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
