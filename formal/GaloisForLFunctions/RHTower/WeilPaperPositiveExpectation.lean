import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lower semicontinuity of continuous nonnegative spectral costs

Bounded truncations prove lower semicontinuity of the extended expectation of
every continuous nonnegative weight. The result works on any topological
measurable space whose open sets are measurable, including real spectral laws.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Extended expectation of a continuous nonnegative weight, with infinity allowed. -/
def paperPositiveExpectation (w : C(X, ℝ≥0)) (μ : ProbabilityMeasure X) : ℝ≥0∞ :=
  ∫⁻ x, (w x : ℝ≥0∞) ∂(μ : Measure X)

omit [OpensMeasurableSpace X] in
/-- The bundled nonnegative weight agrees with the ordinary real-weight convention. -/
theorem paperPositiveExpectation_eq_lintegral_ofReal
    (w : C(X, ℝ≥0)) (μ : ProbabilityMeasure X) :
    paperPositiveExpectation w μ =
      ∫⁻ x, ENNReal.ofReal (w x : ℝ) ∂(μ : Measure X) := by
  simp only [paperPositiveExpectation, ENNReal.ofReal_coe_nnreal]

private def clippedPositiveWeight (w : C(X, ℝ≥0)) (n : ℕ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (w x : ℝ) (n : ℝ))
    ((continuous_subtype_val.comp w.continuous).min continuous_const) n (by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (w x).coe_nonneg (Nat.cast_nonneg n))]
      exact min_le_right _ _)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
private theorem clippedPositiveWeight_nonneg (w : C(X, ℝ≥0)) (n : ℕ) (x : X) :
    0 ≤ clippedPositiveWeight w n x :=
  le_min (w x).coe_nonneg (Nat.cast_nonneg n)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
private theorem clippedPositiveWeight_iSup (w : C(X, ℝ≥0)) (x : X) :
    (⨆ n : ℕ, ENNReal.ofReal (clippedPositiveWeight w n x)) =
      ENNReal.ofReal (w x : ℝ) := by
  apply le_antisymm
  · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
  · obtain ⟨n, hn⟩ := exists_nat_ge (w x : ℝ)
    apply le_iSup_of_le n
    change ENNReal.ofReal (w x : ℝ) ≤ ENNReal.ofReal (min (w x : ℝ) (n : ℝ))
    rw [min_eq_left hn]

private theorem positiveExpectation_eq_iSup (w : C(X, ℝ≥0)) (μ : ProbabilityMeasure X) :
    paperPositiveExpectation w μ =
      ⨆ n : ℕ, ENNReal.ofReal (∫ x, clippedPositiveWeight w n x ∂(μ : Measure X)) := by
  rw [paperPositiveExpectation_eq_lintegral_ofReal]
  calc
    _ = ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (clippedPositiveWeight w n x) ∂(μ : Measure X) := by
      apply lintegral_congr
      intro x
      exact (clippedPositiveWeight_iSup w x).symm
    _ = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (clippedPositiveWeight w n x) ∂(μ : Measure X) :=
      lintegral_iSup (fun n => (clippedPositiveWeight w n).continuous.measurable.ennreal_ofReal)
        (fun m n hmn x => ENNReal.ofReal_le_ofReal
          (min_le_min_left _ (by exact_mod_cast hmn)))
    _ = _ := by
      apply iSup_congr
      intro n
      exact (ofReal_integral_eq_lintegral_ofReal ((clippedPositiveWeight w n).integrable _)
        (Filter.Eventually.of_forall (clippedPositiveWeight_nonneg w n))).symm

/-- Every continuous nonnegative cost has weakly lower semicontinuous extended expectation. -/
theorem lowerSemicontinuous_paperPositiveExpectation (w : C(X, ℝ≥0)) :
    LowerSemicontinuous (paperPositiveExpectation w) := by
  have heq : paperPositiveExpectation w = fun μ : ProbabilityMeasure X =>
      ⨆ n : ℕ, ENNReal.ofReal (∫ x, clippedPositiveWeight w n x ∂(μ : Measure X)) :=
    funext (positiveExpectation_eq_iSup w)
  rw [heq]
  apply lowerSemicontinuous_iSup
  intro n
  exact (ENNReal.continuous_ofReal.comp
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (clippedPositiveWeight w n))).lowerSemicontinuous

/-- Each extended expectation budget is a weakly closed constraint. -/
theorem isClosed_paperPositiveExpectation_sublevel (w : C(X, ℝ≥0)) (B : ℝ≥0∞) :
    IsClosed {μ : ProbabilityMeasure X | paperPositiveExpectation w μ ≤ B} :=
  (lowerSemicontinuous_paperPositiveExpectation w).isClosed_preimage B

end RHTower.WeilWorkPBAP
