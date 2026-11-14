import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.FiniteGammaCoxLaw
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Expected statistics of Gamma–Cox detections

The expectation of a weighted occupancy statistic is the sum of its integrated
Gamma–Poisson marginals. Its limit is the weighted mass of the exact zero set.
Weights may have either sign, and candidate locations may repeat.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators Classical
namespace GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
noncomputable section

/-- The expected weighted occupancy is the sum of the marginal detection probabilities. -/
theorem integral_weighted_occupancy {ι : Type*} [Fintype ι]
    (K : ℝ) (g w : ι → ℝ) :
    (∫ b, ∑ i, if b i then w i else 0 ∂binaryLaw K g) =
      ∑ i, w i * detection (max K 0) (g i) := by
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  change (∫ b, (fun c : Bool => if c then w i else 0) (b i)
    ∂Measure.pi (fun j => bernoulliMeasure true false (parameter K (g j)))) = _
  rw [integral_comp_eval
    (μ := fun j => bernoulliMeasure true false (parameter K (g j))) (i := i)
    (f := fun c : Bool => if c then w i else 0) (Integrable.of_finite.aestronglyMeasurable),
    integral_bernoulliMeasure]
  simp [parameter, mul_comm]

/-- Expected weighted detections converge to the exact weighted zero count. -/
theorem tendsto_expected_occupancy {ι : Type*} [Fintype ι] (g w : ι → ℝ) :
    Tendsto (fun K => ∫ b, ∑ i, if b i then w i else 0 ∂binaryLaw K g)
      atTop (𝓝 (∑ i, if g i = 0 then w i else 0)) := by
  simp_rw [integral_weighted_occupancy]
  apply (tendsto_weighted_detection Finset.univ g w).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with K hK
  rw [max_eq_left hK]

end
end GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.integral_weighted_occupancy
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_expected_occupancy
