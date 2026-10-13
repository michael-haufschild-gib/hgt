import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialGraphRecovery
import GaloisForLFunctions.HTGeometry.HellingerAffinityEmbedding
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # First coordinate preserves all finite Weil pair information

The same polynomial graph reconstructs both laws, for arbitrary finite depth and
real tilt parameters. No limiting schedule or subcriticality is needed.
-/

namespace RHTower

open MeasureTheory InformationTheory
open GaloisForLFunctions.HTGeometry

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem measurableEmbedding_finiteWeilCanonicalPolynomialGraph (r k : ℕ) :
    MeasurableEmbedding (finiteWeilCanonicalPolynomialGraph r k) :=
  (continuous_finiteWeilCanonicalPolynomialGraph r k).measurableEmbedding
    (finiteWeilCanonicalPolynomialGraph_injective r k)

/-- First-coordinate projection preserves directed relative entropy exactly. -/
theorem finiteWeilCanonicalJointQuadraticTilt_first_marginal_klDiv
    (r k : ℕ) (a b d A B D : ℝ) :
    klDiv
      (Measure.map (fun z : E => z 0)
        (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E))
      (Measure.map (fun z : E => z 0)
        (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E)) =
    klDiv (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) := by
  have h := klDiv_map_measurableEmbedding
    (measurableEmbedding_finiteWeilCanonicalPolynomialGraph r k)
    (Measure.map (fun z : E => z 0)
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E))
    (Measure.map (fun z : E => z 0)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E))
  rw [finiteWeilCanonicalPolynomialGraph_reconstruct,
    finiteWeilCanonicalPolynomialGraph_reconstruct] at h
  exact h.symm

/-- One fixed coordinate is sufficient for both directed KL costs. -/
theorem finiteWeilCanonicalJointQuadraticTilt_first_marginal_pairSufficient
    (r k : ℕ) (a b d A B D : ℝ) :
    IsKLPairSufficient (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E)
      (fun z : E => z 0) :=
  ⟨finiteWeilCanonicalJointQuadraticTilt_first_marginal_klDiv r k a b d A B D,
    finiteWeilCanonicalJointQuadraticTilt_first_marginal_klDiv r k A B D a b d⟩

/-- First-coordinate projection preserves Bhattacharyya affinity exactly. -/
theorem finiteWeilCanonicalJointQuadraticTilt_first_marginal_bhattacharyya
    (r k : ℕ) (a b d A B D : ℝ) :
    bhattacharyya
      (Measure.map (fun z : E => z 0)
        (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E))
      (Measure.map (fun z : E => z 0)
        (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E)) =
    bhattacharyya (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) := by
  have h := bhattacharyya_map_measurableEmbedding
    (measurableEmbedding_finiteWeilCanonicalPolynomialGraph r k)
    (Measure.map (fun z : E => z 0)
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E))
    (Measure.map (fun z : E => z 0)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E))
  rw [finiteWeilCanonicalPolynomialGraph_reconstruct,
    finiteWeilCanonicalPolynomialGraph_reconstruct] at h
  exact h.symm

end RHTower
