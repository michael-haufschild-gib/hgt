import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialGraph

/-! Polynomial graph lifting and first-coordinate projection recover each other on the actual laws. -/

open MeasureTheory
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalPolynomialGraph_first_map (r k : ℕ) (ν : Measure ℝ) :
    Measure.map (fun z : E => z 0) (Measure.map (finiteWeilCanonicalPolynomialGraph r k) ν) = ν := by
  rw [Measure.map_map (by fun_prop) (continuous_finiteWeilCanonicalPolynomialGraph r k).measurable]
  exact Measure.map_id

theorem finiteWeilCanonicalPolynomialGraph_reconstruct (r k : ℕ) (a b d : ℝ) :
    Measure.map (finiteWeilCanonicalPolynomialGraph r k)
      (Measure.map (fun z : E => z 0)
        (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)) =
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) := by
  rw [Measure.map_map (continuous_finiteWeilCanonicalPolynomialGraph r k).measurable (by fun_prop)]
  calc
    _ = Measure.map id (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) :=
      Measure.map_congr (finiteWeilCanonicalPolynomialGraph_tilted_ae r k a b d)
    _ = _ := Measure.map_id

theorem finiteWeilCanonicalJointQuadraticTilt_first_marginal_eq_iff
    (r k : ℕ) (a b d A B D : ℝ) :
    Measure.map (fun z : E => z 0) (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) =
      Measure.map (fun z : E => z 0) (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) ↔
        (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) =
          (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) := by
  constructor
  · intro h
    have hgraph := congrArg (Measure.map (finiteWeilCanonicalPolynomialGraph r k)) h
    simpa only [finiteWeilCanonicalPolynomialGraph_reconstruct] using hgraph
  · intro h
    rw [h]

end RHTower
