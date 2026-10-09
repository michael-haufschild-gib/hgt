import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Homotopy.Path
import Mathlib.Tactic

open Complex Topology
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A positively oriented geometric circle, based at its rightmost point. -/
def positiveCirclePath (c : ℂ) (R : ℝ) : Path (c + R) (c + R) where
  toFun t := circleMap c R (2 * Real.pi * (t : ℝ))
  continuous_toFun := by unfold circleMap; fun_prop
  source' := by simp [circleMap]
  target' := by simp [circleMap, Complex.ofReal_mul]

@[simp] theorem positiveCirclePath_apply (c : ℂ) (R : ℝ) (t : I) :
    positiveCirclePath c R t = circleMap c R (2 * Real.pi * (t : ℝ)) := rfl

/-- A half-circle in a quadratic power coordinate. -/
def quadraticRootHalfCircle (r : ℝ) : C(I, ℂ) where
  toFun t := circleMap 0 r (Real.pi * (t : ℝ))
  continuous_toFun := by unfold circleMap; fun_prop

@[simp] theorem quadraticRootHalfCircle_zero (r : ℝ) :
    quadraticRootHalfCircle r 0 = (r : ℂ) := by simp [quadraticRootHalfCircle, circleMap]

@[simp] theorem quadraticRootHalfCircle_one (r : ℝ) :
    quadraticRootHalfCircle r 1 = -(r : ℂ) := by simp [quadraticRootHalfCircle, circleMap]

/-- Squaring the lifted half-circle gives the full target circle exactly. -/
theorem quadraticRootHalfCircle_sq (r : ℝ) (t : I) :
    quadraticRootHalfCircle r t ^ 2 = positiveCirclePath 0 (r ^ 2) t := by
  change circleMap 0 r (Real.pi * (t : ℝ)) ^ 2 = circleMap 0 (r ^ 2) _
  rw [circleMap_zero_pow]
  congr 1
  norm_num
  ring

@[simp] theorem norm_quadraticRootHalfCircle (r : ℝ) (t : I) :
    ‖quadraticRootHalfCircle r t‖ = |r| := norm_circleMap_zero _ _

end
end GaloisForLFunctions.HTGeometry
