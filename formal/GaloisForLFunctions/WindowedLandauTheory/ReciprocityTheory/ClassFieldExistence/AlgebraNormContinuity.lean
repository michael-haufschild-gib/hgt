import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

/-! The algebra norm is continuous in the finite-dimensional module topology. -/

noncomputable section

namespace GlobalTheory.Reciprocity

theorem continuous_algebraNorm (K E : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [CommRing E] [Algebra K E] [FiniteDimensional K E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E] :
    Continuous (Algebra.norm K : E → K) := by
  let b := Module.finBasis K E
  have h : Continuous (Algebra.leftMulMatrix b) :=
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
  have he : (Algebra.norm K : E → K) = fun x => (Algebra.leftMulMatrix b x).det :=
    funext fun x => Algebra.norm_eq_matrix_det b x
  rw [he]
  exact h.matrix_det

end GlobalTheory.Reciprocity
