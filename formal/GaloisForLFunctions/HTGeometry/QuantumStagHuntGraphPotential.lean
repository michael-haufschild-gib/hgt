import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Data.Real.Basic

/-!
# Graph accumulation of the quantum Stag Hunt field

Equation (31) of arXiv:2609.02957 follows from an incidence-matrix identity: summing
one field contribution at every endpoint of every edge gives the degree-weighted vertex
field. A concrete four-regular specialization proves the paper's factor `z = 4` without
regularity hypotheses.
-/

set_option autoImplicit false
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Sum of one spin-field contribution at each incident edge endpoint. -/
def graphEndpointField
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (spin : V → ℝ) : ℝ :=
  ∑ e : Sym2 V, ∑ v : V, G.incMatrix ℝ v e * spin v

/-- Endpoint accumulation equals the degree-weighted vertex field on every finite graph. -/
theorem graphEndpointField_eq_degreeWeighted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (spin : V → ℝ) :
    graphEndpointField G spin = ∑ v : V, (G.degree v : ℝ) * spin v := by
  unfold graphEndpointField
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_mul]
  rw [G.sum_incMatrix_apply]

/-- Exact `z=4` multiplier on a concrete four-regular graph. -/
theorem graphEndpointField_completeGraph_finFive (spin : Fin 5 → ℝ) :
    graphEndpointField (SimpleGraph.completeGraph (Fin 5)) spin = 4 * ∑ v, spin v := by
  rw [graphEndpointField_eq_degreeWeighted]
  simp [SimpleGraph.complete_graph_degree, Finset.mul_sum]

end GaloisForLFunctions.HTGeometry
