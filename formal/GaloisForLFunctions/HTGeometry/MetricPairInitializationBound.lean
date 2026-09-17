import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith

/-!
# Metric pair initialization bounds

The four-point triangle inequality bounds the valuation defect attached to each quadratic matrix
entry in the k-server initialization. Summing gives the determinant-term lower bound used in
Lemma 5.2.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

variable {X : Type*} [PseudoMetricSpace X]

/-- Four-point transport defect is bounded below by the negative source-pair distance. -/
theorem neg_dist_le_pairTransportDefect (s₁ s₂ x y : X) :
    -dist s₁ s₂ ≤ dist s₁ x + dist s₂ y - dist x y := by
  have h := dist_triangle4 x s₁ s₂ y
  rw [dist_comm x s₁] at h
  linarith

/-- Coincident-source specialization: the transport defect is nonnegative. -/
theorem pairTransportDefect_nonneg (s x y : X) :
    0 ≤ dist s x + dist s y - dist x y := by
  simpa using neg_dist_le_pairTransportDefect s s x y

/-- Summed four-point lower bound for an arbitrary finite family. -/
theorem neg_sum_dist_le_sum_pairTransportDefect
    {κ : Type*} [DecidableEq κ] (t : Finset κ)
    (s₁ s₂ x y : κ → X) :
    -(∑ i ∈ t, dist (s₁ i) (s₂ i)) ≤
      ∑ i ∈ t, (dist (s₁ i) (x i) + dist (s₂ i) (y i) - dist (x i) (y i)) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun i _ => neg_dist_le_pairTransportDefect _ _ _ _

end GaloisForLFunctions.HTGeometry
