import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# Closedness and local finiteness of separated configurations

A positive lower bound for distances between distinct points makes a set
closed. A finite metric net in a compact set then contains every separated
point, proving finiteness without a counting or volume computation.
-/

namespace GaloisForLFunctions.HilbertMetric

open Set Metric

variable {X : Type*} [MetricSpace X] {S K : Set X} {δ : ℝ}

/-- A positively separated set contains all its accumulation points. -/
theorem isClosed_of_dist_separated (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) : IsClosed S := by
  have hcl : closure S ⊆ S := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx δ hδ
    let A : Set X := {z | z = y ∨ δ ≤ dist z y}
    have hA : IsClosed A := (isClosed_eq continuous_id continuous_const).union
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
    have hSA : S ⊆ A := by
      intro z hz
      by_cases he : z = y
      · exact Or.inl he
      · exact Or.inr (hsep z hz y hy he)
    rcases closure_minimal hSA hA hx with he | he
    · exact he.symm ▸ hy
    · exact (not_le_of_gt hxy he).elim
  have heq : closure S = S := Subset.antisymm hcl subset_closure
  rw [← heq]
  exact isClosed_closure

/-- Inside a compact set, a positive separation scale forces finiteness. -/
theorem finite_of_dist_separated_of_subset_compact (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y)
    (hK : IsCompact K) (hSK : S ⊆ K) : S.Finite := by
  obtain ⟨t, htS, ht, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded (hK.totallyBounded.subset hSK) δ hδ
  apply ht.subset
  intro x hx
  obtain ⟨y, hy⟩ := mem_iUnion.mp (hcover hx)
  obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
  have heq : x = y := by
    by_contra hne
    exact (not_le_of_gt (Metric.mem_ball.mp hxy)) (hsep x hx y (htS hyt) hne)
  exact heq.symm ▸ hyt

end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.isClosed_of_dist_separated
#print axioms GaloisForLFunctions.HilbertMetric.finite_of_dist_separated_of_subset_compact
