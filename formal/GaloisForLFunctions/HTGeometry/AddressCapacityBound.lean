import GaloisForLFunctions.HTGeometry.CommutatorOperatorBound

/-!
# The finite-order address capacity

A finite sum of subspaces has dimension at most the sum of the dimensions, and no linear map — in
particular no orthogonal projection and no quotient by the scalars — can increase it.  So an address
space assembled from the first `p` homogeneous Lie layers has dimension at most the sum of the layer
dimensions, whatever the layers are.

Each layer is spanned by evaluated words with `k` leaves in a space of dimension `m`, so its
dimension is at most `m^k`, and the capacity bound is the geometric sum.
-/

open Finset Module

namespace GaloisForLFunctions.HTGeometry

section Capacity

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- A finite supremum of subspaces has dimension at most the sum of the dimensions. -/
theorem finrank_biSup_le (S : ℕ → Submodule ℝ V) [FiniteDimensional ℝ V] :
    ∀ p : ℕ, finrank ℝ ↥((Finset.range p).sup S) ≤ ∑ k ∈ Finset.range p, finrank ℝ ↥(S k) := by
  intro p
  induction p with
  | zero =>
    rw [Finset.range_zero, Finset.sup_empty, Finset.sum_empty]
    simp [finrank_bot]
  | succ p ih =>
    have hsplit : (Finset.range (p + 1)).sup S = S p ⊔ (Finset.range p).sup S := by
      rw [Finset.range_add_one, Finset.sup_insert]
    rw [hsplit, Finset.sum_range_succ]
    refine le_trans (Submodule.finrank_add_le_finrank_add_finrank _ _) ?_
    omega

/-- **`(39)`: the address capacity bound.**  The image of the first `p` layers under any linear map
has dimension at most the sum of the layer bounds. -/
theorem finrank_map_biSup_le (S : ℕ → Submodule ℝ V) [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] W)
    (p : ℕ) {b : ℕ → ℕ} (hb : ∀ k, finrank ℝ ↥(S k) ≤ b k) :
    finrank ℝ ↥(((Finset.range p).sup S).map f) ≤ ∑ k ∈ Finset.range p, b k := by
  refine le_trans (Submodule.finrank_map_le f _) ?_
  refine le_trans (finrank_biSup_le S p) ?_
  exact Finset.sum_le_sum fun k _ => hb k

/-- The geometric form of the capacity bound. -/
theorem finrank_map_biSup_le_geom (S : ℕ → Submodule ℝ V) [FiniteDimensional ℝ V]
    (f : V →ₗ[ℝ] W) (p m : ℕ) (hm : ∀ k, finrank ℝ ↥(S k) ≤ m ^ (k + 1)) :
    finrank ℝ ↥(((Finset.range p).sup S).map f) ≤ ∑ k ∈ Finset.range p, m ^ (k + 1) :=
  finrank_map_biSup_le S f p hm

end Capacity

/-! ## The layer bound -/

section Layer

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The span of a finite family has dimension at most the size of the family. -/
theorem finrank_span_range_le {ι : Type*} [Fintype ι] (g : ι → V) :
    finrank ℝ ↥(Submodule.span ℝ (Set.range g)) ≤ Fintype.card ι := by
  have hrange : Submodule.span ℝ (Set.range g)
      = LinearMap.range (Finsupp.linearCombination ℝ g) :=
    (Finsupp.range_linearCombination ℝ).symm
  rw [hrange]
  refine le_trans (LinearMap.finrank_range_le _) ?_
  exact le_of_eq (finrank_finsupp_self ℝ)

/-- **The layer bound.**  A layer spanned by the words indexed by `k`-tuples of basis labels from a
space of dimension `m` has dimension at most `m^k`. -/
theorem finrank_span_le_pow {k m : ℕ} (g : (Fin k → Fin m) → V) :
    finrank ℝ ↥(Submodule.span ℝ (Set.range g)) ≤ m ^ k := by
  refine le_trans (finrank_span_range_le g) ?_
  simp

end Layer


end GaloisForLFunctions.HTGeometry
