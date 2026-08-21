import GaloisForLFunctions.HTGeometry.StarShaped

/-!
# Two homotopy-theoretic reductions

A subset of a subspace is the corresponding subset of the ambient space, and a product with the line
is homotopy equivalent to its first factor.  Both are needed to identify the intersection of the two
star-shaped pieces of a punctured space with the punctured space of one dimension lower.
-/

open CategoryTheory

namespace GaloisForLFunctions.HTGeometry

universe v

/-- A subset of a subspace, as a subspace of the ambient space. -/
noncomputable def subsetSubtypeHomeomorph {X : Type v} [TopologicalSpace X] {S : Set X}
    (T : Set X) (hTS : T ⊆ S) : ↥({p : ↥S | (p : X) ∈ T}) ≃ₜ ↥T where
  toFun p := ⟨((p : ↥S) : X), p.2⟩
  invFun q := ⟨⟨(q : X), hTS q.2⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-- The projection of a product with the line is a homotopy equivalence. -/
noncomputable def prodRealHomotopyEquiv (Y : Type v) [TopologicalSpace Y] :
    ContinuousMap.HomotopyEquiv (Y × ℝ) Y where
  toFun := ⟨Prod.fst, continuous_fst⟩
  invFun := ⟨fun y => (y, 0), Continuous.prodMk continuous_id continuous_const⟩
  left_inv := ⟨{
    toFun := fun p => (p.2.1, (p.1 : ℝ) * p.2.2)
    continuous_toFun := by
      refine Continuous.prodMk (continuous_fst.comp continuous_snd) ?_
      exact (continuous_subtype_val.comp continuous_fst).mul (continuous_snd.comp continuous_snd)
    map_zero_left := fun p => by simp
    map_one_left := fun p => by simp }⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl _⟩

end GaloisForLFunctions.HTGeometry
