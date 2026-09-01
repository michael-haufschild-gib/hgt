import GaloisForLFunctions.HTGeometry.MinimalCompleteSystem

/-!
# Strong Markushevich pairs

A biorthogonal pair is strong, or hereditarily complete, when every system obtained by choosing
independently between each primal vector and its dual is complete. This is the mixed-system
criterion for hereditary completeness used by Markus, Burnol, and Baranov--Belov--Borichev.
-/

namespace GaloisForLFunctions.HTGeometry

open Classical
open scoped InnerProductSpace

variable (𝕜 : Type*) {E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Mixed system selected from a primal/dual pair by a set of primal indices. -/
noncomputable def strongMarkushevichMixed
    (u v : ι → E) (s : Set ι) : ι → E :=
  fun i => if i ∈ s then u i else v i

/-- Pair form of a strong Markushevich basis: biorthogonality plus completeness of every mixed
primal/dual system. Taking the full or empty selector includes completeness of both sides. -/
def IsStrongMarkushevichPair (u v : ι → E) : Prop :=
  IsDualSystem 𝕜 u v ∧
    ∀ s : Set ι, IsCompleteSystem 𝕜 (strongMarkushevichMixed u v s)

variable {𝕜}

/-- Pointwise multiplication by nonzero scalars preserves completeness. -/
theorem IsCompleteSystem.smul_of_ne [CompleteSpace E] {u : ι → E}
    (h : IsCompleteSystem 𝕜 u) (a : ι → 𝕜) (ha : ∀ i, a i ≠ 0) :
    IsCompleteSystem 𝕜 (fun i => a i • u i) := by
  rw [isCompleteSystem_iff_forall_inner_eq_zero] at h ⊢
  intro x hx
  apply h
  intro i
  have hi := hx i
  rw [inner_smul_left] at hi
  exact (mul_eq_zero.mp hi).resolve_left (star_ne_zero.mpr (ha i))

theorem IsStrongMarkushevichPair.isDualSystem {u v : ι → E}
    (h : IsStrongMarkushevichPair 𝕜 u v) : IsDualSystem 𝕜 u v :=
  h.1

theorem IsStrongMarkushevichPair.isCompleteSystem_mixed {u v : ι → E}
    (h : IsStrongMarkushevichPair 𝕜 u v) (s : Set ι) :
    IsCompleteSystem 𝕜 (strongMarkushevichMixed u v s) :=
  h.2 s

theorem IsStrongMarkushevichPair.isCompleteSystem_left {u v : ι → E}
    (h : IsStrongMarkushevichPair 𝕜 u v) : IsCompleteSystem 𝕜 u := by
  have hm := h.2 Set.univ
  rw [show strongMarkushevichMixed u v Set.univ = u by
    funext i
    simp [strongMarkushevichMixed]] at hm
  exact hm

theorem IsStrongMarkushevichPair.isCompleteSystem_right {u v : ι → E}
    (h : IsStrongMarkushevichPair 𝕜 u v) : IsCompleteSystem 𝕜 v := by
  have hm := h.2 ∅
  rw [show strongMarkushevichMixed u v ∅ = v by
    funext i
    simp [strongMarkushevichMixed]] at hm
  exact hm

end GaloisForLFunctions.HTGeometry
