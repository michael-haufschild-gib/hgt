import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Alternating rank in arbitrary characteristic

A maximal isotropic subspace of an alternating space is self-orthogonal, even when
the form is degenerate. The orthogonal dimension formula then forces even rank.
No division by two is used, so the result applies to binary matrices.
-/

open Module
open LinearMap (BilinForm)
namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Adjoining a vector orthogonal to an isotropic subspace preserves isotropy for an
alternating form, including in characteristic two. -/
theorem alternating_sup_span_isotropic {B : BilinForm K V} (hB : B.IsAlt)
    {W : Submodule K V} (hW : W ≤ B.orthogonal W) {x : V}
    (hx : x ∈ B.orthogonal W) :
    W ⊔ K ∙ x ≤ B.orthogonal (W ⊔ K ∙ x) := by
  intro z hz t ht
  rcases Submodule.mem_sup.mp hz with ⟨w, hw, u, hu, rfl⟩
  rcases Submodule.mem_span_singleton.mp hu with ⟨a, rfl⟩
  rcases Submodule.mem_sup.mp ht with ⟨v, hv, u, hu, rfl⟩
  rcases Submodule.mem_span_singleton.mp hu with ⟨b, rfl⟩
  have hxw : B x w = 0 := hB.isRefl _ _ (hx w hw)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hW hw v hv, hx v hv, hxw, hB.self_eq_zero x, mul_zero, add_zero]

/-- Every finite-dimensional alternating space has a self-orthogonal subspace.
Choose an isotropic subspace of maximal dimension and adjoin any orthogonal vector. -/
theorem exists_selfOrthogonal_of_isAlt [FiniteDimensional K V]
    {B : BilinForm K V} (hB : B.IsAlt) :
    ∃ W : Submodule K V, B.orthogonal W = W := by
  let D : Set ℕ := {n | ∃ W : Submodule K V, W ≤ B.orthogonal W ∧ finrank K W = n}
  have hD : D.Finite := (Set.finite_Iic (finrank K V)).subset (by
    rintro n ⟨W, _, rfl⟩
    exact Submodule.finrank_le W)
  have hD0 : D.Nonempty := ⟨0, ⊥, bot_le, by simp⟩
  obtain ⟨n, ⟨W, hW, hdim⟩, hn⟩ := Set.exists_max_image D (fun n => n) hD hD0
  refine ⟨W, le_antisymm ?_ hW⟩
  intro x hx
  have hX := alternating_sup_span_isotropic hB hW hx
  have hle : finrank K ↥(W ⊔ K ∙ x) ≤ finrank K W := by
    rw [hdim]
    exact hn _ ⟨_, hX, rfl⟩
  have heq := Submodule.eq_of_le_of_finrank_le
    (show W ≤ W ⊔ K ∙ x from le_sup_left) hle
  rw [heq]
  exact (show K ∙ x ≤ W ⊔ K ∙ x from le_sup_right)
    (Submodule.mem_span_singleton_self x)

/-- Alternating forms have even rank over every field. The radical lies in every
self-orthogonal subspace, and the orthogonal dimension formula gives the parity. -/
theorem even_finrank_range_of_isAlt [FiniteDimensional K V]
    {B : BilinForm K V} (hB : B.IsAlt) : Even (finrank K B.range) := by
  obtain ⟨W, hW⟩ := exists_selfOrthogonal_of_isAlt hB
  have hrad : B.ker ≤ W := by
    rw [← hW]
    intro x hx y hy
    have hxy : B x y = 0 := congrArg (fun f : V →ₗ[K] K => f y) hx
    exact hB.isRefl _ _ hxy
  have hdim := BilinForm.finrank_add_finrank_orthogonal' (B := B) W
  rw [hW, inf_eq_right.mpr hrad] at hdim
  have hrank := LinearMap.finrank_range_add_finrank_ker B
  refine ⟨finrank K W - finrank K B.ker, ?_⟩
  omega

/-- A nondegenerate alternating space has even dimension in every characteristic. -/
theorem even_finrank_of_nondegenerate_alternating [FiniteDimensional K V]
    {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    Even (finrank K V) := by
  have hrank := LinearMap.finrank_range_add_finrank_ker B
  rw [hnd.ker_eq_bot, finrank_bot, add_zero] at hrank
  rw [← hrank]
  exact even_finrank_range_of_isAlt hB

/-- Skew-symmetrizing any bilinear form gives even rank, also in characteristic two. -/
theorem even_finrank_range_sub_flip [FiniteDimensional K V] (B : BilinForm K V) :
    Even (finrank K (B - B.flip).range) := by
  apply even_finrank_range_of_isAlt
  intro x
  change B x x - B x x = 0
  exact sub_self _

end GaloisForLFunctions.HTGeometry.LinearAlgebra
#print axioms GaloisForLFunctions.HTGeometry.LinearAlgebra.exists_selfOrthogonal_of_isAlt
#print axioms GaloisForLFunctions.HTGeometry.LinearAlgebra.even_finrank_range_of_isAlt
#print axioms GaloisForLFunctions.HTGeometry.LinearAlgebra.even_finrank_of_nondegenerate_alternating
#print axioms GaloisForLFunctions.HTGeometry.LinearAlgebra.even_finrank_range_sub_flip
