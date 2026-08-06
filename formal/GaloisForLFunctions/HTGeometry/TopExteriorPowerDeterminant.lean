import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Determinant

/-!
# The top exterior power of an endomorphism is its determinant

For a free module with a finite linearly ordered basis, the functorial action of an endomorphism
on the top exterior power is multiplication by the determinant of that endomorphism.  In
particular the top wedge of a basis is an eigenvector of every endomorphism, and it is scaled by
a unit exactly when the endomorphism is invertible.

This is the linear-algebraic content of the eigenvolume step of the stable-coframe theorem: a
finite-dimensional space of one-forms stable under pullback has a top wedge that pullback scales
by the determinant of its transition matrix, so the divisor of the top wedge is unchanged.

mathlib has the exterior-power basis and `LinearMap.det` but not the identification between them
in top degree; that identification is proved here.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset Set Module exteriorPower
open scoped Matrix

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Fintype ι] [LinearOrder ι]

/-- The full index set, as a combination of maximal cardinality. -/
def topCombination (ι : Type*) [Fintype ι] :
    Set.powersetCard ι (Fintype.card ι) :=
  ⟨Finset.univ, by simp⟩

instance uniqueTopCombination : Unique (Set.powersetCard ι (Fintype.card ι)) where
  default := topCombination ι
  uniq s := Subtype.ext (Finset.eq_univ_of_card _ (Set.powersetCard.card_eq s))

/-- The increasing enumeration of the full index set is a bijection from `Fin (card ι)`. -/
theorem topCombination_enum_surjective :
    Function.Surjective
      (Set.powersetCard.ofFinEmbEquiv.symm (default : Set.powersetCard ι (Fintype.card ι))) := by
  intro i
  have hmem : i ∈ Set.range
      (Set.powersetCard.ofFinEmbEquiv.symm (default : Set.powersetCard ι (Fintype.card ι))) := by
    rw [Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
    show i ∈ (Finset.univ : Finset ι)
    exact Finset.mem_univ i
  exact hmem

/-- Bijection from `Fin (card ι)` to `ι` given by the increasing enumeration. -/
noncomputable def topEnumEquiv : Fin (Fintype.card ι) ≃ ι :=
  Equiv.ofBijective
    (Set.powersetCard.ofFinEmbEquiv.symm (default : Set.powersetCard ι (Fintype.card ι)))
    ⟨(Set.powersetCard.ofFinEmbEquiv.symm
      (default : Set.powersetCard ι (Fintype.card ι))).injective,
      topCombination_enum_surjective⟩

@[simp] theorem topEnumEquiv_apply (j : Fin (Fintype.card ι)) :
    (topEnumEquiv (ι := ι)) j =
      Set.powersetCard.ofFinEmbEquiv.symm
        (default : Set.powersetCard ι (Fintype.card ι)) j :=
  rfl

/-- The coordinate matrix of an endomorphism, read along the increasing enumeration of the full
index set, has the determinant of that endomorphism. -/
theorem det_coord_matrix (b : Basis ι R M) (f : M →ₗ[R] M) :
    (Matrix.of fun i j : Fin (Fintype.card ι) =>
      b.coord (topEnumEquiv (ι := ι) j) (f (b (topEnumEquiv (ι := ι) i)))).det =
      LinearMap.det f := by
  classical
  have hsub :
      (Matrix.of fun i j : Fin (Fintype.card ι) =>
        b.coord (topEnumEquiv (ι := ι) j) (f (b (topEnumEquiv (ι := ι) i)))) =
      ((LinearMap.toMatrix b b f)ᵀ).submatrix
        (topEnumEquiv (ι := ι)) (topEnumEquiv (ι := ι)) := by
    ext i j
    simp [LinearMap.toMatrix_apply, Basis.coord_apply]
  rw [hsub, Matrix.det_submatrix_equiv_self, Matrix.det_transpose,
    LinearMap.det_toMatrix]

/-- **The top exterior power of an endomorphism is multiplication by its determinant.** -/
theorem exteriorPower_map_card_eq_det_smul (b : Basis ι R M) (f : M →ₗ[R] M) :
    exteriorPower.map (Fintype.card ι) f =
      LinearMap.det f • (LinearMap.id : ⋀[R]^(Fintype.card ι) M →ₗ[R] _) := by
  classical
  refine Basis.ext (b.exteriorPower (Fintype.card ι)) fun s => ?_
  have hs : s = default := Subsingleton.elim _ _
  subst hs
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family]
  apply (b.exteriorPower (Fintype.card ι)).repr.injective
  ext
  rw [exteriorPower.basis_repr_apply]
  show _ = (Basis.repr (b.exteriorPower (Fintype.card ι))
    (LinearMap.det f • ιMulti_family R (Fintype.card ι) b default)) default
  rw [map_smul, Finsupp.smul_apply, exteriorPower.basis_repr_self, smul_eq_mul, mul_one,
    ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti]
  exact det_coord_matrix b f

/-- The top wedge of a basis is an eigenvector of every endomorphism, with eigenvalue the
determinant. -/
theorem exteriorPower_map_card_apply (b : Basis ι R M) (f : M →ₗ[R] M)
    (x : ⋀[R]^(Fintype.card ι) M) :
    exteriorPower.map (Fintype.card ι) f x = LinearMap.det f • x := by
  rw [exteriorPower_map_card_eq_det_smul b f]
  rfl

omit [Fintype ι] [LinearOrder ι] in
/-- The determinant of a linear automorphism is a unit. -/
theorem isUnit_det_linearEquiv (f : M ≃ₗ[R] M) :
    IsUnit (LinearMap.det (f : M →ₗ[R] M)) := by
  refine IsUnit.of_mul_eq_one (LinearMap.det (f.symm : M →ₗ[R] M)) ?_
  rw [← LinearMap.det_comp]
  have hcomp : (f : M →ₗ[R] M) ∘ₗ (f.symm : M →ₗ[R] M) = LinearMap.id := by
    ext x
    simp
  rw [hcomp, LinearMap.det_id]

/-- **Eigenvolume law.**  Pullback along an automorphism of a finite-rank space scales the top
wedge by a unit, so the divisor of the top wedge is unchanged. -/
theorem exteriorPower_map_card_eq_unit_smul (b : Basis ι R M) (f : M ≃ₗ[R] M) :
    ∃ u : Rˣ, ∀ x : ⋀[R]^(Fintype.card ι) M,
      exteriorPower.map (Fintype.card ι) (f : M →ₗ[R] M) x = (u : R) • x := by
  obtain ⟨u, hu⟩ := isUnit_det_linearEquiv f
  exact ⟨u, fun x => by rw [exteriorPower_map_card_apply b, hu]⟩

end GaloisForLFunctions.HTGeometry
