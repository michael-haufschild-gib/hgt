import GaloisForLFunctions.HTGeometry.LeafExtensionSpectrumRealRelationEscape

/-!
# The escape property in canonical submodule coordinates

The escape property is stated for a set of matrices; the extremality theorems consume it for the
canonical real-affine coordinate presentation of a finite-dimensional real Hermitian matrix space,
on the index type `Fin D`.  Two transports bridge the gap: relabelling the carrier by an
equivalence, and passing from a submodule to its canonical generator family.

## Main results

* `matrixCharpolyRelation_reindex` — characteristic roots are unchanged by relabelling.
* `SpectrumEscapesAffineRelations.reindex` — so is the escape property.
* `SpectrumEscapesAffineRelations.ofSubmodule` — the escape property in canonical coordinates.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem matrixCharpolyRelation_reindex (e : I ≃ J) (M : Matrix I I ℂ) (z : ℂ) :
    matrixCharpolyRelation (Matrix.reindex e e M, z) = matrixCharpolyRelation (M, z) := by
  classical
  have hscal :
      (Matrix.scalar J z : Matrix J J ℂ) = (Matrix.scalar I z : Matrix I I ℂ).submatrix e.symm e.symm := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [Matrix.scalar_apply]
    · have : e.symm a ≠ e.symm b := fun h => hab (e.symm.injective h)
      simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ this]
  show (Matrix.scalar J z - Matrix.reindex e e M).det = (Matrix.scalar I z - M).det
  rw [hscal]
  rw [show (Matrix.reindex e e M) = M.submatrix e.symm e.symm from rfl]
  rw [show ((Matrix.scalar I) z).submatrix ⇑e.symm ⇑e.symm - M.submatrix ⇑e.symm ⇑e.symm
      = ((Matrix.scalar I) z - M).submatrix ⇑e.symm ⇑e.symm from rfl]
  exact Matrix.det_submatrix_equiv_self e.symm _

/-- **Relabelling the carrier preserves the escape property.** -/
theorem SpectrumEscapesAffineRelations.reindex (e : I ≃ J) {S : Set (Matrix I I ℂ)}
    (hS : SpectrumEscapesAffineRelations S) {T : Set (Matrix J J ℂ)}
    (hT : ∀ M ∈ S, Matrix.reindex e e M ∈ T) :
    SpectrumEscapesAffineRelations T := by
  classical
  intro c hbalanced hc target
  have hbalanced' : ∑ i, c (e i) = 0 := by
    rw [← hbalanced]
    exact Fintype.sum_equiv e _ _ fun i => rfl
  have hc' : (fun i => c (e i)) ≠ 0 := by
    intro h
    refine hc (funext fun j => ?_)
    have := congrFun h (e.symm j)
    simpa using this
  obtain ⟨M, hMS, E, hEinj, hEroot, hEesc⟩ := hS (fun i => c (e i)) hbalanced' hc' target
  refine ⟨Matrix.reindex e e M, hT M hMS, fun j => E (e.symm j),
    hEinj.comp e.symm.injective, ?_, ?_⟩
  · intro j
    rw [matrixCharpolyRelation_reindex]
    exact hEroot (e.symm j)
  · intro π hzero
    refine hEesc ((e.trans π).trans e.symm) ?_
    rw [← hzero]
    refine (Fintype.sum_equiv e.symm _ _ fun j => ?_).symm
    simp

/-- **The escape property in canonical submodule coordinates.** -/
theorem SpectrumEscapesAffineRelations.ofSubmodule {L : Submodule ℝ (Matrix I I ℂ)}
    (hL : SpectrumEscapesAffineRelations (↑L : Set (Matrix I I ℂ))) :
    SpectrumEscapesAffineRelations
      (Set.range (realAffineMatrix 0 (realMatrixSubmoduleGenerator L))) := by
  refine hL.mono ?_
  intro H hH
  obtain ⟨p, hp⟩ := exists_realAffineMatrix_eq_of_mem_submodule L H hH
  exact ⟨p, hp⟩

end

end GaloisForLFunctions.HTGeometry
