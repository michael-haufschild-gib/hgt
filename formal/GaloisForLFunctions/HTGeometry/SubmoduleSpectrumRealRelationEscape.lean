import GaloisForLFunctions.HTGeometry.SubmoduleSpectrumRelationEscape
import GaloisForLFunctions.HTGeometry.SpectrumRealRelationEscape

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Relabelling the carrier preserves homogeneous real-relation escape. -/
theorem SpectrumEscapesRealRelations.reindex (e : I ≃ J)
    {S : Set (Matrix I I ℂ)} (hS : SpectrumEscapesRealRelations S)
    {T : Set (Matrix J J ℂ)}
    (hT : ∀ M ∈ S, Matrix.reindex e e M ∈ T) :
    SpectrumEscapesRealRelations T := by
  classical
  intro c hbalanced hc
  have hbalanced' : ∑ i, c (e i) = 0 := by
    rw [← hbalanced]
    exact Fintype.sum_equiv e _ _ fun i => rfl
  have hc' : (fun i => c (e i)) ≠ 0 := by
    intro h
    refine hc (funext fun j => ?_)
    have := congrFun h (e.symm j)
    simpa using this
  obtain ⟨M, hMS, E, hEinj, hEroot, hEesc⟩ := hS
    (fun i => c (e i)) hbalanced' hc'
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

/-- Canonical generators of a real Hermitian submodule retain homogeneous
real-relation escape. -/
theorem SpectrumEscapesRealRelations.ofSubmodule
    {L : Submodule ℝ (Matrix I I ℂ)}
    (hL : SpectrumEscapesRealRelations (↑L : Set (Matrix I I ℂ))) :
    SpectrumEscapesRealRelations
      (Set.range (realAffineMatrix 0 (realMatrixSubmoduleGenerator L))) := by
  refine hL.mono ?_
  intro H hH
  obtain ⟨p, hp⟩ := exists_realAffineMatrix_eq_of_mem_submodule L H hH
  exact ⟨p, hp⟩

end


end GaloisForLFunctions.HTGeometry
