import GaloisForLFunctions.HTGeometry.AffineSpectrumRelationEscape
import GaloisForLFunctions.HTGeometry.HypergraphProjectiveSpectralFactorization
import GaloisForLFunctions.HTGeometry.ShellCoeffScaling

/-!
# Homogeneous spectral escape implies affine escape for a linear family

A linear Hamiltonian family is closed under real rescaling.  Once a nonzero balanced spectral
character misses zero under every labelling, scaling the witness lets it miss any prescribed
affine level: each of the finitely many labellings forbids only one scale.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Linear-family affine escape.**  A homogeneous linear Hamiltonian family that escapes every
balanced real relation also escapes every prescribed affine level. -/
theorem SpectrumEscapesRealRelations.linearFamily_toAffine
    {N D : ℕ}
    (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (hS : SpectrumEscapesRealRelations
      (Set.range (spectralEnsembleMatrix P))) :
    SpectrumEscapesAffineRelations
      (Set.range (spectralEnsembleMatrix P)) := by
  classical
  intro c hbalanced hc target
  obtain ⟨H, ⟨θ, hθ⟩, E, hEinj, hEroot, hEescape⟩ :=
    hS c hbalanced hc
  let action : Equiv.Perm (Fin D) → ℝ := fun σ ↦ ∑ i, c i * E (σ i)
  let forbidden : Set ℝ :=
    Set.range (fun σ : Equiv.Perm (Fin D) ↦ target / action σ) ∪ {0}
  have hforbidden : forbidden.Finite :=
    Set.Finite.union (Set.finite_range _) (Set.finite_singleton 0)
  obtain ⟨t, ht⟩ := hforbidden.exists_notMem
  have ht0 : t ≠ 0 := by
    intro htzero
    apply ht
    exact Set.mem_union_right _ (by simp [htzero])
  refine ⟨t • H, ?_, fun i ↦ t * E i, ?_, ?_, ?_⟩
  · refine ⟨fun a ↦ t * θ a, ?_⟩
    rw [spectralEnsembleMatrix_smul, hθ]
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  · intro i j hij
    exact hEinj (mul_left_cancel₀ ht0 hij)
  · intro i
    simpa using
      (matrixCharpolyRelation_smul_add_smul_one H t 0 (E i) (hEroot i))
  · intro σ hcontra
    have haction0 : action σ ≠ 0 := hEescape σ
    have hsum : ∑ i, c i * (t * E (σ i)) = t * action σ := by
      simp only [action]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum] at hcontra
    apply ht
    apply Set.mem_union_left
    refine Set.mem_range.mpr ⟨σ, ?_⟩
    exact ((eq_div_iff haction0).2 hcontra).symm

end

end GaloisForLFunctions.HTGeometry
