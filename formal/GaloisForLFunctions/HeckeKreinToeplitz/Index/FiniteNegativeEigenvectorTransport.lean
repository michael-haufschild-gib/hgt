import GaloisForLFunctions.HeckeKreinToeplitz.Index.NonpositiveFiniteIndexEigenvector

/-!
# Nonpositive eigenvectors with an arbitrary finite negative factor

An orthonormal basis identifies the negative Hilbert factor with a finite
Euclidean space. Transporting the isometry preserves its form and eigenvectors.
-/

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Nontrivial E]

/-- A nontrivial finite negative Hilbert factor forces a nonpositive eigenvector. -/
theorem exists_nonpositive_eigenvector_finite_negative
    (T : (H × E) ≃L[ℂ] (H × E)) (hT : ∀ v w, pairing (T v) (T w) = pairing v w) :
    ∃ (w : H × E) (a : ℂ), w ≠ 0 ∧ a ≠ 0 ∧ (pairing w w).re ≤ 0 ∧ T w = a • w := by
  let b := stdOrthonormalBasis ℂ E
  let e := ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℂ H)
    b.repr.toContinuousLinearEquiv
  have hp (v w : H × E) : pairing (e v) (e w) = pairing v w := by
    change inner ℂ v.1 w.1 - inner ℂ (b.repr v.2) (b.repr w.2) =
      inner ℂ v.1 w.1 - inner ℂ v.2 w.2
    rw [b.repr.inner_map_map]
  let S := (e.symm.trans T).trans e
  have hS : ∀ v w, pairing (S v) (S w) = pairing v w := by
    intro v w
    change pairing (e (T (e.symm v))) (e (T (e.symm w))) = _
    rw [hp, hT]
    simpa only [e.apply_symm_apply] using (hp (e.symm v) (e.symm w)).symm
  have hm : 0 < Module.finrank ℂ E := Module.finrank_pos_iff.mpr inferInstance
  obtain ⟨w, a, hw, ha, hq, he⟩ := exists_nonpositive_eigenvector S hS hm
  refine ⟨e.symm w, a, ?_, ha, ?_, ?_⟩
  · intro hz
    exact hw (e.symm.injective (hz.trans (map_zero e.symm).symm))
  · have hh := hp (e.symm w) (e.symm w)
    rw [e.apply_symm_apply] at hh
    rw [← hh]
    exact hq
  · apply e.injective
    rw [map_smul, e.apply_symm_apply]
    exact he

#print axioms exists_nonpositive_eigenvector_finite_negative

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
