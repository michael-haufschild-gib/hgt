import GaloisForLFunctions.HeckeKreinToeplitz.Index.ClosedFiniteNegativeSignature
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeEigenvectorTransport

/-!
# Nonpositive eigenvectors inside closed invariant subspaces

A closed nondegenerate subspace has its own complete signed Hilbert model.
Two-sided invariance permits restriction of a form-isometry to this model.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Restrict a continuous linear equivalence to a subspace invariant in both directions. -/
def restrictEquiv (W : Submodule ℂ (H × E)) (T : (H × E) ≃L[ℂ] (H × E))
    (hf : ∀ v ∈ W, T v ∈ W) (hb : ∀ v ∈ W, T.symm v ∈ W) : W ≃L[ℂ] W where
  toFun v := ⟨T v, hf v v.property⟩
  invFun v := ⟨T.symm v, hb v v.property⟩
  left_inv v := Subtype.ext (T.symm_apply_apply v)
  right_inv v := Subtype.ext (T.apply_symm_apply v)
  map_add' u v := Subtype.ext (map_add T (u : H × E) (v : H × E))
  map_smul' a v := Subtype.ext (map_smul T a (v : H × E))
  continuous_toFun := (T.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (T.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- Every closed nondegenerate invariant subspace containing a nonpositive direction
contains a nonpositive eigenvector of the restricted form-isometry. -/
theorem exists_nonpositive_eigenvector_closed_subspace [CompleteSpace H] [FiniteDimensional ℂ E]
    (W : Submodule ℂ (H × E)) (hW : IsClosed (W : Set (H × E)))
    (hnd : restrictedRadical W = ⊥)
    (hn : ∃ v ∈ W, v ≠ 0 ∧ (pairing v v).re ≤ 0)
    (T : (H × E) ≃L[ℂ] (H × E)) (hT : ∀ v w, pairing (T v) (T w) = pairing v w)
    (hf : ∀ v ∈ W, T v ∈ W) (hb : ∀ v ∈ W, T.symm v ∈ W) :
    ∃ (w : H × E) (a : ℂ), w ∈ W ∧ w ≠ 0 ∧ a ≠ 0 ∧
      (pairing w w).re ≤ 0 ∧ T w = a • w := by
  letI : CompleteSpace (positiveKernel W) := (isClosed_positiveKernel W hW).completeSpace_coe
  obtain ⟨n, d, hd, e, he⟩ := exists_closed_signed_splitting W hW hnd
  let T₀ := restrictEquiv W T hf hb
  let S := (e.symm.trans T₀).trans e
  have hS : ∀ v w, pairing (S v) (S w) = pairing v w := by
    intro v w
    change pairing (e (T₀ (e.symm v))) (e (T₀ (e.symm w))) = _
    rw [he]
    change pairing (T (e.symm v)) (T (e.symm w)) = _
    rw [hT]
    simpa only [e.apply_symm_apply] using (he (e.symm v) (e.symm w)).symm
  obtain ⟨v, hvW, hv, hq⟩ := hn
  let v₀ : W := ⟨v, hvW⟩
  have hv₀ : e v₀ ≠ 0 := by
    intro h
    have hz : v₀ = 0 := e.injective (h.trans (map_zero e).symm)
    exact hv (congrArg Subtype.val hz)
  have hvq : (pairing (e v₀) (e v₀)).re ≤ 0 := by rw [he]; exact hq
  have hsnd : (e v₀).2 ≠ 0 := fun h => hv₀ (eq_zero_of_nonpositive_snd_eq_zero hvq h)
  letI : Nontrivial (FiniteSignature.NegativeSpace d hd) := ⟨⟨(e v₀).2, 0, hsnd⟩⟩
  obtain ⟨w, a, hw, ha, hwq, hwe⟩ := exists_nonpositive_eigenvector_finite_negative S hS
  have hw₀ : e.symm w ≠ 0 := by
    intro h
    exact hw (e.symm.injective (h.trans (map_zero e.symm).symm))
  have hTe : T₀ (e.symm w) = a • e.symm w := by
    apply e.injective
    rw [map_smul, e.apply_symm_apply]
    exact hwe
  refine ⟨(e.symm w : H × E), a, (e.symm w).property,
    (fun h => hw₀ (Subtype.ext h)), ha, ?_, congrArg Subtype.val hTe⟩
  have hh := he (e.symm w) (e.symm w)
  rw [e.apply_symm_apply] at hh
  rw [← hh]
  exact hwq

#print axioms exists_nonpositive_eigenvector_closed_subspace

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
