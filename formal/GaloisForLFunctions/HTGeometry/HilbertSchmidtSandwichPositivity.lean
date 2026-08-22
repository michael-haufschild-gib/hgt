import GaloisForLFunctions.HTGeometry.HilbertSchmidtSandwichBounds

/-!
# Positivity of the Hilbert–Schmidt sandwich form

The quadratic form `Y ↦ ⟨a Y b, Y⟩_HS` is nonnegative whenever `a` and `b` are positive.  Writing
`a = s⋆s` and `b = t t⋆`, the two adjunction identities of the Hilbert–Schmidt inner product,

`⟨A ∘ S, T⟩_HS = ⟨S, A† ∘ T⟩_HS`,   `⟨S ∘ B, T⟩_HS = ⟨S, T ∘ B†⟩_HS`,

collapse the form to a squared Hilbert–Schmidt norm:

`⟨(s⋆s) Y (t t⋆), Y⟩_HS = ⟨s Y t, s Y t⟩_HS = ‖s Y t‖²_HS`.

This is the trace-free replacement for the semigroup-integral positivity argument of
Kim–Mer–Pálfia (arXiv:2607.29142), Lemma 3.11.
-/

open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Left adjunction** for the Hilbert–Schmidt inner product. -/
theorem hsInner_comp_left (A S T : E →L[𝕜] E) :
    hsInner (A ∘L S) T = hsInner S (adjoint A ∘L T) := by
  refine tsum_congr fun i => ?_
  rw [comp_apply, comp_apply, adjoint_inner_right]

/-- **Right adjunction** for the Hilbert–Schmidt inner product. -/
theorem hsInner_comp_right {S T : E →L[𝕜] E} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T)
    (B : E →L[𝕜] E) : hsInner (S ∘L B) T = hsInner S (T ∘L adjoint B) := by
  have hSB : IsHilbertSchmidt (S ∘L B) := hS.comp_right B
  have hTB : IsHilbertSchmidt (T ∘L adjoint B) := hT.comp_right (adjoint B)
  have step1 : hsInner (S ∘L B) T = hsInner (adjoint T) (adjoint (S ∘L B)) :=
    (hsInner_adjoint_adjoint hT hSB).symm
  have step2 : hsInner (adjoint T) (adjoint (S ∘L B))
      = hsInner (adjoint T) (adjoint B ∘L adjoint S) := by rw [adjoint_comp]
  have step3 : hsInner (adjoint T) (adjoint B ∘L adjoint S)
      = hsInner (B ∘L adjoint T) (adjoint S) := by
    have hc : hsInner (adjoint T) (adjoint B ∘L adjoint S)
        = conj (hsInner (adjoint B ∘L adjoint S) (adjoint T)) :=
      hsInner_conj_symm _ _
    rw [hc, hsInner_comp_left, adjoint_adjoint, ← hsInner_conj_symm]
  have step4 : hsInner (B ∘L adjoint T) (adjoint S) = hsInner S (T ∘L adjoint B) := by
    have hrepr : (B ∘L adjoint T) = adjoint (T ∘L adjoint B) := by
      rw [adjoint_comp, adjoint_adjoint]
    rw [hrepr]
    exact hsInner_adjoint_adjoint hTB hS
  rw [step1, step2, step3, step4]

/-- **The Hilbert–Schmidt sandwich form is a squared norm.** -/
theorem hsInner_sandwich_eq {s t Y : E →L[𝕜] E} (hY : IsHilbertSchmidt Y) :
    hsInner ((adjoint s ∘L s) ∘L Y ∘L (t ∘L adjoint t)) Y
      = hsInner (s ∘L Y ∘L t) (s ∘L Y ∘L t) := by
  have hsY : IsHilbertSchmidt (s ∘L Y) := hY.comp_left s
  have hsYt : IsHilbertSchmidt (s ∘L Y ∘L t) := hsY.comp_right t
  have e1 : (adjoint s ∘L s) ∘L Y ∘L (t ∘L adjoint t)
      = adjoint s ∘L ((s ∘L Y ∘L t) ∘L adjoint t) := by
    simp only [comp_assoc]
  rw [e1, hsInner_comp_left, adjoint_adjoint]
  rw [hsInner_comp_right hsYt (hY.comp_left s) (adjoint t), adjoint_adjoint]
  simp only [comp_assoc]

/-- **Nonnegativity of the Hilbert–Schmidt sandwich form.** -/
theorem re_hsInner_sandwich_nonneg {s t Y : E →L[𝕜] E} (hY : IsHilbertSchmidt Y) :
    0 ≤ RCLike.re (hsInner ((adjoint s ∘L s) ∘L Y ∘L (t ∘L adjoint t)) Y) := by
  have hsYt : IsHilbertSchmidt (s ∘L Y ∘L t) := (hY.comp_left s).comp_right t
  rw [hsInner_sandwich_eq hY, hsInner_self_re hsYt]
  exact hsNormSq_nonneg _

/-- The sandwich form equals the squared Hilbert–Schmidt norm of the symmetrised sandwich. -/
theorem re_hsInner_sandwich_eq_hsNormSq {s t Y : E →L[𝕜] E} (hY : IsHilbertSchmidt Y) :
    RCLike.re (hsInner ((adjoint s ∘L s) ∘L Y ∘L (t ∘L adjoint t)) Y)
      = hsNormSq (s ∘L Y ∘L t) := by
  have hsYt : IsHilbertSchmidt (s ∘L Y ∘L t) := (hY.comp_left s).comp_right t
  rw [hsInner_sandwich_eq hY, hsInner_self_re hsYt]

end ContinuousLinearMap
