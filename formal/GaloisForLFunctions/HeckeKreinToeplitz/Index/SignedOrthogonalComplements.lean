import GaloisForLFunctions.HeckeKreinToeplitz.Index.RestrictedFiniteNegativeRadical
import GaloisForLFunctions.HeckeKreinToeplitz.Index.MinimalNonpositiveInvariantSubspace

/-!
# Signed orthogonal complements

The signed orthogonal complement is closed and respects invertible
form-isometries. A sign change in the finite negative factor reduces the
double-complement identity to ordinary Hilbert orthogonality.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Orthogonality for the indefinite pairing. -/
def signedOrthogonal (U : Submodule ℂ (H × E)) : Submodule ℂ (H × E) :=
  ⨅ u : U, (pairingLinear (u : H × E)).ker

theorem mem_signedOrthogonal (U : Submodule ℂ (H × E)) (v : H × E) :
    v ∈ signedOrthogonal U ↔ ∀ u ∈ U, pairing u v = 0 := by
  rw [signedOrthogonal, Submodule.mem_iInf]
  exact ⟨fun h u hu => h ⟨u, hu⟩, fun h u => h u u.property⟩

theorem isClosed_signedOrthogonal (U : Submodule ℂ (H × E)) :
    IsClosed (signedOrthogonal U : Set (H × E)) := by
  have heq : (signedOrthogonal U : Set (H × E)) =
      ⋂ u : U, {v | pairing (u : H × E) v = 0} := by
    ext v
    change (v ∈ signedOrthogonal U) ↔ v ∈ ⋂ u : U, {v | pairing (u : H × E) v = 0}
    rw [mem_signedOrthogonal, Set.mem_iInter]
    exact ⟨fun h u => h u u.property, fun h u hu => h ⟨u, hu⟩⟩
  rw [heq]
  apply isClosed_iInter
  intro u
  exact isClosed_eq (continuous_pairing.comp
    (continuous_const.prodMk continuous_id)) continuous_const

theorem le_signedOrthogonal_signedOrthogonal (U : Submodule ℂ (H × E)) :
    U ≤ signedOrthogonal (signedOrthogonal U) := by
  intro u hu
  apply (mem_signedOrthogonal _ _).mpr
  intro v hv
  rw [← pairing_conj_symm, (mem_signedOrthogonal U v).mp hv u hu, map_zero]

/-- Closed subspaces equal their signed double orthogonal complements. -/
theorem signedOrthogonal_signedOrthogonal [CompleteSpace H] [CompleteSpace E]
    (U : Submodule ℂ (H × E)) (hU : IsClosed (U : Set (H × E))) :
    signedOrthogonal (signedOrthogonal U) = U := by
  apply le_antisymm _ (le_signedOrthogonal_signedOrthogonal U)
  intro v hv
  let A := WithLp 2 (H × E)
  let e : A ≃L[ℂ] H × E := WithLp.prodContinuousLinearEquiv 2 ℂ H E
  let K : Submodule ℂ A := U.comap e.toLinearMap
  have hK : IsClosed (K : Set A) := hU.preimage e.continuous
  letI : CompleteSpace K := hK.completeSpace_coe
  have he : e.symm v ∈ Kᗮᗮ := by
    apply (Submodule.mem_orthogonal Kᗮ _).mpr
    intro x hx
    have hx' : (x.fst, -x.snd) ∈ signedOrthogonal U := by
      apply (mem_signedOrthogonal U _).mpr
      intro u hu
      have h := (Submodule.mem_orthogonal K x).mp hx (e.symm u) (by
        change e (e.symm u) ∈ U
        rw [e.apply_symm_apply]
        exact hu)
      change inner ℂ u.1 x.fst + inner ℂ u.2 x.snd = 0 at h
      simpa only [pairing, inner_neg_right, sub_neg_eq_add] using h
    have h := (mem_signedOrthogonal (signedOrthogonal U) v).mp hv _ hx'
    change inner ℂ x.fst v.1 + inner ℂ x.snd v.2 = 0
    simpa only [pairing, inner_neg_left, sub_neg_eq_add] using h
  rw [K.orthogonal_orthogonal] at he
  change e (e.symm v) ∈ U at he
  simpa only [e.apply_symm_apply] using he

/-- Invertible isometries preserving a subspace preserve its signed complement. -/
theorem map_mem_signedOrthogonal (U : Submodule ℂ (H × E))
    (T : (H × E) ≃L[ℂ] (H × E)) (hT : ∀ v w, pairing (T v) (T w) = pairing v w)
    (hb : ∀ u ∈ U, T.symm u ∈ U) {v : H × E} (hv : v ∈ signedOrthogonal U) :
    T v ∈ signedOrthogonal U := by
  apply (mem_signedOrthogonal U _).mpr
  intro u hu
  have h := hT (T.symm u) v
  rw [T.apply_symm_apply] at h
  rw [h]
  exact (mem_signedOrthogonal U v).mp hv _ (hb u hu)

theorem isBiInvariant_signedOrthogonal {ι : Type*}
    (T : ι → (H × E) ≃L[ℂ] (H × E))
    (hT : ∀ i v w, pairing (T i v) (T i w) = pairing v w)
    (U : Submodule ℂ (H × E)) (hU : IsBiInvariant T U) :
    IsBiInvariant T (signedOrthogonal U) := by
  intro i v hv
  constructor
  · exact map_mem_signedOrthogonal U (T i) (hT i) (fun u hu => (hU i u hu).2) hv
  · apply map_mem_signedOrthogonal U (T i).symm _ (fun u hu => (hU i u hu).1) hv
    intro x y
    have h := hT i ((T i).symm x) ((T i).symm y)
    rw [(T i).apply_symm_apply, (T i).apply_symm_apply] at h
    exact h.symm

/-- The radical of a closed subspace's complement lies in the original space. -/
theorem restrictedRadical_signedOrthogonal [CompleteSpace H] [CompleteSpace E]
    (U : Submodule ℂ (H × E)) (hU : IsClosed (U : Set (H × E))) :
    restrictedRadical (signedOrthogonal U) = signedOrthogonal U ⊓ U := by
  change signedOrthogonal U ⊓ signedOrthogonal (signedOrthogonal U) = _
  rw [signedOrthogonal_signedOrthogonal U hU]

#print axioms signedOrthogonal_signedOrthogonal
#print axioms isBiInvariant_signedOrthogonal
#print axioms restrictedRadical_signedOrthogonal

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
