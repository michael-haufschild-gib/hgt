import GaloisForLFunctions.HTGeometry.LinearPMapBoundedUnitaryTransport

/-!
# Natural squares under unitary transport

Abstract transport lemmas for an unbounded operator `Q`, its natural square `A`, exact square-domain
membership, and the composition identity. Compiling dependent subtype transport once keeps concrete
spectral applications small and stable.
-/

open Set
open scoped LinearPMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem unitaryConjugate_domain_le_of_domain_le (U : E ≃ₗᵢ[ℂ] K)
    {Q A : K →ₗ.[ℂ] K} (hAQ : A.domain ≤ Q.domain) :
    (unitaryConjugateLinearPMap U A).domain ≤
      (unitaryConjugateLinearPMap U Q).domain := by
  intro f hf
  exact hAQ hf

theorem unitaryConjugate_mem_iff_apply_mem
    (U : E ≃ₗᵢ[ℂ] K) {Q A : K →ₗ.[ℂ] K}
    (hmem : ∀ (x : K) (hx : x ∈ Q.domain),
      x ∈ A.domain ↔ Q ⟨x, hx⟩ ∈ Q.domain)
    (f : E) (hf : f ∈ (unitaryConjugateLinearPMap U Q).domain) :
    f ∈ (unitaryConjugateLinearPMap U A).domain ↔
      unitaryConjugateLinearPMap U Q ⟨f, hf⟩ ∈
        (unitaryConjugateLinearPMap U Q).domain := by
  let fQ : Q.domain := unitaryConjugateDomainMap U Q ⟨f, hf⟩
  change U f ∈ A.domain ↔
    U (unitaryConjugateLinearPMap U Q ⟨f, hf⟩) ∈ Q.domain
  rw [unitaryConjugateLinearPMap_apply, LinearIsometryEquiv.apply_symm_apply]
  exact hmem (U f) fQ.property

theorem unitaryConjugate_square_apply
    (U : E ≃ₗᵢ[ℂ] K) {Q A : K →ₗ.[ℂ] K}
    (haction : ∀ (x : A.domain) (hx : (x : K) ∈ Q.domain)
      (hQ : Q ⟨(x : K), hx⟩ ∈ Q.domain),
      Q ⟨Q ⟨(x : K), hx⟩, hQ⟩ = A x)
    (f : (unitaryConjugateLinearPMap U A).domain)
    (hf : (f : E) ∈ (unitaryConjugateLinearPMap U Q).domain)
    (hQ : unitaryConjugateLinearPMap U Q ⟨(f : E), hf⟩ ∈
      (unitaryConjugateLinearPMap U Q).domain) :
    unitaryConjugateLinearPMap U Q
        ⟨unitaryConjugateLinearPMap U Q ⟨(f : E), hf⟩, hQ⟩ =
      unitaryConjugateLinearPMap U A f := by
  let fA : A.domain := unitaryConjugateDomainMap U A f
  let fQ : Q.domain := unitaryConjugateDomainMap U Q ⟨(f : E), hf⟩
  have hfval : (fA : K) = (fQ : K) := rfl
  have hQK : Q fQ ∈ Q.domain := by
    change U (unitaryConjugateLinearPMap U Q ⟨(f : E), hf⟩) ∈ Q.domain at hQ
    rw [unitaryConjugateLinearPMap_apply, LinearIsometryEquiv.apply_symm_apply] at hQ
    exact hQ
  let qfE : (unitaryConjugateLinearPMap U Q).domain :=
    ⟨unitaryConjugateLinearPMap U Q ⟨(f : E), hf⟩, hQ⟩
  let qfQ : Q.domain := unitaryConjugateDomainMap U Q qfE
  have hqfQval : (qfQ : K) = Q fQ := by
    change U (unitaryConjugateLinearPMap U Q ⟨(f : E), hf⟩) = Q fQ
    rw [unitaryConjugateLinearPMap_apply, LinearIsometryEquiv.apply_symm_apply]
    rfl
  apply U.injective
  calc
    U (unitaryConjugateLinearPMap U Q qfE) = Q qfQ := by
      rw [unitaryConjugateLinearPMap_apply, LinearIsometryEquiv.apply_symm_apply]
    _ = Q ⟨Q fQ, hQK⟩ := by
      congr 2
      exact Subtype.ext hqfQval
    _ = A fA := by
      have hxA : (fA : K) ∈ Q.domain := by
        rw [hfval]
        exact fQ.property
      have hinput : (⟨(fA : K), hxA⟩ : Q.domain) = fQ := Subtype.ext hfval
      have hQKA : Q ⟨(fA : K), hxA⟩ ∈ Q.domain := by
        rw [hinput]
        exact hQK
      have ha := haction fA hxA hQKA
      let qinA : Q.domain := ⟨Q ⟨(fA : K), hxA⟩, hQKA⟩
      let qinF : Q.domain := ⟨Q fQ, hQK⟩
      have hqin : qinA = qinF := by
        apply Subtype.ext
        exact congrArg Q hinput
      calc
        Q qinF = Q qinA := congrArg Q hqin.symm
        _ = A fA := ha
    _ = U (unitaryConjugateLinearPMap U A f) := by
      rw [unitaryConjugateLinearPMap_apply, LinearIsometryEquiv.apply_symm_apply]

end

end GaloisForLFunctions.HTGeometry

