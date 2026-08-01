import GaloisForLFunctions.HTGeometry.AutPermutesRoots

/-!
# Root enumerations transport along an isomorphism

An isomorphism over the base matches the root sets of a polynomial with base-field coefficients, so
an enumeration of the roots on one side pulls back to an enumeration on the other, and a surjective
action on one side gives a surjective action on the other.

This carries the root data computed in a convenient model over to whatever field a later
construction produces.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F E E' : Type*} [Field F] [Field E] [Field E'] [Algebra F E] [Algebra F E']

theorem mem_rootSet_algEquiv_iff (φ : E ≃ₐ[F] E') {p : Polynomial F} (hp : p ≠ 0) {x : E} :
    φ x ∈ p.rootSet E' ↔ x ∈ p.rootSet E := by
  have hneE : p.map (algebraMap F E) ≠ 0 := fun hcon =>
    hp ((Polynomial.map_eq_zero_iff (algebraMap F E).injective).1 hcon)
  have hneE' : p.map (algebraMap F E') ≠ 0 := fun hcon =>
    hp ((Polynomial.map_eq_zero_iff (algebraMap F E').injective).1 hcon)
  rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet']
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hneE, ?_⟩
    have hcomp : Polynomial.aeval (φ.toAlgHom x) p = φ.toAlgHom (Polynomial.aeval x p) :=
      Polynomial.aeval_algHom_apply _ _ _
    have h0 : φ (Polynomial.aeval x p) = 0 := hcomp ▸ h
    exact φ.injective (by rw [h0, map_zero])
  · rintro ⟨-, h⟩
    refine ⟨hneE', ?_⟩
    have hcomp : Polynomial.aeval (φ.toAlgHom x) p = φ.toAlgHom (Polynomial.aeval x p) :=
      Polynomial.aeval_algHom_apply _ _ _
    have h0 : Polynomial.aeval (φ.toAlgHom x) p = 0 := by rw [hcomp, h, map_zero]
    exact h0

/-- **An enumeration of the roots transports along an isomorphism.** -/
theorem rootEnumeration_algEquiv (φ : E ≃ₐ[F] E') {p : Polynomial F} (hp : p ≠ 0) {d : ℕ}
    (v : Fin d → E') (hvinj : Function.Injective v)
    (hrange : ∀ x : E', x ∈ p.rootSet E' ↔ ∃ i, v i = x) :
    Function.Injective (fun i => φ.symm (v i)) ∧
      (∀ x : E, x ∈ p.rootSet E ↔ ∃ i, φ.symm (v i) = x) := by
  refine ⟨fun i j hij => hvinj (φ.symm.injective hij), fun x => ?_⟩
  rw [← mem_rootSet_algEquiv_iff φ hp, hrange (φ x)]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [hi, AlgEquiv.symm_apply_apply]⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← hi, AlgEquiv.apply_symm_apply]⟩

/-- **A surjective action on the roots transports along an isomorphism.** -/
theorem rootAction_surjective_algEquiv (φ : E ≃ₐ[F] E') {d : ℕ} (v : Fin d → E')
    (hsurj : ∀ e : Equiv.Perm (Fin d), ∃ σ : E' ≃ₐ[F] E', ∀ i, σ (v i) = v (e i)) :
    ∀ e : Equiv.Perm (Fin d), ∃ τ : E ≃ₐ[F] E, ∀ i, τ (φ.symm (v i)) = φ.symm (v (e i)) := by
  intro e
  obtain ⟨σ, hσ⟩ := hsurj e
  refine ⟨(φ.trans σ).trans φ.symm, fun i => ?_⟩
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  rw [hσ i]

end GaloisForLFunctions.HTGeometry
