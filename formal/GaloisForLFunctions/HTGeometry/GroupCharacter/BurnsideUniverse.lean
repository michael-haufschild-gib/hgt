import GaloisForLFunctions.HTGeometry.GroupCharacter.Burnside

/-!
# Burnside's theorem in an arbitrary universe

The character-theoretic development is carried out for groups in `Type` because mathlib's
`FDRep.simple_iff_end_is_rank_one` requires the base field and the group to live in the same
universe.  Every finite group is isomorphic to a group in `Type` (Cayley's theorem followed by a
transport of `Equiv.Perm` along a bijection with `Fin n`), so Burnside's theorem transports.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

/-- Transport of a permutation group along an equivalence, as a group isomorphism. -/
def permCongrMulEquiv {α : Type u} {β : Type*} (e : α ≃ β) :
    Equiv.Perm α ≃* Equiv.Perm β where
  toFun σ := (e.symm.trans σ).trans e
  invFun τ := (e.trans τ).trans e.symm
  left_inv σ := by ext x; simp
  right_inv τ := by ext x; simp
  map_mul' σ τ := by ext x; simp

/-- Every finite group is isomorphic to a group living in `Type`. -/
theorem exists_type_zero_model (G : Type u) [Group G] [Finite G] :
    ∃ (H : Type) (_ : Group H) (_ : Finite H), Nonempty (G ≃* H) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  have hinj : Function.Injective
      ((permCongrMulEquiv e).toMonoidHom.comp (MulAction.toPermHom G G)) := by
    intro a b hab
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at hab
    have h1 := (permCongrMulEquiv e).injective hab
    have h2 := congrArg (fun σ : Equiv.Perm G => σ 1) h1
    simpa using h2
  exact ⟨↥((permCongrMulEquiv e).toMonoidHom.comp (MulAction.toPermHom G G)).range,
    inferInstance, inferInstance, ⟨MonoidHom.ofInjective hinj⟩⟩

/-- **Burnside's `p ^ a q ^ b` theorem** for a finite group in any universe. -/
theorem isSolvable_of_card_dvd_two_prime_powers {G : Type u} [Group G] [Finite G]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hdvd : Nat.card G ∣ p ^ a * q ^ b) :
    IsSolvable G := by
  classical
  obtain ⟨H, _, _, ⟨e⟩⟩ := exists_type_zero_model G
  haveI : Fintype H := Fintype.ofFinite H
  haveI : DecidableEq H := Classical.decEq H
  have hcard : Nat.card H = Nat.card G := (Nat.card_congr e.toEquiv).symm
  haveI : IsSolvable H :=
    isSolvable_of_card_dvd_prime_pow_mul_prime_pow hp hq (by rw [hcard]; exact hdvd)
  exact solvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

end GaloisForLFunctions.HTGeometry.GroupCharacter
