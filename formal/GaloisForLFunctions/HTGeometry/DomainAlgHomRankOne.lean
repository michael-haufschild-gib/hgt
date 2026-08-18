import GaloisForLFunctions.HTGeometry.MonicRelationNonzeroConstant
import GaloisForLFunctions.HTGeometry.AlgebraCharpoly

/-!
# A domain finite free over a domain with a section has rank one

If `B` is a domain, finite free of rank `n` over a domain `A`, and there is an `A`-algebra map
`B → A`, then `n = 1`.  The map is surjective because it fixes the base, and injective because a
nonzero kernel element satisfies a monic relation with nonzero constant term (`IsDomain B` lets one
cancel the element out of the relation) which the map would send to that nonzero constant.

This is the last step of every simple-connectedness statement in this lane, isolated so that both
the complex and the general form can use it.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- **A domain finite free over a domain admitting a section has rank one.** -/
theorem rank_eq_one_of_algHom {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Free A B] [Module.Finite A B] {n : ℕ}
    (e : Module.Basis (Fin n) A B) (ψ : B →ₐ[A] A) : n = 1 := by
  classical
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    by_contra hkne
    obtain ⟨r, hrm, hrz, hr0⟩ := exists_monic_coeff_zero_ne_zero (A := A) hkne
      (algCharpoly A k).natDegree (algCharpoly A k) (algCharpoly_monic A k) rfl
      (aeval_algCharpoly A k)
    apply hr0
    have h1 : ψ (Polynomial.aeval k r) = Polynomial.aeval (ψ k) r :=
      (Polynomial.aeval_algHom_apply ψ k r).symm
    rw [hrz, map_zero, hk] at h1
    have h2 : Polynomial.aeval (0 : A) r = r.coeff 0 := by
      simp [Polynomial.coeff_zero_eq_eval_zero]
    rw [h2] at h1
    exact h1.symm
  have hsurj : Function.Surjective ψ := fun a => ⟨algebraMap A B a, ψ.commutes a⟩
  have hbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  let φ : B ≃ₗ[A] A :=
    { Equiv.ofBijective ψ hbij with
      map_add' := map_add _
      map_smul' := fun c x => by simp [Equiv.ofBijective, Algebra.smul_def] }
  have h1 : Module.finrank A B = n := by
    rw [Module.finrank_eq_card_basis e]; simp
  have h2 : Module.finrank A B = 1 := by
    rw [φ.finrank_eq, Module.finrank_self]
  omega

end

end GaloisForLFunctions.HTGeometry
