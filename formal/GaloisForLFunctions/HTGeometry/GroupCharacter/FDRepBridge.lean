import GaloisForLFunctions.HTGeometry.GroupCharacter.Schur
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Bridge to mathlib's `FDRep` character theory

A minimal `G`-stable subspace of `ℂ[G]` gives a simple object of `FDRep ℂ G` whose character is
`chi`.  This lets the orthogonality relations of `FDRep.char_orthonormal` be applied to the
decomposition produced by `exists_simple_decomposition`.
-/

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra CategoryTheory

variable {G : Type} [Group G] [Fintype G]

/-- The representation of `G` on a `G`-stable subspace of the group algebra. -/
def repOf {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) :
    Representation ℂ G ↥N where
  toFun := rho hN
  map_one' := rho_one hN
  map_mul' g h := rho_mul hN g h

@[simp] theorem repOf_apply {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g : G) :
    repOf hN g = rho hN g := rfl

/-- The object of `FDRep ℂ G` attached to a `G`-stable subspace. -/
noncomputable def fdRepOf {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) :
    FDRep ℂ G := FDRep.of (repOf hN)

@[simp] theorem fdRepOf_ρ {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) :
    (fdRepOf hN).ρ = repOf hN := FDRep.of_ρ' _

theorem character_fdRepOf {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g : G) :
    (fdRepOf hN).character g = chi hN g := by
  rw [FDRep.character, fdRepOf_ρ, repOf_apply]
  rfl

theorem invariants_linHom {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsMinimalGStable N) :
    (Representation.linHom (repOf hN.stable) (repOf hN.stable)).invariants
      = ℂ ∙ (LinearMap.id : ↥N →ₗ[ℂ] ↥N) := by
  apply le_antisymm
  · intro f hf
    rw [Representation.mem_invariants] at hf
    refine Submodule.mem_span_singleton.mpr ?_
    obtain ⟨c, hc⟩ := schur hN f ?_
    · exact ⟨c, by ext v; simpa using (hc v).symm⟩
    · intro g
      refine LinearMap.ext fun v => ?_
      have h := hf g⁻¹
      have h2 := congrArg (fun (φ : ↥N →ₗ[ℂ] ↥N) => φ ((rho hN.stable g) v)) h
      simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply,
        repOf_apply, inv_inv] at h2
      rw [← rho_mul, inv_mul_cancel, rho_one] at h2
      simpa using h2.symm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    rw [SetLike.mem_coe, Representation.mem_invariants]
    intro g
    refine LinearMap.ext fun v => ?_
    simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply,
      repOf_apply, LinearMap.id_coe, id_eq]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
    have : rho hN.stable g ∘ₗ rho hN.stable g⁻¹ = LinearMap.id := by
      rw [← rho_mul, mul_inv_cancel, rho_one]
    sorry

theorem simple_fdRepOf {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsMinimalGStable N) :
    Simple (fdRepOf hN.stable) := by
  haveI : NeZero ((Nat.card G : ℂ)) := ⟨by
    simp [Nat.card_eq_fintype_card, Fintype.card_ne_zero]⟩
  haveI : Nontrivial ↥N := Submodule.nontrivial_iff_ne_bot.mpr hN.ne_bot
  rw [FDRep.simple_iff_end_is_rank_one]
  rw [← LinearEquiv.finrank_eq
    (Representation.linHom.invariantsEquivFDRepHom (fdRepOf hN.stable) (fdRepOf hN.stable))]
  rw [fdRepOf_ρ, invariants_linHom hN]
  exact finrank_span_singleton (by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : ↥N)
    exact hv (by simpa using congrArg (fun (φ : ↥N →ₗ[ℂ] ↥N) => φ v) h))

end GaloisForLFunctions.HTGeometry.GroupCharacter
