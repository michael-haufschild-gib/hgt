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

section Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]

/-- If every intertwiner of `ρ` is a scalar, the space of intertwiners is a line. -/
theorem finrank_invariants_linHom_eq_one (ρ : Representation ℂ G V)
    (hschur : ∀ f : V →ₗ[ℂ] V, (∀ g : G, (ρ g) ∘ₗ f = f ∘ₗ (ρ g)) → ∃ c : ℂ, ∀ v, f v = c • v) :
    Module.finrank ℂ ↥(Representation.linHom ρ ρ).invariants = 1 := by
  have hid : (LinearMap.id : V →ₗ[ℂ] V) ∈ (Representation.linHom ρ ρ).invariants := by
    rw [Representation.mem_invariants]
    intro g
    rw [Representation.linHom_apply]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
  have hidne : (⟨LinearMap.id, hid⟩ : ↥(Representation.linHom ρ ρ).invariants) ≠ 0 := by
    intro h
    refine hv0 ?_
    have h2 := congrArg (fun (w : ↥(Representation.linHom ρ ρ).invariants) =>
      (w : V →ₗ[ℂ] V) v0) h
    simpa using h2
  refine (finrank_eq_one_iff_of_nonzero' _ hidne).mpr ?_
  rintro ⟨f, hf⟩
  rw [Representation.mem_invariants] at hf
  have hequiv : ∀ g : G, (ρ g) ∘ₗ f = f ∘ₗ (ρ g) := by
    intro g
    have hinv : ∀ w : V, (ρ g⁻¹) ((ρ g) w) = w := by
      intro w
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    refine LinearMap.ext fun v => ?_
    have h := hf g
    rw [Representation.linHom_apply] at h
    have h2 := congrArg (fun (φ : V →ₗ[ℂ] V) => φ ((ρ g) v)) h
    simp only [LinearMap.coe_comp, Function.comp_apply, hinv] at h2
    simpa using h2
  obtain ⟨c, hc⟩ := hschur f hequiv
  exact ⟨c, Subtype.ext (LinearMap.ext fun v => by simpa using (hc v).symm)⟩

/-- Simplicity criterion for `FDRep.of ρ`: every intertwiner is a scalar. -/
theorem simple_of_schur (ρ : Representation ℂ G V)
    (hschur : ∀ f : V →ₗ[ℂ] V, (∀ g : G, (ρ g) ∘ₗ f = f ∘ₗ (ρ g)) → ∃ c : ℂ, ∀ v, f v = c • v) :
    Simple (FDRep.of ρ) := by
  haveI : NeZero ((Nat.card G : ℂ)) := ⟨by simp [Nat.card_eq_fintype_card, Fintype.card_ne_zero]⟩
  rw [FDRep.simple_iff_end_is_rank_one,
    ← LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom
      (FDRep.of ρ) (FDRep.of ρ))]
  rw [FDRep.of_ρ']
  exact finrank_invariants_linHom_eq_one ρ hschur

end Abstract

/-- The representation of `G` on a `G`-stable subspace of the group algebra. -/
noncomputable def repOf {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) :
    Representation ℂ G ↥N where
  toFun := rho hN
  map_one' := rho_one hN
  map_mul' g h := rho_mul hN g h

omit [Fintype G] in
@[simp] theorem repOf_apply {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g : G) :
    repOf hN g = rho hN g := rfl

/-- The object of `FDRep ℂ G` attached to a `G`-stable subspace. -/
noncomputable def fdRepOf {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) :
    FDRep ℂ G := FDRep.of (repOf hN)

theorem character_fdRepOf {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g : G) :
    (fdRepOf hN).character g = chi hN g := rfl

theorem simple_fdRepOf {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsMinimalGStable N) :
    Simple (fdRepOf hN.stable) := by
  haveI : Nontrivial ↥N := Submodule.nontrivial_iff_ne_bot.mpr hN.ne_bot
  exact simple_of_schur (repOf hN.stable) (fun f hf => schur hN f hf)

end GaloisForLFunctions.HTGeometry.GroupCharacter
