import GaloisForLFunctions.RHTower.Artin.ArtinCharacterInduction
import GaloisForLFunctions.RHTower.Artin.ArtinVirtualCharacterPairing

/-!
# Universe-polymorphic Frobenius reciprocity

The induction--restriction adjunction is constructed directly on raw intertwining spaces. Unlike
the categorical `Rep.indResHomEquiv`, this statement permits representation carriers in unrelated
universes. Character-pairing reciprocity follows by identifying both pairings with dimensions of
the corresponding intertwining spaces.
-/

open scoped BigOperators MonoidAlgebra

noncomputable section

universe u v w x

namespace GaloisForLFunctions

open Finsupp TensorProduct Representation

/-- Universe-polymorphic induction--restriction adjunction on actual intertwining spaces. -/
def indResIntertwiningEquiv
    {H : Type u} {G : Type v} [Group H] [Group G]
    {V : Type w} [AddCommGroup V] [Module ℂ V]
    {W : Type x} [AddCommGroup W] [Module ℂ W]
    (φ : H →* G) (ρ : Representation ℂ H V) (σ : Representation ℂ G W) :
    (Representation.ind φ ρ).IntertwiningMap σ ≃ₗ[ℂ]
      ρ.IntertwiningMap (σ.comp φ) where
  toFun f := ⟨f.toLinearMap ∘ₗ IndV.mk φ ρ 1, fun g ↦ by
    ext y
    have hf := LinearMap.congr_fun (f.2 (φ g)) (IndV.mk φ ρ 1 y)
    simp_all [← Coinvariants.mk_inv_tmul]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h ↦ σ h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)
    fun g ↦ by
      ext h y
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      have hf := LinearMap.congr_fun (f.2 g) y
      have hf' : f (ρ g y) = σ (φ g) (f y) := by simpa using hf
      simp [ofMulAction_single, mul_inv_rev, hf'], fun g ↦ by ext; simp⟩
  left_inv f := by
    ext h y
    have hf := LinearMap.congr_fun (f.2 h⁻¹) (IndV.mk φ ρ 1 y)
    simpa using hf.symm
  right_inv _ := by ext; simp

/-- Frobenius reciprocity for normalized character pairings of actual finite-dimensional
representations, with no carrier-universe restriction. -/
theorem characterPairing_induced_restricted
    {H : Type u} {G : Type v} [Group H] [Fintype H] [Group G] [Fintype G]
    (φ : H →* G)
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type x} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G W) :
    characterPairing G (Representation.ind φ ρ).character σ.character =
      characterPairing H ρ.character (Representation.character (σ.comp φ)) := by
  rw [representationCharacterPairing_eq_finrank, representationCharacterPairing_eq_finrank]
  exact congrArg (fun n : ℕ ↦ (n : ℂ))
    (LinearEquiv.finrank_eq (indResIntertwiningEquiv φ ρ σ))

end GaloisForLFunctions
