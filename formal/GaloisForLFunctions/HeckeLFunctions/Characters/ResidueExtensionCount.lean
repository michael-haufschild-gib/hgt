import GaloisForLFunctions.HeckeLFunctions.Characters.RestrictionFibers
import GaloisForLFunctions.HeckeLFunctions.ResidueCharactersTrivialOnUnitsAreHeckeCharacters

/-!
# The exact number of Hecke characters with fixed residue and sign data

A character of finite residues and real signs comes from a Hecke character exactly
when it is trivial on the image of global units. For every number field the fibre
then has the size of the ordinary class group; otherwise it is empty.

The principal ray classes are the kernel of `Cl_𝔪 → Cl_K`. Descending the residue
character to that kernel and extending it makes the fibre a copy of the class
characters. This applies Proposition 3.12 of arXiv:2610.23742 to the existing
number-field ray-class sequence, without requiring a principal ideal ring.
-/

noncomputable section
open NumberField
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- Finite residues and real signs map onto the principal ray classes. -/
def principalRayResidueMap :
    (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) →* (toClassGroup 𝔪).ker :=
  (fullRayResidueClass 𝔪).codRestrict _ fun g => by
    obtain ⟨α, rfl⟩ := rayHom_surjective 𝔪 g
    rw [fullRayResidueClass_rayHom, ← range_rayResidueClass]
    exact ⟨⟨rayHom 𝔪 α, α, rfl⟩, rayResidueClass_apply 𝔪 α⟩

theorem principalRayResidueMap_surjective : Function.Surjective (principalRayResidueMap 𝔪) := by
  intro c
  obtain ⟨α, hα⟩ := ker_toClassGroup_le 𝔪 c c.property
  refine ⟨rayHom 𝔪 α, Subtype.ext ?_⟩
  change fullRayResidueClass 𝔪 (rayHom 𝔪 α) = c.val
  rw [fullRayResidueClass_rayHom, hα]

private theorem ker_principalRayResidueMap_le
    (φ : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) →* ℂˣ)
    (hφ : ∀ u : (𝓞 K)ˣ, φ (rayHom 𝔪 (globalUnitPrimeTo 𝔪 u)) = 1) :
    (principalRayResidueMap 𝔪).ker ≤ φ.ker := by
  intro g hg
  change principalRayResidueMap 𝔪 g = 1 at hg
  have hclass : fullRayResidueClass 𝔪 g = 1 := congrArg Subtype.val hg
  exact ker_rayResidueClass_le 𝔪 φ hφ
    (show (⟨g, rayHom_surjective 𝔪 g⟩ : (rayHom 𝔪).range) ∈
      (rayResidueClass 𝔪).ker from hclass)

/-- Compatible residue and sign data descend to a character of the principal ray classes. -/
def principalRayCharacter
    (φ : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) →* ℂˣ)
    (hφ : ∀ u : (𝓞 K)ˣ, φ (rayHom 𝔪 (globalUnitPrimeTo 𝔪 u)) = 1) :
    (toClassGroup 𝔪).ker →* ℂˣ :=
  (QuotientGroup.lift _ φ (ker_principalRayResidueMap_le 𝔪 φ hφ)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (principalRayResidueMap_surjective 𝔪)).symm.toMonoidHom

theorem principalRayCharacter_apply
    (φ : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) →* ℂˣ)
    (hφ : ∀ u : (𝓞 K)ˣ, φ (rayHom 𝔪 (globalUnitPrimeTo 𝔪 u)) = 1)
    (g : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)) :
    principalRayCharacter 𝔪 φ hφ (principalRayResidueMap 𝔪 g) = φ g := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _
      (principalRayResidueMap_surjective 𝔪)).symm (principalRayResidueMap 𝔪 g) =
      (g : _ ⧸ (principalRayResidueMap 𝔪).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [principalRayCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    h, QuotientGroup.lift_mk]

private theorem residue_fiber_iff_principal_fiber
    (φ : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) →* ℂˣ)
    (hφ : ∀ u : (𝓞 K)ˣ, φ (rayHom 𝔪 (globalUnitPrimeTo 𝔪 u)) = 1)
    (ψ : HeckeCharacter 𝔪) :
    rayResidueCharacter 𝔪 ψ = φ ↔
      ψ.comp (toClassGroup 𝔪).ker.subtype = principalRayCharacter 𝔪 φ hφ := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro c
    obtain ⟨g, rfl⟩ := principalRayResidueMap_surjective 𝔪 c
    change ψ (fullRayResidueClass 𝔪 g) =
      principalRayCharacter 𝔪 φ hφ (principalRayResidueMap 𝔪 g)
    rw [principalRayCharacter_apply]
    exact congrArg (fun χ => χ g) h
  · intro h
    apply MonoidHom.ext
    intro g
    have hg := congrArg (fun χ : (toClassGroup 𝔪).ker →* ℂˣ =>
      χ (principalRayResidueMap 𝔪 g)) h
    exact hg.trans (principalRayCharacter_apply 𝔪 φ hφ g)

/-- The extensions of compatible residue data are parametrised by ordinary class characters. -/
def residueExtensionEquiv
    (φ : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) →* ℂˣ)
    (hφ : ∀ u : (𝓞 K)ˣ, φ (rayHom 𝔪 (globalUnitPrimeTo 𝔪 u)) = 1) :
    {ψ : HeckeCharacter 𝔪 // rayResidueCharacter 𝔪 ψ = φ} ≃
      (ClassGroup (𝓞 K) →* ℂˣ) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective _ (toClassGroup_surjective 𝔪)
  let e₁ : {ψ : HeckeCharacter 𝔪 // rayResidueCharacter 𝔪 ψ = φ} ≃
      {ψ : HeckeCharacter 𝔪 //
        ψ.comp (toClassGroup 𝔪).ker.subtype = principalRayCharacter 𝔪 φ hφ} := {
    toFun ψ := ⟨ψ.val, (residue_fiber_iff_principal_fiber 𝔪 φ hφ ψ.val).mp ψ.property⟩
    invFun ψ := ⟨ψ.val, (residue_fiber_iff_principal_fiber 𝔪 φ hφ ψ.val).mpr ψ.property⟩
    left_inv _ := Subtype.ext rfl
    right_inv _ := Subtype.ext rfl }
  refine e₁.trans ((CharacterExtensions.extensionEquiv (toClassGroup 𝔪).ker
    (principalRayCharacter 𝔪 φ hφ)).trans ?_)
  exact {
    toFun χ := χ.comp e.symm.toMonoidHom
    invFun χ := χ.comp e.toMonoidHom
    left_inv χ := by
      apply MonoidHom.ext
      intro q
      exact congrArg χ (e.symm_apply_apply q)
    right_inv χ := by
      apply MonoidHom.ext
      intro c
      exact congrArg χ (e.apply_symm_apply c) }

/-- Global-unit compatibility is exactly the obstruction to extending residue and sign data. -/
theorem residueExtensions_nonempty_iff
    (φ : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) →* ℂˣ) :
    Nonempty {ψ : HeckeCharacter 𝔪 // rayResidueCharacter 𝔪 ψ = φ} ↔
      ∀ u : (𝓞 K)ˣ, φ (rayHom 𝔪 (globalUnitPrimeTo 𝔪 u)) = 1 := by
  constructor
  · rintro ⟨ψ, hψ⟩ u
    rw [← hψ, rayResidueCharacter, MonoidHom.comp_apply, fullRayResidueClass_rayHom,
      rayClassOfElt_globalUnit, map_one]
  · intro hφ
    exact ⟨(residueExtensionEquiv 𝔪 φ hφ).symm 1⟩

/-- Every compatible datum has exactly `h_K` lifts; incompatible data have none. -/
theorem card_residueExtensions
    (φ : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) →* ℂˣ) :
    Nat.card {ψ : HeckeCharacter 𝔪 // rayResidueCharacter 𝔪 ψ = φ} =
      if ∀ u : (𝓞 K)ˣ, φ (rayHom 𝔪 (globalUnitPrimeTo 𝔪 u)) = 1
      then Nat.card (ClassGroup (𝓞 K)) else 0 := by
  by_cases hφ : ∀ u : (𝓞 K)ˣ, φ (rayHom 𝔪 (globalUnitPrimeTo 𝔪 u)) = 1
  · rw [if_pos hφ, Nat.card_congr (residueExtensionEquiv 𝔪 φ hφ),
      RHTower.deningerCharacter_card]
  · rw [if_neg hφ]
    letI : IsEmpty {ψ : HeckeCharacter 𝔪 // rayResidueCharacter 𝔪 ψ = φ} :=
      ⟨fun ψ => hφ ((residueExtensions_nonempty_iff 𝔪 φ).mp ⟨ψ⟩)⟩
    exact Nat.card_eq_zero_of_isEmpty

#print axioms residueExtensionEquiv
#print axioms residueExtensions_nonempty_iff
#print axioms card_residueExtensions

end GaloisForLFunctions.HeckeLFunctions
