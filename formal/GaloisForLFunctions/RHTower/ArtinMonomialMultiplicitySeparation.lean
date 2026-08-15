import GaloisForLFunctions.RHTower.ArtinVirtualFrobeniusReciprocity
import GaloisForLFunctions.RHTower.ArtinFiniteAbelianFourier
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Separation of concrete virtual Artin characters by monomial multiplicities

The full family of integral multiplicities against induced linear characters determines a
concrete virtual character of a finite group.  The proof restricts to the cyclic subgroup generated
by an arbitrary group element, transports each monomial coefficient by virtual Frobenius
reciprocity, and applies the integral Fourier expansion on that cyclic subgroup.

This is finite-character infrastructure only.  It is not Brauer induction, an integral monomial
span theorem, a Heilbronn effectivity result, or a statement about Artin `L`-functions.
-/

open scoped BigOperators Classical

noncomputable section

universe u

namespace GaloisForLFunctions

/-- The complete integral monomial-multiplicity profile of a concrete virtual character. -/
def monomialMultiplicityProfile (G : Type u) [Group G] [Fintype G]
    (θ : VirtualCharacter G) :
    (Σ H : Subgroup G, LinearCharacter H) → ℤ :=
  fun q => monomialMultiplicity G θ q.1 q.2

/-- The integral virtual-character multiplicity is symmetric. -/
theorem virtualMultiplicity_comm (G : Type u) [Group G] [Fintype G]
    (θ η : VirtualCharacter G) :
    virtualMultiplicity G θ η = virtualMultiplicity G η θ := by
  apply Int.cast_injective (α := ℂ)
  rw [virtualMultiplicity_cast, virtualMultiplicity_cast]
  exact characterPairing_comm G _ _

/-- A concrete virtual character of a finite group is determined by all of its integral
multiplicities against induced linear characters. -/
theorem monomialMultiplicityProfile_injective (G : Type u) [Group G] [Fintype G] :
    Function.Injective (monomialMultiplicityProfile G) := by
  intro θ η hprofile
  apply Subtype.ext
  funext g
  let H : Subgroup G := Subgroup.zpowers g
  letI : IsCyclic H := by
    dsimp [H]
    infer_instance
  letI : CommGroup H := IsCyclic.commGroup
  letI : Finite (LinearCharacter H) := RHTower.deningerCharacterGroup_finite
  letI : Fintype (LinearCharacter H) := Fintype.ofFinite _
  have hmono (χ : LinearCharacter H) :
      monomialMultiplicity G θ H χ = monomialMultiplicity G η H χ := by
    simpa only [monomialMultiplicityProfile] using
      congrFun hprofile ⟨H, χ⟩
  have hcoeff (χ : LinearCharacter H) :
      virtualMultiplicity H (linearVirtualCharacter H χ)
          (VirtualCharacter.restrict G H.subtype θ) =
        virtualMultiplicity H (linearVirtualCharacter H χ)
          (VirtualCharacter.restrict G H.subtype η) := by
    calc
      virtualMultiplicity H (linearVirtualCharacter H χ)
          (VirtualCharacter.restrict G H.subtype θ) =
          virtualMultiplicity H (VirtualCharacter.restrict G H.subtype θ)
            (linearVirtualCharacter H χ) :=
        virtualMultiplicity_comm H _ _
      _ = monomialMultiplicity G θ H χ :=
        (monomialMultiplicity_eq_restriction_linearMultiplicity G H χ θ).symm
      _ = monomialMultiplicity G η H χ := hmono χ
      _ = virtualMultiplicity H (VirtualCharacter.restrict G H.subtype η)
          (linearVirtualCharacter H χ) :=
        monomialMultiplicity_eq_restriction_linearMultiplicity G H χ η
      _ = virtualMultiplicity H (linearVirtualCharacter H χ)
          (VirtualCharacter.restrict G H.subtype η) :=
        virtualMultiplicity_comm H _ _
  have hres : VirtualCharacter.restrict G H.subtype θ =
      VirtualCharacter.restrict G H.subtype η := by
    calc
      VirtualCharacter.restrict G H.subtype θ =
          ∑ χ : LinearCharacter H,
            virtualMultiplicity H (linearVirtualCharacter H χ)
              (VirtualCharacter.restrict G H.subtype θ) • linearVirtualCharacter H χ :=
        finiteAbelian_virtual_fourier_integral_subtype _
      _ = ∑ χ : LinearCharacter H,
            virtualMultiplicity H (linearVirtualCharacter H χ)
              (VirtualCharacter.restrict G H.subtype η) • linearVirtualCharacter H χ := by
        apply Finset.sum_congr rfl
        intro χ _
        rw [hcoeff χ]
      _ = VirtualCharacter.restrict G H.subtype η :=
        (finiteAbelian_virtual_fourier_integral_subtype _).symm
  simpa [H] using
    congrArg (fun ξ : VirtualCharacter H => ξ.val ⟨g, Subgroup.mem_zpowers g⟩) hres

end GaloisForLFunctions
