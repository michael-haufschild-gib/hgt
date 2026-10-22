import GaloisForLFunctions.RHTower.Artin.ArtinMonomialMultiplicitySeparation

/-!
# Monomial-multiplicity Hasse principle for virtual Artin characters

For a finite group, all integral multiplicities against characters induced from linear subgroup
characters form a faithful additive profile of a concrete virtual character.  This yields a
Brauer-style local-to-global congruence and guarantees that one monomial probe detects every
nonzero virtual character.

This is character-theoretic separation, not the integral spanning statement of Brauer induction.
-/

open scoped Classical

noncomputable section

namespace GaloisForLFunctions

universe u

/-- Complete monomial multiplicity profile as an additive observable. -/
def monomialMultiplicityProfileAddHom
    (G : Type u) [Group G] [Fintype G] :
    VirtualCharacter G →+ ((Σ H : Subgroup G, LinearCharacter H) → ℤ) where
  toFun := monomialMultiplicityProfile G
  map_zero' := by
    funext q
    apply Int.cast_injective (α := ℂ)
    simp [monomialMultiplicityProfile, monomialMultiplicity, virtualMultiplicity_cast]
  map_add' θ η := by
    funext q
    exact monomialMultiplicity_add G θ η q.1 q.2

@[simp] theorem monomialMultiplicity_zero
    (G : Type u) [Group G] [Fintype G]
    (H : Subgroup G) (χ : LinearCharacter H) :
    monomialMultiplicity G (0 : VirtualCharacter G) H χ = 0 := by
  have h := congrFun (monomialMultiplicityProfileAddHom G).map_zero ⟨H, χ⟩
  exact h

/-- Virtual characters are additively equivalent to realized monomial-multiplicity profiles. -/
noncomputable def monomialMultiplicityProfileRangeEquiv
    (G : Type u) [Group G] [Fintype G] :
    VirtualCharacter G ≃+ AddMonoidHom.range (monomialMultiplicityProfileAddHom G) :=
  AddEquiv.ofBijective (monomialMultiplicityProfileAddHom G).rangeRestrict
    ⟨(AddMonoidHom.rangeRestrict_injective_iff.mpr
      (monomialMultiplicityProfile_injective G)),
      (monomialMultiplicityProfileAddHom G).rangeRestrict_surjective⟩

/-- Brauer-style Hasse congruence: all induced-linear multiplicities determine a virtual
character. -/
theorem virtualCharacter_congr_monomialMultiplicity_hasse_iff
    (G : Type u) [Group G] [Fintype G] (θ η : VirtualCharacter G) :
    θ = η ↔ ∀ (H : Subgroup G) (χ : LinearCharacter H),
      monomialMultiplicity G θ H χ = monomialMultiplicity G η H χ := by
  constructor
  · rintro rfl
    exact fun _ _ ↦ rfl
  · intro h
    apply monomialMultiplicityProfile_injective G
    funext q
    exact h q.1 q.2

/-- A virtual character vanishes iff every monomial multiplicity vanishes. -/
theorem virtualCharacter_eq_zero_monomialMultiplicity_hasse_iff
    (G : Type u) [Group G] [Fintype G] (θ : VirtualCharacter G) :
    θ = 0 ↔ ∀ (H : Subgroup G) (χ : LinearCharacter H),
      monomialMultiplicity G θ H χ = 0 := by
  constructor
  · rintro rfl
    exact fun H χ ↦ monomialMultiplicity_zero G H χ
  · intro h
    apply monomialMultiplicityProfile_injective G
    funext q
    exact (h q.1 q.2).trans (monomialMultiplicity_zero G q.1 q.2).symm

/-- Every nonzero virtual character is detected by one induced linear character. -/
theorem exists_monomialMultiplicity_ne_zero_of_virtualCharacter_ne_zero
    (G : Type u) [Group G] [Fintype G] (θ : VirtualCharacter G) (hθ : θ ≠ 0) :
    ∃ (H : Subgroup G) (χ : LinearCharacter H), monomialMultiplicity G θ H χ ≠ 0 := by
  by_contra h
  push Not at h
  exact hθ ((virtualCharacter_eq_zero_monomialMultiplicity_hasse_iff G θ).2 h)

end GaloisForLFunctions

end
