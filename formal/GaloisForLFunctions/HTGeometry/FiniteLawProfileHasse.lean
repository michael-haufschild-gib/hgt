import GaloisForLFunctions.HTGeometry.ConstitutiveAdaptiveProcompletion

/-!
# Complete-profile Hasse principle for finite effective laws

A finite-support law on natural-number coordinates is reconstructed by its complete Boolean
response profile.  Equality and emptiness are coordinatewise, one coordinate distinguishes every
pair of laws, and every effective complete profile has one unique finite-support realization.

This identifies the sharp positive side of the corpus's adaptive-effectivity obstruction: complete
local data are faithful even though no finite adaptive experiment decides global effectivity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Effective Boolean profiles as an intrinsic subtype. -/
abbrev EffectiveConstitutiveBooleanProfile :=
  {b : ConstitutiveBooleanProfile // ExperimentallyEffective b}

/-- Finite effective laws are equivalent to the complete profiles they realize. -/
noncomputable def finiteLawProfileEquivRange :
    Finset ℕ ≃ Set.range finiteLawProfile :=
  Equiv.ofInjective finiteLawProfile finiteLawProfile_injective

/-- Complete-profile Hasse congruence for finite effective laws. -/
theorem finiteLaw_congr_profile_hasse_iff (F G : Finset ℕ) :
    F = G ↔ ∀ n : ℕ, finiteLawProfile F n = finiteLawProfile G n := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    exact finiteLawProfile_injective (funext h)

/-- A finite law is empty exactly when every local Boolean response is false. -/
theorem finiteLaw_eq_empty_profile_hasse_iff (F : Finset ℕ) :
    F = ∅ ↔ ∀ n : ℕ, finiteLawProfile F n = false := by
  rw [finiteLaw_congr_profile_hasse_iff]
  simp [finiteLawProfile]

/-- Distinct finite laws are detected at one queried coordinate. -/
theorem exists_finiteLawProfile_ne_of_ne
    (F G : Finset ℕ) (hFG : F ≠ G) :
    ∃ n : ℕ, finiteLawProfile F n ≠ finiteLawProfile G n := by
  by_contra h
  push Not at h
  exact hFG ((finiteLaw_congr_profile_hasse_iff F G).2 h)

/-- Every effective complete Boolean profile has one unique finite-support global law. -/
theorem effectiveProfile_existsUnique_finiteLaw
    (b : EffectiveConstitutiveBooleanProfile) :
    ∃! F : Finset ℕ, finiteLawProfile F = b.1 := by
  obtain ⟨F, hF⟩ := b.2
  exact ⟨F, hF, fun G hG ↦ finiteLawProfile_injective (hG.trans hF.symm)⟩

end

end GaloisForLFunctions.HTGeometry
