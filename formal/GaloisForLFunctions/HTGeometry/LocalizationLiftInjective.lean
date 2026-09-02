import Mathlib.RingTheory.Localization.Basic

/-!
# Injective maps out of a localization

An injective ring map into a field extends injectively across any localization whose denominator
submonoid excludes zero.  This is the arbitrary-submonoid analogue of the principal-localization
lemma used by the critical source chart.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **An injective map to a field stays injective after localization away from zero.** -/
theorem injective_localizationLift_of_injective
    {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    {M : Submonoid R} [Algebra R S] [IsLocalization M S]
    (g : R →+* F) (hg : Function.Injective g) (hM : (0 : R) ∉ M) :
    Function.Injective
      (IsLocalization.lift (S := S) (g := g)
        (fun s => (isUnit_iff_ne_zero.mpr (fun hs =>
          hM (by
            have hs0 : (s : R) = 0 := hg (by simpa using hs)
            exact hs0 ▸ s.2))))) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
  rw [IsLocalization.lift_mk'] at hz
  have hx : g x = 0 :=
    (mul_eq_zero.mp hz).resolve_right (Units.ne_zero _)
  have hx0 : x = 0 := hg (by simpa using hx)
  rw [hx0]
  exact IsLocalization.mk'_zero s

end GaloisForLFunctions.HTGeometry
