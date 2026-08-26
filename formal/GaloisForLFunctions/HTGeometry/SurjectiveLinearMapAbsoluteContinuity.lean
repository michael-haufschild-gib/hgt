import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# Absolute continuity under a surjective finite linear map

The pushforward of additive Haar measure by a surjective finite-dimensional linear map is a
positive scalar multiple of additive Haar measure.  Therefore every law dominated by source
Lebesgue measure has a target law dominated by target Lebesgue measure.  This is the reusable
finite-dimensional bridge from Hermite interpolation to nondegenerate finite-jet laws.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A surjective complex-linear image of a finite-dimensional Lebesgue-absolutely-continuous law
is again Lebesgue-absolutely-continuous. -/
theorem map_surjectiveLinearMap_absolutelyContinuous
    {M N : ℕ} (L : (Fin M → ℂ) →ₗ[ℂ] (Fin N → ℂ))
    (hL : Function.Surjective L) (μ : Measure (Fin M → ℂ))
    (hμ : μ ≪ (volume : Measure (Fin M → ℂ))) :
    Measure.map L μ ≪ (volume : Measure (Fin N → ℂ)) := by
  have hmeas : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hpush := hμ.map hmeas
  obtain ⟨c, _hc, hvolume⟩ := L.exists_map_addHaar_eq_smul_addHaar
    (volume : Measure (Fin M → ℂ)) (volume : Measure (Fin N → ℂ)) hL
  rw [hvolume] at hpush
  exact hpush.trans Measure.smul_absolutelyContinuous

end

end GaloisForLFunctions.HTGeometry
