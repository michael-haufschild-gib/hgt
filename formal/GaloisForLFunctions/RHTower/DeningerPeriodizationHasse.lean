import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.RHTower.DeningerPeriodizationSplit

/-!
# Hasse quotient for Deninger periodization

Global exponential-Schwartz data modulo lattice defects are exactly smooth periodic local data.
The quotient equivalence is supplemented by congruence and representative-classification forms.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Global exponential-Schwartz data modulo lattice defects classify periodic local data. -/
noncomputable def deningerPeriodizationHasseQuotientEquiv {L : ℝ} (hL : 0 < L) :
    (DeningerExpSchwartz ⧸ LinearMap.range (deningerPeriodizationDefect L)) ≃ₗ[ℂ]
      DeningerSmoothPeriodic L :=
  linearHasseQuotientEquiv
    (deningerPeriodizationDefect L) (deningerPeriodizationMap hL)
    (LinearMap.exact_iff.mpr (deningerPeriodizationMap_ker hL))
    (deningerPeriodizationMap_surjective hL)

@[simp] theorem deningerPeriodizationHasseQuotientEquiv_mk
    {L : ℝ} (hL : 0 < L) (f : DeningerExpSchwartz) :
    deningerPeriodizationHasseQuotientEquiv hL (Submodule.Quotient.mk f) =
      deningerPeriodizationMap hL f := by
  simp [deningerPeriodizationHasseQuotientEquiv]

/-- Two global representatives yield the same periodic local datum exactly when their difference
is a lattice defect. -/
theorem deningerPeriodization_congr_hasse_iff
    {L : ℝ} (hL : 0 < L) (f g : DeningerExpSchwartz) :
    f - g ∈ LinearMap.range (deningerPeriodizationDefect L) ↔
      deningerPeriodizationMap hL f = deningerPeriodizationMap hL g :=
  linearHasse_congr_iff
    (deningerPeriodizationDefect L) (deningerPeriodizationMap hL)
    (LinearMap.exact_iff.mpr (deningerPeriodizationMap_ker hL)) f g

/-- Every periodic local datum has a global representative, unique modulo lattice defects. -/
theorem deningerPeriodization_exists_unique_mod_defect
    {L : ℝ} (hL : 0 < L) (F : DeningerSmoothPeriodic L) :
    ∃ f : DeningerExpSchwartz, deningerPeriodizationMap hL f = F ∧
      ∀ g : DeningerExpSchwartz, deningerPeriodizationMap hL g = F ↔
        g - f ∈ LinearMap.range (deningerPeriodizationDefect L) :=
  linearHasse_exists_unique_mod_global
    (deningerPeriodizationDefect L) (deningerPeriodizationMap hL)
    (LinearMap.exact_iff.mpr (deningerPeriodizationMap_ker hL))
    (deningerPeriodizationMap_surjective hL) F

end
end RHTower
