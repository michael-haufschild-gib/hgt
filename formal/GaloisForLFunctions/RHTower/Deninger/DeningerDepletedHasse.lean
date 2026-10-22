import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.RHTower.Deninger.DeningerDepletedQuotient

/-!
# Hasse quotient for the depleted Meyer sector

Depleted Meyer classes modulo the admitted global sector are exactly smooth periodic local data.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Depleted Meyer classes modulo admitted classes classify periodic local data. -/
noncomputable def deningerDepletedHasseQuotientEquiv {L : ℝ} (hL : 0 < L) :
    (DeningerDepletedQuotient L ⧸ LinearMap.range (deningerIota L)) ≃ₗ[ℂ]
      DeningerSmoothPeriodic L :=
  linearHasseQuotientEquiv
    (deningerIota L) (deningerPerBar hL)
    (LinearMap.exact_iff.mpr (deningerIota_range_eq_perBar_ker hL).symm)
    (deningerPerBar_surjective hL)

@[simp] theorem deningerDepletedHasseQuotientEquiv_mk
    {L : ℝ} (hL : 0 < L) (x : DeningerDepletedQuotient L) :
    deningerDepletedHasseQuotientEquiv hL (Submodule.Quotient.mk x) =
      deningerPerBar hL x := by
  simp [deningerDepletedHasseQuotientEquiv]

/-- Two depleted classes have identical periodic data exactly when they differ by an admitted
global class. -/
theorem deningerDepleted_congr_hasse_iff
    {L : ℝ} (hL : 0 < L) (x y : DeningerDepletedQuotient L) :
    x - y ∈ LinearMap.range (deningerIota L) ↔
      deningerPerBar hL x = deningerPerBar hL y :=
  linearHasse_congr_iff
    (deningerIota L) (deningerPerBar hL)
    (LinearMap.exact_iff.mpr (deningerIota_range_eq_perBar_ker hL).symm) x y

/-- Every periodic datum has a depleted representative, unique modulo the admitted sector. -/
theorem deningerDepleted_exists_unique_mod_admitted
    {L : ℝ} (hL : 0 < L) (F : DeningerSmoothPeriodic L) :
    ∃ x : DeningerDepletedQuotient L, deningerPerBar hL x = F ∧
      ∀ y : DeningerDepletedQuotient L, deningerPerBar hL y = F ↔
        y - x ∈ LinearMap.range (deningerIota L) :=
  linearHasse_exists_unique_mod_global
    (deningerIota L) (deningerPerBar hL)
    (LinearMap.exact_iff.mpr (deningerIota_range_eq_perBar_ker hL).symm)
    (deningerPerBar_surjective hL) F

end
end RHTower
