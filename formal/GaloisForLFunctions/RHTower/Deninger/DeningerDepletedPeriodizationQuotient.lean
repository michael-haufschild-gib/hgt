import GaloisForLFunctions.RHTower.Deninger.DeningerDepletedQuotient
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Quotient form of depleted periodization

The depleted periodization sequence identifies the global quotient after removing its admitted
sector with the smooth periodic data observed at the period.  This packages the short exact
sequence as its canonical quotient-level local realization equivalence.
-/

namespace RHTower

noncomputable section

/-- **Depleted periodization local-global equivalence.** Quotienting the depleted global sector by
the admitted sector gives exactly the smooth periodic data at the local period. -/
noncomputable def deningerDepletedPeriodizationQuotientEquiv {L : ℝ} (hL : 0 < L) :
    (DeningerDepletedQuotient L ⧸ LinearMap.range (deningerIota L)) ≃ₗ[ℂ]
      ↥(DeningerSmoothPeriodic L) :=
  (Submodule.quotEquivOfEq _ _ (deningerIota_range_eq_perBar_ker hL)).trans
    (LinearMap.quotKerEquivOfSurjective (deningerPerBar hL)
      (deningerPerBar_surjective hL))

/-- The depleted periodization quotient equivalence is induced by descended periodization. -/
theorem deningerDepletedPeriodizationQuotientEquiv_mk {L : ℝ} (hL : 0 < L)
    (x : DeningerDepletedQuotient L) :
    deningerDepletedPeriodizationQuotientEquiv hL (Submodule.Quotient.mk x) =
      deningerPerBar hL x := by
  simp [deningerDepletedPeriodizationQuotientEquiv]

end
