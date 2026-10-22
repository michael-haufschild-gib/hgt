import GaloisForLFunctions.RHTower.Deninger.DeningerPeriodizationSplit
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Quotient form of periodization

The periodization sequence identifies global Schwartz data modulo the translation-defect image
with the smooth periodic data observed at one period.  This gives the canonical quotient-level
realization form of the split exact periodization sequence.
-/

namespace RHTower

noncomputable section

/-- **Periodization local-global equivalence.** Global Schwartz data modulo translation defects
are linearly equivalent to smooth periodic data. -/
noncomputable def deningerPeriodizationQuotientEquiv {L : ℝ} (hL : 0 < L) :
    (DeningerExpSchwartz ⧸ LinearMap.range (deningerPeriodizationDefect L)) ≃ₗ[ℂ]
      ↥(DeningerSmoothPeriodic L) :=
  (Submodule.quotEquivOfEq _ _ (deningerPeriodizationMap_ker hL).symm).trans
    (LinearMap.quotKerEquivOfSurjective (deningerPeriodizationMap hL)
      (deningerPeriodizationMap_surjective hL))

/-- The periodization quotient equivalence is induced by the periodization map. -/
theorem deningerPeriodizationQuotientEquiv_mk {L : ℝ} (hL : 0 < L)
    (x : DeningerExpSchwartz) :
    deningerPeriodizationQuotientEquiv hL (Submodule.Quotient.mk x) =
      deningerPeriodizationMap hL x := by
  simp [deningerPeriodizationQuotientEquiv]

end
