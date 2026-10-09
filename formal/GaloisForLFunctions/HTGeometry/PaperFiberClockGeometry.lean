import GaloisForLFunctions.HTGeometry.PaperFourVariableClockCriterion
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.AllFibers
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.GeometricInterpretation
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.Rectifiability

/-!
The exact fibres from OpenAI/math's StableCoordinate construction are affine
three-spaces over ℂ. Ambient scheme rectification of any one fibre is equivalent
to existence of a locally nilpotent transverse clock on the original four
variables. This connects the source's geometric and algebraic interfaces without
assuming either rectifiability or a clock.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate StableCoordinate.GeometricInterpretation

/-- Every exact fibre has an affine-space isomorphism over the complex base. -/
def paperFiberAffineSpaceIso (t : ℂ) :=
  AffineGeometry.affineSpaceOverIsoOfAlgEquiv (exactFiberEquiv t)

/-- Each actual fibre ideal is prime; no generic-fibre hypothesis is required. -/
theorem paperFiberIdeal_isPrime (t : ℂ) : (fiberIdeal t).IsPrime :=
  fiberIdeal_isPrime_of_affineFiber t (all_fibers_isAffineThreeSpace t)

/-- Scheme rectification of one level is exactly the transverse-clock problem. -/
theorem paperFourVariableClock_iff_schemeRectifiable (t : ℂ) :
    (∃ D : Derivation ℂ (R 4) (R 4),
      D f = 1 ∧ ∀ p : R 4, ∃ n : ℕ, (D^[n]) p = 0) ↔
      IsSchemeRectifiableFiber t :=
  paperFourVariableClock_iff_coordinate.trans
    ((rectifiableFiber_iff_coordinate t).symm.trans
      (rectifiableFiber_iff_schemeRectifiable t (all_fibers_isAffineThreeSpace t)))

/-- Ambient rectifiability cannot vary with the chosen complex level. -/
theorem paperFiberSchemeRectifiable_level_independent (s t : ℂ) :
    IsSchemeRectifiableFiber s ↔ IsSchemeRectifiableFiber t :=
  (paperFourVariableClock_iff_schemeRectifiable s).symm.trans
    (paperFourVariableClock_iff_schemeRectifiable t)

/-- Straightening one embedded fibre is equivalent to straightening every fibre. -/
theorem paperFiberSchemeRectifiable_iff_all (t : ℂ) :
    IsSchemeRectifiableFiber t ↔ ∀ s : ℂ, IsSchemeRectifiableFiber s := by
  exact ⟨fun h s => (paperFiberSchemeRectifiable_level_independent t s).mp h,
    fun h => h t⟩

end GaloisForLFunctions.HTGeometry
