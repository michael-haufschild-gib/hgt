import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilPrimeEntryAtomicConnection
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimeEntrySlopeTomography

/-!
# Guinand--Weil / first-clock prime-entry bridge

The corpus already contained one-sided entry tomography for the first physical odd clock in full
aperture `L`.  The Guinand--Weil event connection uses half-aperture `a=L/2`, includes the source
normalization by `pi`, and then extends through diagonal and divided-difference coordinates.

This file records the exact scale dictionary and rewrites the new whole-matrix tangent directly in
terms of the prior first-clock slope.  It prevents the new result from claiming the old scalar
slope as novelty while isolating the genuinely new rank-one matrix lift.
-/

noncomputable section

namespace RHTower

open Matrix

/-- Half-aperture and source normalization multiply the old first-clock slope by `2 / pi`. -/
theorem ccmGuinandWeilPrimeEntryMatrixRate_eq_firstClockSlope (k : ℕ) :
    ccmGuinandWeilPrimeEntryMatrixRate k =
      (2 / Real.pi) * ccmFirstClockPrimeEntrySlope k := by
  rw [ccmGuinandWeilPrimeEntryMatrixRate, ccmFirstClockPrimeEntrySlope]
  field_simp [Real.pi_ne_zero]
  ring

/-- The new whole-matrix event tangent is the old scalar tomography slope lifted along the fixed
constant-boundary projector. -/
theorem ccmGuinandWeilPrimeEntryRankOneTangent_eq_firstClockSlope
    (k : ℕ) (N : ℕ) :
    ccmGuinandWeilPrimeEntryRankOneTangent k N =
      ((2 / Real.pi) * ccmFirstClockPrimeEntrySlope k) •
        Matrix.vecMulVec
          (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
          ccmConstantBoundary := by
  rw [ccmGuinandWeilPrimeEntryRankOneTangent,
    ccmGuinandWeilPrimeEntryMatrixRate_eq_firstClockSlope]

end RHTower
