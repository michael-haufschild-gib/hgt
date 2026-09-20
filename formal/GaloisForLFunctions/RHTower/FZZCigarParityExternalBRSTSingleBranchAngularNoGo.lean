import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBranchChargeNoGo
import GaloisForLFunctions.RHTower.FZZCigarParityTorusHolonomyFourierResonanceNoGo

/-!
# FZZ external-BRST single-branch angular no-go

## FZZ-P proof-chain position

Halder--Jafferis' compact-circle external momentum is the integer `p`.  The
literal marked `W⁺` and `W⁻` OPE branch charges are respectively `p` and `-p`.
For a single external insertion with no compensating compact Fourier weight,
the branch factor is therefore the unit-circle character of that charge.

Exact compact-circle orthogonality makes both unweighted angular averages zero
whenever a branch is present.  This kills the chain

`single external-BRST branch factor` → `unweighted compact integration` →
`oriented FZZ-P Ward source` → `radial zero exclusion` → `RH`.

The positive survivor is sharp: a source must contain a compact-charge-neutral
multi-vertex kernel or a nonfactorized matching Fourier weight before angular
integration.  This theorem does not assert cancellation for either survivor.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Compact angular factor forced by the `W⁺` external-BRST branch charge `p`. -/
def fzzCigarExternalBRSTPlusAngularBranchKernel
    (_k : ℝ) (_j : ℂ) (p _ν : ℤ) (s : ℝ) : ℂ :=
  RHTower.fzzTorusHolonomyCharacter p s

/-- Compact angular factor forced by the `W⁻` external-BRST branch charge `-p`. -/
def fzzCigarExternalBRSTMinusAngularBranchKernel
    (_k : ℝ) (_j : ℂ) (p _ν : ℤ) (s : ℝ) : ℂ :=
  RHTower.fzzTorusHolonomyCharacter (-p) s

/-- Exact unweighted compact average of the `W⁺` one-branch factor. -/
theorem intervalIntegral_fzzCigarExternalBRSTPlusAngularBranchKernel
    (k : ℝ) (j : ℂ) (p ν : ℤ) :
    (∫ s in (0 : ℝ)..1, fzzCigarExternalBRSTPlusAngularBranchKernel k j p ν s) =
      if p = 0 then 1 else 0 := by
  exact RHTower.intervalIntegral_fzzTorusHolonomyCharacter p

/-- Exact unweighted compact average of the `W⁻` one-branch factor. -/
theorem intervalIntegral_fzzCigarExternalBRSTMinusAngularBranchKernel
    (k : ℝ) (j : ℂ) (p ν : ℤ) :
    (∫ s in (0 : ℝ)..1, fzzCigarExternalBRSTMinusAngularBranchKernel k j p ν s) =
      if p = 0 then 1 else 0 := by
  change (∫ s in (0 : ℝ)..1, RHTower.fzzTorusHolonomyCharacter (-p) s) =
    if p = 0 then 1 else 0
  rw [RHTower.intervalIntegral_fzzTorusHolonomyCharacter]
  by_cases hp : p = 0
  · simp [hp]
  · have hneg : -p ≠ 0 := neg_ne_zero.mpr hp
    simp [hp, hneg]

/-- Every branch-incident single external insertion has vanishing unweighted
compact average for both marked winding signs. -/
theorem fzzCigarExternalBRSTAngularBranchAverages_eq_zero_of_incident
    (k : ℝ) (j : ℂ) (p ν : ℤ)
    (hincident : FZZCigarExternalBRSTMarkedBranchIncident k j p ν) :
    (∫ s in (0 : ℝ)..1, fzzCigarExternalBRSTPlusAngularBranchKernel k j p ν s) = 0 ∧
      (∫ s in (0 : ℝ)..1, fzzCigarExternalBRSTMinusAngularBranchKernel k j p ν s) = 0 := by
  have hp : p ≠ 0 :=
    (fzzCigarExternalBRSTMarkedBranchIncident_iff_momentum_ne_zero k j p ν).mp hincident
  constructor
  · rw [intervalIntegral_fzzCigarExternalBRSTPlusAngularBranchKernel, if_neg hp]
  · rw [intervalIntegral_fzzCigarExternalBRSTMinusAngularBranchKernel, if_neg hp]

/-- Closed FZZ-P subroute: a single branch-incident external BRST character
cannot survive unweighted compact integration. -/
theorem not_exists_fzzCigarExternalBRSTSingleBranch_unweightedAngularSurvivor :
    ¬ ∃ (k : ℝ) (j : ℂ) (p ν : ℤ),
      FZZCigarExternalBRSTMarkedBranchIncident k j p ν ∧
        ((∫ s in (0 : ℝ)..1, fzzCigarExternalBRSTPlusAngularBranchKernel k j p ν s) ≠ 0 ∨
          (∫ s in (0 : ℝ)..1, fzzCigarExternalBRSTMinusAngularBranchKernel k j p ν s) ≠ 0) := by
  rintro ⟨k, j, p, ν, hincident, hsurvives⟩
  have havg := fzzCigarExternalBRSTAngularBranchAverages_eq_zero_of_incident
    k j p ν hincident
  rcases hsurvives with hplus | hminus
  · exact hplus havg.1
  · exact hminus havg.2

end

end GaloisForLFunctions.RHTower
