import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusUnitHardyGramRigidity
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardySaturation

/-!
# Source Julia--Pythagoras identification

P-G38 turns the two-sided Möbius aperture into a unit-vector curve with a
strict normalized Hardy Gram.  The missing geometric interpretation is exact:
the complementary coordinate is the same half-plane Cayley factor used by the
source-canonical Xi Ward--Hardy phase.

For half-density coordinates `x=1+2u` and `y=1+2v`, the source overlap is
`2 sqrt(xy)/(x+y)` and the Cayley discrepancy is `(x-y)/(x+y)`.  Their squares
sum to one.  Thus normalized source loss and Xi Ward contractivity are not two
independent phenomena; they are the two legs of one Julia cell.

This also closes a tempting false route.  Unit normalization cannot force RH:
it moves exceptional displacement into a nonzero Cayley coordinate.  A genuine
producer must force that coordinate to vanish, equivalently force source
aperture saturation, rather than derive contractivity already built into the
cell.
-/

open Complex

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Cayley discrepancy between two source apertures in positive half-density coordinates. -/
def mobiusCriticalTwoSidedCayleyDiscrepancy (u v : ℝ) : ℝ :=
  ((1 + 2 * u) - (1 + 2 * v)) /
    ((1 + 2 * u) + (1 + 2 * v))

/-- Simplified physical-aperture formula for the Cayley discrepancy. -/
theorem mobiusCriticalTwoSidedCayleyDiscrepancy_eq
    {u v : ℝ} :
    mobiusCriticalTwoSidedCayleyDiscrepancy u v =
      (u - v) / (1 + u + v) := by
  by_cases hden : 1 + u + v = 0
  · have hden2 : (1 + 2 * u) + (1 + 2 * v) = 0 := by linarith
    rw [mobiusCriticalTwoSidedCayleyDiscrepancy, hden, hden2]
    simp
  · rw [mobiusCriticalTwoSidedCayleyDiscrepancy]
    have hden2 : (1 + 2 * u) + (1 + 2 * v) ≠ 0 := by
      intro hzero
      apply hden
      linarith
    field_simp [hden, hden2]
    ring

/-- The source aperture discrepancy is literally one positive-real
`xiWardHalfPlaneCayleyFactor`. -/
theorem xiWardHalfPlaneCayleyFactor_sourceApertures
    (u v : ℝ) :
    xiWardHalfPlaneCayleyFactor
        ((((1 + 2 * u) / 2 : ℝ) : ℂ))
        ((((1 + 2 * u) / 2 : ℝ) : ℂ))
        (1 + 2 * v) =
      (mobiusCriticalTwoSidedCayleyDiscrepancy u v : ℂ) := by
  rw [xiWardHalfPlaneCayleyFactor,
    mobiusCriticalTwoSidedCayleyDiscrepancy]
  push_cast
  ring

/-- **P-G39 source Julia--Pythagoras law.** Normalized Hardy overlap and
Cayley discrepancy are complementary orthogonal coordinates. -/
theorem sq_mobiusCriticalTwoSidedCayleyDiscrepancy_add_sq_unitHardyGram
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    mobiusCriticalTwoSidedCayleyDiscrepancy u v ^ (2 : ℕ) +
      mobiusCriticalTwoSidedUnitHardyGram u v ^ (2 : ℕ) = 1 := by
  have hxu : 0 ≤ 1 + 2 * u := by linarith
  have hxv : 0 ≤ 1 + 2 * v := by linarith
  have hsu := Real.sq_sqrt hxu
  have hsv := Real.sq_sqrt hxv
  have hden : 1 + u + v ≠ 0 := by linarith
  rw [mobiusCriticalTwoSidedCayleyDiscrepancy_eq,
    mobiusCriticalTwoSidedUnitHardyGram]
  field_simp [hden]
  ring_nf at hsu hsv ⊢
  nlinarith

/-- Normalized Hardy loss in squared overlap is exactly Cayley energy. -/
theorem one_sub_sq_unitHardyGram_eq_sq_cayleyDiscrepancy
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    1 - mobiusCriticalTwoSidedUnitHardyGram u v ^ (2 : ℕ) =
      mobiusCriticalTwoSidedCayleyDiscrepancy u v ^ (2 : ℕ) := by
  nlinarith [
    sq_mobiusCriticalTwoSidedCayleyDiscrepancy_add_sq_unitHardyGram hu hv]

/-- Source Hardy saturation is equivalently vanishing of the exact Xi-Ward
Cayley aperture factor. -/
theorem mobiusCriticalTwoSidedUnitHardyGram_eq_one_iff_cayleyFactor_eq_zero
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    mobiusCriticalTwoSidedUnitHardyGram u v = 1 ↔
      xiWardHalfPlaneCayleyFactor
        ((((1 + 2 * u) / 2 : ℝ) : ℂ))
        ((((1 + 2 * u) / 2 : ℝ) : ℂ))
        (1 + 2 * v) = 0 := by
  rw [mobiusCriticalTwoSidedUnitHardyGram_eq_one_iff hu hv,
    xiWardHalfPlaneCayleyFactor_sourceApertures]
  constructor
  · intro huv
    subst v
    rw [mobiusCriticalTwoSidedCayleyDiscrepancy]
    simp
  · intro hzero
    have hre := congrArg Complex.re hzero
    simp only [ofReal_re, zero_re] at hre
    rw [mobiusCriticalTwoSidedCayleyDiscrepancy_eq] at hre
    have hden : 1 + u + v ≠ 0 := by linarith
    have hdiff := (div_eq_zero_iff.mp hre).resolve_right hden
    linarith

end

end RHTower.HedenmalmThetaSource
