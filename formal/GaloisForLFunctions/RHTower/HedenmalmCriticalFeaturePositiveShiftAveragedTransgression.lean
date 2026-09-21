import GaloisForLFunctions.RHTower.XiWardCubicPositiveShiftAveragedMultiplicity

/-!
# HCF transverse positive-shift noncancellation

The positive-real Euler displacement is vertical in the centered `XiC` coordinate:
`XiC z = xi (1 / 2 + z * I)`.  The source-first displacement average therefore has
the correct transverse geometry for HCF.  This leaf records its exact noncancellation
law: an arbitrary nondegenerate positive displacement interval retains strictly positive
Xi multiplicity at every centered zero.

This is intentionally a local-germ statement.  It closes the fixed-shift predecessor
cancellation obstruction, but does not assert the separate height-local source-square
ceiling needed by the HCF receiver.
-/

open Complex Filter Topology Set MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

/-- A positive-real Euler displacement is a transverse centered-`XiC` displacement. -/
theorem xiWardCubicPositiveRealShift_centered_transverse
    (z : ℂ) (eps : ℝ) :
    (1 / 2 + (z - (eps : ℂ) * I) * I : ℂ) =
      1 / 2 + z * I + (eps : ℂ) := by
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Every centered Xi zero has strictly positive multiplicity after every nondegenerate
positive-real shift average.  Thus no interval average can cancel its transverse residue. -/
theorem xiWardCubicShiftAveragedDivisorMultiplicity_re_pos_of_XiC_zero
    {z : ℂ} (hz : XiC z = 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 < (xiWardCubicShiftAveragedDivisorMultiplicity
      (1 / 2 + z * I) a b).re := by
  have hxi : xi (1 / 2 + z * I) = 0 := by
    simpa only [XiC] using hz
  rw [xiWardCubicShiftAveragedDivisorMultiplicity_eq _ ha hab]
  exact_mod_cast Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hxi)

/-- The transverse averaged divisor landing is nonzero at every centered Xi zero. -/
theorem xiWardCubicShiftAveragedDivisorMultiplicity_ne_zero_of_XiC_zero
    {z : ℂ} (hz : XiC z = 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    xiWardCubicShiftAveragedDivisorMultiplicity (1 / 2 + z * I) a b ≠ 0 := by
  intro hzero
  have hpos := xiWardCubicShiftAveragedDivisorMultiplicity_re_pos_of_XiC_zero
    hz ha hab
  rw [hzero] at hpos
  norm_num at hpos

end

end RHTower
