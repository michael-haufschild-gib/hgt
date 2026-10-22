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

/-- The centered logarithmic derivative is the original completed logarithmic derivative
rotated by `I`.  This is the differential form of the centered coordinate
`XiC z = xi (1 / 2 + z * I)`. -/
theorem logDeriv_XiC_eq_I_mul_logDeriv_xi_centered (z : ℂ) :
    logDeriv XiC z = I * logDeriv xi (1 / 2 + z * I) := by
  have hinner : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I z := by
    simpa using ((hasDerivAt_id z).mul_const I).const_add (1 / 2 : ℂ)
  have hXiC : HasDerivAt XiC (deriv xi (1 / 2 + z * I) * I) z := by
    have hxi : HasDerivAt xi (deriv xi (1 / 2 + z * I)) (1 / 2 + z * I) :=
      (xi_differentiable _).hasDerivAt
    exact hxi.comp z hinner
  rw [logDeriv_apply, logDeriv_apply, hXiC.deriv, XiC]
  ring

/-- After displacement weighting, the continued Euler positive-shift transgression is exactly
the centered endpoint logarithmic derivative minus its positive transverse predecessor.  Thus a
positive interval average cannot erase an endpoint residue by reparameterization. -/
theorem I_mul_ofReal_mul_xiWardCubicPositiveShiftDivisorTransgression_eq_centered_difference
    (z : ℂ) {eps : ℝ} (heps : eps ≠ 0) :
    I * ((eps : ℂ) * xiWardCubicPositiveShiftDivisorTransgression
      (1 / 2 + z * I) eps) =
      logDeriv XiC z - logDeriv XiC (z + (eps : ℂ) * I) := by
  have htrans : xiWardCubicPositiveShiftDivisorTransgression
      (1 / 2 + z * I) eps =
      (logDeriv xi (1 / 2 + z * I) -
        logDeriv xi (1 / 2 + z * I - (eps : ℂ))) / (eps : ℂ) := by
    rw [xiWardCubicPositiveShiftDivisorTransgression,
      xiFluxShiftDifference, seamFluxCochain, seamFluxCochain]
    ring
  have hcoord : (1 / 2 + z * I - (eps : ℂ) : ℂ) =
      1 / 2 + (z + (eps : ℂ) * I) * I := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [htrans, logDeriv_XiC_eq_I_mul_logDeriv_xi_centered,
    logDeriv_XiC_eq_I_mul_logDeriv_xi_centered, hcoord]
  field_simp [ofReal_ne_zero.mpr heps]

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
