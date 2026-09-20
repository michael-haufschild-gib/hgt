import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTAdaptiveOnShellOccurrenceNoGo

/-!
# FZZ external-BRST modulus: literal physical radial selector

## FZZ-P proof-chain position

The FZZ-P route needs a source-side observable whose physical zero locus is
the radial-momentum wall, before a source-fixed full branch-kernel integral
can be coupled to the mixed Ward identity.  The signed external-BRST branch
charges are already known to be blind to radial momentum.  Their charge-even
log-modulus is the positive survivor: it reconstructs the external radial
label.

This `[BRIDGE]` first evaluates that survivor on the unit physical continuum
`j = -1/2 + i P`.  At every physical level `k > 2`, its imaginary component is
exactly `-2 P / (1 - 2/k)` and therefore vanishes precisely at `P = 0`.  It
then proves the same exact zero locus for the literal Halder--Jafferis continuum
`j = -1/2 - i sqrt(k-2) P`.

This discharges the *local external-BRST source-observable* premise.  It does
not assert that this modulus occurs with a source-fixed phase and nonzero
coefficient in the fully integrated branch kernel.  That integration/coupling
step remains the load-bearing FZZ-P obstacle toward the Ward identity, radial
zero exclusion, and RH.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Charge-even external-BRST log modulus on the physical continuum
`j = -1/2 + i P`. -/
def fzzCigarExternalBRSTPhysicalEvenLogModulusMean
    (k radialMomentum : ℝ) (p ν : ℤ) : ℂ :=
  fzzCigarExternalBRSTEvenLogModulusMean k
    (-(1 : ℂ) / 2 + (radialMomentum : ℂ) * Complex.I) p ν

/-- Exact physical-continuum imaginary component of the charge-even modulus. -/
theorem fzzCigarExternalBRSTPhysicalEvenLogModulusMean_im
    (k radialMomentum : ℝ) (p ν : ℤ) :
    (fzzCigarExternalBRSTPhysicalEvenLogModulusMean k radialMomentum p ν).im =
      -2 * radialMomentum / (1 - 2 / k) := by
  let q : ℝ := 1 - 2 / k
  have hform : fzzCigarExternalBRSTPhysicalEvenLogModulusMean
      k radialMomentum p ν =
      ((1 / q : ℝ) : ℂ) + ((-2 * radialMomentum / q : ℝ) : ℂ) * Complex.I := by
    rw [fzzCigarExternalBRSTPhysicalEvenLogModulusMean,
      fzzCigarExternalBRSTEvenLogModulusMean_eq,
      fzzCigarReplicaRadialDenominator]
    dsimp [q]
    rw [Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_mul]
    push_cast
    ring
  rw [hform]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, add_zero]
  dsimp [q]
  ring

/-- **Local external-BRST radial selection.** At every physical cigar level,
the charge-even log modulus has vanishing imaginary component exactly on the
radial-momentum wall. -/
theorem fzzCigarExternalBRSTPhysicalEvenLogModulusMean_im_eq_zero_iff
    {k : ℝ} (hk : 2 < k) (radialMomentum : ℝ) (p ν : ℤ) :
    (fzzCigarExternalBRSTPhysicalEvenLogModulusMean k radialMomentum p ν).im = 0 ↔
      radialMomentum = 0 := by
  rw [fzzCigarExternalBRSTPhysicalEvenLogModulusMean_im]
  have hk0 : k ≠ 0 := ne_of_gt (lt_trans (by norm_num) hk)
  have hq : 1 - 2 / k ≠ 0 := by
    intro h
    field_simp [hk0] at h
    linarith
  constructor
  · intro h
    have hnum : -2 * radialMomentum = 0 :=
      (div_eq_zero_iff.mp h).resolve_right hq
    linarith
  · rintro rfl
    norm_num

end

end GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- **Literal HJ external-BRST radial selection.** The charge-even log modulus
on the Halder--Jafferis continuum vanishes in its imaginary component exactly
at zero radial momentum. -/
theorem fzzHJExternalBRSTEvenLogModulusMean_im_eq_zero_iff
    {k P : ℝ} (hk : 2 < k) :
    (fzzCigarExternalBRSTEvenLogModulusMean k
      (fzzHJPhysicalRadialLabel k P) 0 1).im = 0 ↔ P = 0 := by
  constructor
  · intro h
    by_contra hP
    exact (fzzHJExternalBRSTEvenLogModulusMean_im_ne_zero hk hP) h
  · rintro rfl
    rw [fzzHJPhysicalRadialLabel,
      fzzCigarExternalBRSTEvenLogModulusMean_eq,
      fzzCigarReplicaRadialDenominator]
    norm_num

end

end RHTower
