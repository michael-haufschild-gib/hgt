import GaloisForLFunctions.RHTower.FZZCigarCouplingInsertionGamma

/-!
# Literal FZZ neutral radial cross-depth coherence

## FZZ-P proof-chain position

The FZZ-P source problem requires a literal complex, non-scalar,
cross-depth coherent contribution to the fully integrated mixed
replica--momentum Ward identity.  Scalar-real plane derivatives and Hermitian
compact reporters are already ruled out; the one-sided radial receiver has
strictly negative imaginary part.

For two independently retained logarithmic coupling depths `u₁,u₂`, this
module constructs the literal neutral radial covariance
`C(u₁,v,p) * conj C(u₂,v,p)`.  Its exact phase is
`exp(-i p (u₁-u₂) / exp v)`, multiplied by the positive Gamma modulus square.
Thus, away from the discrete phase nodes, it has a nonzero imaginary part.
This discharges the source-existence part of the surviving FZZ-P mechanism:
the candidate is genuinely complex and cross-depth, not a scalar reporter.

It does not claim that the physical replica measure supplies a particular
off-diagonal depth pair with the required integrated Ward sign.  Establishing
that source-fixed integration and its coupling to the radial receiver remains
the load-bearing FZZ-P step toward RH.
-/

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Literal neutral radial covariance between two logarithmic coupling depths. -/
def fzzRadialCouplingCrossDepthCoherence (u₁ u₂ v p : ℝ) : ℂ :=
  fzzRadialCouplingCharacteristic u₁ v p *
    (starRingEnd ℂ) (fzzRadialCouplingCharacteristic u₂ v p)

/--
The cross-depth covariance has exactly the relative coupling phase, times the
Gamma factor paired with its conjugate.
-/
theorem fzzRadialCouplingCrossDepthCoherence_eq_phase
    (u₁ u₂ v p : ℝ) :
    fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p =
      Complex.exp (-(((p * (u₁ - u₂) / Real.exp v : ℝ) : ℂ) * Complex.I)) *
        (Complex.Gamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I) *
          (starRingEnd ℂ)
            (Complex.Gamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I))) := by
  unfold fzzRadialCouplingCrossDepthCoherence
  rw [fzzRadialCouplingCharacteristic_eq_gamma,
    fzzRadialCouplingCharacteristic_eq_gamma, map_mul]
  rw [← Complex.exp_conj]
  have hconj :
      (starRingEnd ℂ) (-(((p * u₂ / Real.exp v : ℝ) : ℂ) * Complex.I)) =
        ((p * u₂ / Real.exp v : ℝ) : ℂ) * Complex.I := by
    rw [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj]
  calc
    _ = (Complex.exp (-(↑(p * u₁ / Real.exp v) * Complex.I)) *
        Complex.exp (↑(p * u₂ / Real.exp v) * Complex.I)) *
          (Complex.Gamma (1 + ↑(p / Real.exp v) * Complex.I) *
            (starRingEnd ℂ) (Complex.Gamma (1 + ↑(p / Real.exp v) * Complex.I))) := by
      ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- The same covariance is a unit-circle relative phase times a positive real Gamma modulus. -/
theorem fzzRadialCouplingCrossDepthCoherence_eq_phase_normSq
    (u₁ u₂ v p : ℝ) :
    fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p =
      ((Complex.normSq
        (Complex.Gamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)) : ℝ) : ℂ) *
        Complex.exp (-(((p * (u₁ - u₂) / Real.exp v : ℝ) : ℂ) * Complex.I)) := by
  rw [fzzRadialCouplingCrossDepthCoherence_eq_phase, Complex.mul_conj]
  ring

/-- Exact imaginary component of the literal cross-depth coherence. -/
theorem fzzRadialCouplingCrossDepthCoherence_im
    (u₁ u₂ v p : ℝ) :
    (fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p).im =
      -(Complex.normSq
        (Complex.Gamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)) *
          Real.sin (p * (u₁ - u₂) / Real.exp v)) := by
  rw [fzzRadialCouplingCrossDepthCoherence_eq_phase_normSq]
  have hphase :
      -(((p * (u₁ - u₂) / Real.exp v : ℝ) : ℂ) * Complex.I) =
        ((-(p * (u₁ - u₂) / Real.exp v : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hphase, Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    neg_mul, Real.sin_neg]
  ring

/-- The literal cross-depth covariance never vanishes. -/
theorem fzzRadialCouplingCrossDepthCoherence_ne_zero
    (u₁ u₂ v p : ℝ) :
    fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p ≠ 0 := by
  unfold fzzRadialCouplingCrossDepthCoherence
  apply mul_ne_zero
  · exact fzzRadialCouplingCharacteristic_ne_zero u₁ v p
  · intro h
    apply fzzRadialCouplingCharacteristic_ne_zero u₂ v p
    have hs := congrArg (starRingEnd ℂ) h
    simpa using hs

/--
Outside its explicit phase nodes, the literal two-depth source has nonzero
imaginary part and therefore cannot be a scalar-real or Hermitian reporter.
-/
theorem fzzRadialCouplingCrossDepthCoherence_im_ne_zero
    {u₁ u₂ v p : ℝ}
    (hphase : Real.sin (p * (u₁ - u₂) / Real.exp v) ≠ 0) :
    (fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p).im ≠ 0 := by
  rw [fzzRadialCouplingCrossDepthCoherence_im]
  apply neg_ne_zero.mpr
  apply mul_ne_zero
  · have hgamma : Complex.Gamma
        (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      intro hz
      have hchar := fzzRadialCouplingCharacteristic_ne_zero 0 v p
      rw [fzzRadialCouplingCharacteristic_eq_gamma, hz, mul_zero] at hchar
      exact hchar rfl
    exact (Complex.normSq_pos.mpr hgamma).ne'
  · exact hphase

end

end GaloisForLFunctions.RHTower
