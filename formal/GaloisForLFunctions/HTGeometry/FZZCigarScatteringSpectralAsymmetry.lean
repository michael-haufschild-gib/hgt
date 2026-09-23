import GaloisForLFunctions.RHTower.BoseMellinCoordinate
import GaloisForLFunctions.HTGeometry.CauchyKernelFourier

/-!
# FZZ-cigar scattering spectral asymmetry

This file isolates a black-hole source that is absent from a generic KMS system.  In the
supersymmetric `SL(2,R)/U(1)` cigar, the non-holomorphic part of the twisted elliptic genus is
the mismatch between right-moving bosonic and fermionic continuum densities.  Ashok--Troost,
arXiv:1101.1059, equation (4.10), derive that mismatch from the exact reflection amplitudes:

`Delta rho(p) = (2 pi)⁻¹ ((i p - m)⁻¹ - (i p + m)⁻¹)`.

For positive charge it is the negative Cauchy density `-m / (pi (p²+m²))`.  Fourier transform
in radial momentum therefore gives `-exp(-m |t|)`.  The positive reflection deficit over the
unit charge tower is consequently

`sum_{m >= 1} exp(-m t) = 1 / (exp t - 1)`.

Its Mellin transform is `Gamma(s) zeta(s)`.  Here the Bose kernel is not postulated from generic
thermality: it is reconstructed from the exact cigar reflection-phase asymmetry of long strings.

Lean proves the exact rational reflection law, positivity, its Cauchy-density Fourier transform,
the charge-tower sum, and the Mellin identity.
-/

open Complex MeasureTheory Set

namespace HTGeometry

noncomputable section

/-- Exact right-moving boson--fermion continuum-density mismatch from the cigar reflection
amplitudes.  `m` is the asymptotic right-moving charge and `p` radial momentum. -/
def fzzCigarRightMovingSpectralAsymmetry (m p : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ((Complex.I * (p : ℂ) - (m : ℂ))⁻¹ -
      (Complex.I * (p : ℂ) + (m : ℂ))⁻¹)

/-- The exact reflection-amplitude asymmetry is a real negative Cauchy density. -/
theorem fzzCigarRightMovingSpectralAsymmetry_eq (m p : ℝ) :
    fzzCigarRightMovingSpectralAsymmetry m p =
      (((-m / (Real.pi * (p ^ (2 : ℕ) + m ^ (2 : ℕ)))) : ℝ) : ℂ) := by
  by_cases hm : m = 0
  · subst m
    simp [fzzCigarRightMovingSpectralAsymmetry]
  have hminus : Complex.I * (p : ℂ) - (m : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact hm hre
  have hplus : Complex.I * (p : ℂ) + (m : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact hm hre
  have hden : p ^ (2 : ℕ) + m ^ (2 : ℕ) ≠ 0 := by positivity
  have hprod :
      (Complex.I * (p : ℂ) - (m : ℂ)) *
          (Complex.I * (p : ℂ) + (m : ℂ)) =
        -(((p ^ (2 : ℕ) + m ^ (2 : ℕ)) : ℝ) : ℂ) := by
    calc
      (Complex.I * (p : ℂ) - (m : ℂ)) *
            (Complex.I * (p : ℂ) + (m : ℂ)) =
          (Complex.I * (p : ℂ)) ^ (2 : ℕ) - (m : ℂ) ^ (2 : ℕ) := by ring
      _ = -(((p ^ (2 : ℕ) + m ^ (2 : ℕ)) : ℝ) : ℂ) := by
        rw [mul_pow, Complex.I_sq]
        push_cast
        ring
  rw [fzzCigarRightMovingSpectralAsymmetry]
  push_cast
  field_simp
  rw [show
    2 * (m : ℂ) * (Complex.I * (p : ℂ) - (m : ℂ)) *
        (Complex.I * (p : ℂ) + (m : ℂ)) =
      2 * (m : ℂ) *
        ((Complex.I * (p : ℂ) - (m : ℂ)) *
          (Complex.I * (p : ℂ) + (m : ℂ))) by ring]
  rw [hprod]
  push_cast
  have hdenC : (p : ℂ) ^ (2 : ℕ) + (m : ℂ) ^ (2 : ℕ) ≠ 0 := by
    exact_mod_cast hden
  rw [show
    -(2 * (m : ℂ) * -((p : ℂ) ^ (2 : ℕ) + (m : ℂ) ^ (2 : ℕ)) /
        ((p : ℂ) ^ (2 : ℕ) + (m : ℂ) ^ (2 : ℕ))) =
      ((m : ℂ) * 2 * ((p : ℂ) ^ (2 : ℕ) + (m : ℂ) ^ (2 : ℕ))) /
        ((p : ℂ) ^ (2 : ℕ) + (m : ℂ) ^ (2 : ℕ)) by ring]
  apply (eq_div_iff hdenC).2
  ring

/-- Positive reflection deficit, the sign-reversal of the continuum spectral asymmetry. -/
def fzzCigarReflectionDeficit (m p : ℝ) : ℝ :=
  m / (Real.pi * (p ^ (2 : ℕ) + m ^ (2 : ℕ)))

/-- Every positive-charge cigar reflection deficit is strictly positive at every real radial
momentum. -/
theorem fzzCigarReflectionDeficit_pos {m p : ℝ} (hm : 0 < m) :
    0 < fzzCigarReflectionDeficit m p := by
  rw [fzzCigarReflectionDeficit]
  positivity

/-- Exact radial-momentum transform of the positive cigar reflection deficit. -/
theorem integral_fzzCigarReflectionDeficit_mul_cexp_neg
    {m : ℝ} (hm : 0 < m) (t : ℝ) :
    (∫ p : ℝ, ((fzzCigarReflectionDeficit m p : ℝ) : ℂ) *
      Complex.exp (((-(t * p) : ℝ) : ℂ) * I)) =
        ((Real.exp (-(m * |t|)) : ℝ) : ℂ) := by
  have h :=
    GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq_mul_cexp_neg hm t
  simp_rw [fzzCigarReflectionDeficit]
  have hfactor :
      (∫ p : ℝ, (((m / (Real.pi * (p ^ (2 : ℕ) + m ^ (2 : ℕ)))) : ℝ) : ℂ) *
        Complex.exp (((-(t * p) : ℝ) : ℂ) * I)) =
        (((m / Real.pi : ℝ) : ℂ) *
          ∫ p : ℝ, (((m ^ (2 : ℕ) + p ^ (2 : ℕ) : ℝ) : ℂ)⁻¹ *
            Complex.exp (((-(t * p) : ℝ) : ℂ) * I))) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    push_cast
    rw [show (p : ℂ) ^ (2 : ℕ) + (m : ℂ) ^ (2 : ℕ) =
      (m : ℂ) ^ (2 : ℕ) + (p : ℂ) ^ (2 : ℕ) by ring]
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [hfactor, h]
  push_cast
  have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hm)
  have hpiC : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (m : ℂ) / (Real.pi : ℂ) *
      ((Real.pi : ℂ) / (m : ℂ) *
        Complex.exp (-((m : ℂ) * ((|t| : ℝ) : ℂ)))) =
      ((m : ℂ) / (m : ℂ)) * ((Real.pi : ℂ) / (Real.pi : ℂ)) *
        Complex.exp (-((m : ℂ) * ((|t| : ℝ) : ℂ))) by ring]
  rw [div_self hmC, div_self hpiC]
  simp

/-- Radial-delay contribution of the `n+1` charge sector.  It is the Fourier transform of the
positive Cauchy reflection deficit, restricted to positive radial delay. -/
def fzzCigarChargeDelay (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-((n : ℝ) + 1) * t)

/-- Each positive-charge delay is exactly the Fourier image of its reflection deficit. -/
theorem fzzCigarChargeDelay_eq_reflectionDeficitFourier
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ p : ℝ, ((fzzCigarReflectionDeficit ((n : ℝ) + 1) p : ℝ) : ℂ) *
      Complex.exp (((-(t * p) : ℝ) : ℂ) * I)) =
        ((fzzCigarChargeDelay n t : ℝ) : ℂ) := by
  unfold fzzCigarChargeDelay
  have h := integral_fzzCigarReflectionDeficit_mul_cexp_neg
    (m := (n : ℝ) + 1) (by positivity) t
  rw [abs_of_pos ht] at h
  rw [h]
  congr 2
  ring

/-- Total positive long-string delay deficit over the unit charge tower. -/
def fzzCigarContinuumDelay (t : ℝ) : ℝ :=
  (Real.exp t - 1)⁻¹

/-- Exact charge decomposition of the long-string reflection-delay deficit. -/
theorem hasSum_fzzCigarChargeDelay {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => fzzCigarChargeDelay n t) (fzzCigarContinuumDelay t) := by
  simpa [fzzCigarChargeDelay, fzzCigarContinuumDelay] using
    RHTower.hasSum_boseKernel ht

/-- Mellin moment of the positive cigar continuum delay. -/
def fzzCigarContinuumMellin (a : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ a * fzzCigarContinuumDelay t

/-- Exact cigar scattering bridge: its positive-delay Mellin moment is the Gamma--zeta product.
The Riemann zeta divisor therefore comes from the long-string reflection asymmetry after removing
the zero-free Gamma normalization. -/
theorem ofReal_fzzCigarContinuumMellin {a : ℝ} (ha : 0 < a) :
    ((fzzCigarContinuumMellin a : ℝ) : ℂ) =
      Complex.Gamma (((a + 1 : ℝ) : ℂ)) *
        riemannZeta (((a + 1 : ℝ) : ℂ)) := by
  simpa [fzzCigarContinuumMellin, fzzCigarContinuumDelay, RHTower.boseMellin,
    div_eq_mul_inv] using RHTower.ofReal_boseMellin ha

end

end HTGeometry
