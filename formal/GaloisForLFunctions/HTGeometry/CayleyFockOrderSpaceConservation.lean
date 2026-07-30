import GaloisForLFunctions.RHTower.WCoordinate
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Cayley--Fock order-space conservation

A Cayley mode `a = 1 + b` does not spread arbitrarily through factorially normalized derivative
orders. Its exact channel profile is a Poisson packet. The packet center is

`d x`, where `d = ‖b‖²`,

and its total exponential mass is

`exp (κ x)`, where `κ = ‖1 + b‖² - 1`.

For a conjugate pair, the adjacent-order exterior determinant removes the rotating phase without
removing either invariant. Its channel profile is the same Poisson packet with a fixed negative
sign, and summing over every order returns the exact exponential mass.

For the Riemann Cayley coordinate, `b = (ρ - 1)⁻¹`. Then

`d = |ρ - 1|⁻²` and `κ = (2 Re ρ - 1) d`.

Consequently the packet center and growth exponent reconstruct `ρ` up to conjugation. These laws
are source-independent and apply to any coherent exponential mode.
-/

open Complex Real
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Derivative-order drift of a coherent Cayley mode. -/
def cayleyFockDrift (b : ℂ) : ℝ := ‖b‖ ^ 2

/-- Total Fock growth exponent of the Cayley mode `1 + b`. -/
def cayleyFockExponent (b : ℂ) : ℝ := ‖1 + b‖ ^ 2 - 1

/-- Real Poisson weight, algebraically meaningful for every real parameter. -/
def poissonOrderWeight (lam : ℝ) (r : ℕ) : ℝ :=
  Real.exp (-lam) * lam ^ r / r.factorial

/-- The order-`r` coherent exponential jet. -/
def coherentExponentialJet (c b : ℂ) (x : ℝ) (r : ℕ) : ℂ :=
  c * b ^ r * Complex.exp (b * (x : ℂ))

/-- The Cayley growth exponent splits into radial drift and linear displacement. -/
theorem cayleyFockExponent_eq (b : ℂ) :
    cayleyFockExponent b = 2 * b.re + cayleyFockDrift b := by
  rw [cayleyFockExponent, cayleyFockDrift, Complex.sq_norm,
    Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im]
  ring

/-- Exact squared norm of one coherent exponential jet. -/
theorem norm_coherentExponentialJet_sq (c b : ℂ) (x : ℝ) (r : ℕ) :
    ‖coherentExponentialJet c b x r‖ ^ 2 =
      ‖c‖ ^ 2 * (‖b‖ ^ 2) ^ r * Real.exp (2 * b.re * x) := by
  rw [coherentExponentialJet, norm_mul, norm_mul, norm_pow, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  rw [mul_pow]
  ring_nf
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- **Poisson order-space conservation.** Factorially normalized derivative energy is exactly a
Poisson packet of mean `d x`, multiplied by the total Cayley instability `exp (κ x)`. -/
theorem coherentExponentialJet_poisson_conservation
    (c b : ℂ) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial * ‖coherentExponentialJet c b x r‖ ^ 2 =
      ‖c‖ ^ 2 * Real.exp (cayleyFockExponent b * x) *
        poissonOrderWeight (cayleyFockDrift b * x) r := by
  rw [norm_coherentExponentialJet_sq, poissonOrderWeight, cayleyFockExponent_eq,
    cayleyFockDrift]
  rw [show (‖b‖ ^ 2 * x) ^ r = (‖b‖ ^ 2) ^ r * x ^ r by
    rw [mul_pow]]
  have hexp :
      Real.exp (2 * b.re * x) =
        Real.exp ((2 * b.re + ‖b‖ ^ 2) * x) *
          Real.exp (-(‖b‖ ^ 2 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show
    x ^ r / r.factorial *
        (‖c‖ ^ 2 * (‖b‖ ^ 2) ^ r * Real.exp (2 * b.re * x)) =
      ‖c‖ ^ 2 * (‖b‖ ^ 2) ^ r * x ^ r / r.factorial *
        Real.exp (2 * b.re * x) by ring]
  rw [hexp]
  ring

/-- Canonical time of a nonzero coherent generator. It is the
unique clock that normalizes derivative-order drift to `tau`. -/
def coherentGeneratorObservationTime
    (b : ℂ) (tau : ℝ) : ℝ :=
  tau / Complex.normSq b

/-- Universal transverse rate in the reciprocal generator
coordinate. -/
def coherentGeneratorDualRate (b : ℂ) : ℝ :=
  2 * (b⁻¹).re + 1

/-- Canonical generator time normalizes the Poisson drift exactly. -/
theorem coherentGenerator_drift_observationTime
    (b : ℂ) (tau : ℝ) (hb : b ≠ 0) :
    cayleyFockDrift b * coherentGeneratorObservationTime b tau =
      tau := by
  rw [cayleyFockDrift, Complex.sq_norm,
    coherentGeneratorObservationTime]
  field_simp [ne_of_gt (Complex.normSq_pos.mpr hb)]

/-- Poisson drift normalization uniquely forces the canonical
generator clock. -/
theorem coherentGenerator_observationTime_unique
    (b : ℂ) (tau x : ℝ) (hb : b ≠ 0)
    (hx : cayleyFockDrift b * x = tau) :
    x = coherentGeneratorObservationTime b tau := by
  rw [coherentGeneratorObservationTime, ← hx, cayleyFockDrift,
    Complex.sq_norm]
  exact (mul_div_cancel_left₀ x
    (ne_of_gt (Complex.normSq_pos.mpr hb))).symm

/-- **Coherent generator duality.** The clock forced by order
normalization converts a generator into its conjugate reciprocal. -/
theorem coherentGenerator_duality
    (b : ℂ) (tau : ℝ) (hb : b ≠ 0) :
    b * (coherentGeneratorObservationTime b tau : ℂ) =
      (starRingEnd ℂ) (b⁻¹) * (tau : ℂ) := by
  rw [coherentGeneratorObservationTime, Complex.inv_def]
  have hden : Complex.normSq b ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hb)
  have hdenC : (Complex.normSq b : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  push_cast
  rw [map_mul]
  simp
  field_simp [hdenC]

/-- Total coherent growth at canonical time is measured by the
universal reciprocal-generator horizon. -/
theorem coherentGenerator_exponent_observationTime
    (b : ℂ) (tau : ℝ) (hb : b ≠ 0) :
    cayleyFockExponent b * coherentGeneratorObservationTime b tau =
      coherentGeneratorDualRate b * tau := by
  rw [cayleyFockExponent_eq, cayleyFockDrift, Complex.sq_norm,
    coherentGeneratorObservationTime, coherentGeneratorDualRate,
    Complex.inv_re]
  have hden : Complex.normSq b ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hb)
  field_simp

/-- Fock growth factors into order drift and reciprocal-generator
orientation. -/
theorem cayleyFockExponent_eq_drift_mul_dualRate
    (b : ℂ) (hb : b ≠ 0) :
    cayleyFockExponent b =
      cayleyFockDrift b * coherentGeneratorDualRate b := by
  rw [cayleyFockExponent_eq, cayleyFockDrift,
    coherentGeneratorDualRate, Complex.inv_re,
    Complex.sq_norm]
  have hden : Complex.normSq b ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hb)
  field_simp

/-- Reciprocal-generator neutrality is exactly vanishing total Fock
growth. -/
theorem coherentGeneratorDualRate_eq_zero_iff_fockExponent_eq_zero
    (b : ℂ) (hb : b ≠ 0) :
    coherentGeneratorDualRate b = 0 ↔
      cayleyFockExponent b = 0 := by
  have htime :
      coherentGeneratorObservationTime b 1 ≠ 0 := by
    rw [coherentGeneratorObservationTime]
    exact div_ne_zero one_ne_zero
      (ne_of_gt (Complex.normSq_pos.mpr hb))
  have hlink :=
    coherentGenerator_exponent_observationTime b 1 hb
  simp only [mul_one] at hlink
  constructor
  · intro hrate
    rw [hrate] at hlink
    exact (mul_eq_zero.mp hlink).resolve_right htime
  · intro hexp
    rw [hexp, zero_mul] at hlink
    exact hlink.symm

/-- Fock neutrality is exactly the unit circle of the shifted
generator `1 + b`. -/
theorem cayleyFockExponent_eq_zero_iff_shift_norm_one
    (b : ℂ) :
    cayleyFockExponent b = 0 ↔ ‖1 + b‖ = 1 := by
  rw [cayleyFockExponent]
  constructor
  · intro h
    have hn : 0 ≤ ‖1 + b‖ := norm_nonneg _
    nlinarith
  · intro h
    rw [h]
    norm_num

/-- Universal line--circle equivalence: the neutral line in reciprocal
generator space is the shifted-generator unit circle. -/
theorem coherentGeneratorDualRate_eq_zero_iff_shift_norm_one
    (b : ℂ) (hb : b ≠ 0) :
    coherentGeneratorDualRate b = 0 ↔ ‖1 + b‖ = 1 := by
  rw [coherentGeneratorDualRate_eq_zero_iff_fockExponent_eq_zero b hb,
    cayleyFockExponent_eq_zero_iff_shift_norm_one]

/-- **Universal generator-horizon conservation.** At the uniquely
Poisson-normalized clock, every coherent exponential has a
height-free packet whose sole exponential datum is reciprocal
generator orientation. -/
theorem coherentGenerator_poisson_conservation
    (c b : ℂ) (tau : ℝ) (r : ℕ) (hb : b ≠ 0) :
    coherentGeneratorObservationTime b tau ^ r / r.factorial *
        ‖coherentExponentialJet c b
          (coherentGeneratorObservationTime b tau) r‖ ^ 2 =
      ‖c‖ ^ 2 *
        Real.exp (coherentGeneratorDualRate b * tau) *
          poissonOrderWeight tau r := by
  rw [coherentExponentialJet_poisson_conservation]
  rw [coherentGenerator_exponent_observationTime b tau hb,
    coherentGenerator_drift_observationTime b tau hb]

/-- A two-mode coherent jet. -/
def twoModeCoherentJet (c d b e : ℂ) (x : ℝ) (r : ℕ) : ℂ :=
  c * b ^ r * Complex.exp (b * (x : ℂ)) +
    d * e ^ r * Complex.exp (e * (x : ℂ))

/-- Adjacent-order exterior curvature of a two-mode jet. -/
def twoModeCoherentExterior (c d b e : ℂ) (x : ℝ) (r : ℕ) : ℂ :=
  twoModeCoherentJet c d b e x r * twoModeCoherentJet c d b e x (r + 2) -
    twoModeCoherentJet c d b e x (r + 1) ^ 2

/-- The exterior curvature deletes both diagonal modes and retains exactly their squared
separation. -/
theorem twoModeCoherentExterior_eq
    (c d b e : ℂ) (x : ℝ) (r : ℕ) :
    twoModeCoherentExterior c d b e x r =
      c * d * (b - e) ^ 2 * (b * e) ^ r *
        Complex.exp ((b + e) * (x : ℂ)) := by
  rw [twoModeCoherentExterior, twoModeCoherentJet, twoModeCoherentJet,
    twoModeCoherentJet]
  rw [pow_add, pow_add, pow_add, pow_add]
  norm_num
  rw [mul_pow]
  rw [show
    Complex.exp ((b + e) * (x : ℂ)) =
      Complex.exp (b * (x : ℂ)) * Complex.exp (e * (x : ℂ)) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  ring

/-- A conjugate pair has a real, nonpositive exterior curvature. -/
theorem twoModeCoherentExterior_conj_eq
    (m : ℝ) (b : ℂ) (x : ℝ) (r : ℕ) :
    twoModeCoherentExterior (m : ℂ) (m : ℂ) b (starRingEnd ℂ b) x r =
      ((m ^ 2 : ℝ) : ℂ) * (b - (starRingEnd ℂ b)) ^ 2 *
        ((‖b‖ ^ (2 * r) * Real.exp (2 * b.re * x) : ℝ) : ℂ) := by
  rw [twoModeCoherentExterior_eq]
  rw [show b * (starRingEnd ℂ b) = ((‖b‖ ^ 2 : ℝ) : ℂ) by
    rw [Complex.mul_conj, Complex.sq_norm]]
  have hexp :
      Complex.exp ((b + (starRingEnd ℂ b)) * (x : ℂ)) =
        ((Real.exp (2 * b.re * x) : ℝ) : ℂ) := by
    rw [Complex.add_conj]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp]
  rw [show (m : ℂ) * (m : ℂ) = (((m ^ 2 : ℝ) : ℂ)) by
    push_cast
    ring]
  rw [show ((((‖b‖ ^ 2 : ℝ) : ℂ)) ^ r) =
      (((‖b‖ ^ (2 * r) : ℝ) : ℂ)) by
    rw [← Complex.ofReal_pow, pow_mul]]
  rw [Complex.ofReal_mul]
  ring

/-- The phase-free conjugate exterior has the same Poisson packet as the one-mode energy, with
fixed negative sign removed. -/
theorem neg_re_twoModeCoherentExterior_conj_poisson_conservation
    (m : ℝ) (b : ℂ) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial *
        (-(twoModeCoherentExterior (m : ℂ) (m : ℂ) b
          (starRingEnd ℂ b) x r).re) =
      4 * m ^ 2 * b.im ^ 2 *
        Real.exp (cayleyFockExponent b * x) *
          poissonOrderWeight (cayleyFockDrift b * x) r := by
  rw [twoModeCoherentExterior_conj_eq]
  rw [show (b - (starRingEnd ℂ b)) ^ 2 =
      (((-4 * b.im ^ 2 : ℝ) : ℂ)) by
    rw [Complex.sub_conj, mul_pow, Complex.I_sq]
    push_cast
    ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  rw [poissonOrderWeight, cayleyFockExponent_eq, cayleyFockDrift]
  rw [show (‖b‖ ^ 2 * x) ^ r = (‖b‖ ^ 2) ^ r * x ^ r by
    rw [mul_pow]]
  have hexp :
      Real.exp (2 * b.re * x) =
        Real.exp ((2 * b.re + ‖b‖ ^ 2) * x) *
          Real.exp (-(‖b‖ ^ 2 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Summing the complete exterior order tower returns the exact signed exponential instability. -/
theorem tsum_twoModeCoherentExterior_conj
    (m : ℝ) (b : ℂ) (x : ℝ) :
    ∑' r : ℕ, ((x : ℂ) ^ r / r.factorial) *
        twoModeCoherentExterior (m : ℂ) (m : ℂ) b
          (starRingEnd ℂ b) x r =
      ((m ^ 2 : ℝ) : ℂ) * (b - (starRingEnd ℂ b)) ^ 2 *
        Complex.exp ((cayleyFockExponent b * x : ℝ) : ℂ) := by
  have hsum :=
    (NormedSpace.expSeries_div_hasSum_exp
      (((‖b‖ ^ 2 * x : ℝ) : ℂ))).mul_left
        (((m ^ 2 : ℝ) : ℂ) * (b - (starRingEnd ℂ b)) ^ 2 *
          Complex.exp ((2 * b.re * x : ℝ) : ℂ))
  rw [show
    (fun r : ℕ => (((m ^ 2 : ℝ) : ℂ) *
        (b - (starRingEnd ℂ b)) ^ 2 *
        Complex.exp ((2 * b.re * x : ℝ) : ℂ)) *
          (((‖b‖ ^ 2 * x : ℝ) : ℂ) ^ r / r.factorial)) =
      (fun r : ℕ => ((x : ℂ) ^ r / r.factorial) *
        twoModeCoherentExterior (m : ℂ) (m : ℂ) b
          (starRingEnd ℂ b) x r) by
    funext r
    rw [twoModeCoherentExterior_conj_eq]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow]
    push_cast
    rw [mul_pow, pow_mul]
    ring] at hsum
  rw [hsum.tsum_eq]
  rw [← Complex.exp_eq_exp_ℂ]
  have hexp :
      Complex.exp ((2 * b.re * x : ℝ) : ℂ) *
          Complex.exp ((‖b‖ ^ 2 * x : ℝ) : ℂ) =
        Complex.exp ((cayleyFockExponent b * x : ℝ) : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    rw [cayleyFockExponent_eq, cayleyFockDrift]
    push_cast
    ring
  calc
    ((m ^ 2 : ℝ) : ℂ) * (b - (starRingEnd ℂ b)) ^ 2 *
          Complex.exp ((2 * b.re * x : ℝ) : ℂ) *
          Complex.exp ((‖b‖ ^ 2 * x : ℝ) : ℂ) =
        ((m ^ 2 : ℝ) : ℂ) * (b - (starRingEnd ℂ b)) ^ 2 *
          (Complex.exp ((2 * b.re * x : ℝ) : ℂ) *
            Complex.exp ((‖b‖ ^ 2 * x : ℝ) : ℂ)) := by ring
    _ = ((m ^ 2 : ℝ) : ℂ) * (b - (starRingEnd ℂ b)) ^ 2 *
          Complex.exp ((cayleyFockExponent b * x : ℝ) : ℂ) := by
      rw [hexp]

/-- Riemann-coordinate exponent: transverse displacement times inverse-square distance from the
reflection point. -/
theorem cayleyFockExponent_of_rho
    {rho : ℂ} (h : rho ≠ 1) :
    cayleyFockExponent ((rho - 1)⁻¹) =
      (2 * rho.re - 1) * cayleyFockDrift ((rho - 1)⁻¹) := by
  rw [cayleyFockExponent_eq]
  rw [cayleyFockDrift, Complex.sq_norm, Complex.normSq_inv]
  rw [Complex.inv_re]
  simp only [Complex.sub_re, Complex.one_re]
  have hden : Complex.normSq (rho - 1) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (sub_ne_zero.mpr h))
  field_simp [hden]
  ring

/-- Riemann-coordinate packet drift. -/
theorem cayleyFockDrift_of_rho
    {rho : ℂ} (_h : rho ≠ 1) :
    cayleyFockDrift ((rho - 1)⁻¹) =
      (Complex.normSq (rho - 1))⁻¹ := by
  rw [cayleyFockDrift, Complex.sq_norm, Complex.normSq_inv]

/-- Ridge position and exponential growth recover the real part of the spectral point. -/
theorem rho_re_from_cayleyFock_ridge
    {rho : ℂ} (h : rho ≠ 1) :
    rho.re =
      1 / 2 * (1 +
        cayleyFockExponent ((rho - 1)⁻¹) /
          cayleyFockDrift ((rho - 1)⁻¹)) := by
  rw [cayleyFockExponent_of_rho h]
  have hd : cayleyFockDrift ((rho - 1)⁻¹) ≠ 0 := by
    exact pow_ne_zero 2
      (norm_ne_zero_iff.mpr (inv_ne_zero (sub_ne_zero.mpr h)))
  field_simp [hd]
  ring

/-- Ridge position and exponential growth recover the squared height of the spectral point. -/
theorem rho_im_sq_from_cayleyFock_ridge
    {rho : ℂ} (h : rho ≠ 1) :
    rho.im ^ 2 =
      1 / cayleyFockDrift ((rho - 1)⁻¹) -
        1 / 4 * (1 -
          cayleyFockExponent ((rho - 1)⁻¹) /
            cayleyFockDrift ((rho - 1)⁻¹)) ^ 2 := by
  let d := cayleyFockDrift ((rho - 1)⁻¹)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact pow_ne_zero 2
      (norm_ne_zero_iff.mpr (inv_ne_zero (sub_ne_zero.mpr h)))
  have hnorm :
      d⁻¹ = (rho.re - 1) ^ 2 + rho.im ^ 2 := by
    change (cayleyFockDrift ((rho - 1)⁻¹))⁻¹ =
      (rho.re - 1) ^ 2 + rho.im ^ 2
    rw [cayleyFockDrift_of_rho h, inv_inv, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero]
    ring
  have hk :=
    cayleyFockExponent_of_rho h
  change cayleyFockExponent ((rho - 1)⁻¹) = (2 * rho.re - 1) * d at hk
  have hratio :
      cayleyFockExponent ((rho - 1)⁻¹) / d =
        2 * rho.re - 1 := by
    rw [hk]
    field_simp
  change rho.im ^ 2 =
    1 / d - 1 / 4 *
      (1 - cayleyFockExponent ((rho - 1)⁻¹) / d) ^ 2
  rw [hratio, one_div, hnorm]
  ring

end

end GaloisForLFunctions.HTGeometry
