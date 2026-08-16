import GaloisForLFunctions.RHTower.HurwitzShiftTaylor

/-!
# The archimedean phase identity of the Jonquière channels

Averaging the two boundary phases of the Jonquière expansion against the cosine factor of the
zeta functional equation collapses to a single power of `i` times `sin(π s)`.  This is the exact
mechanism by which the `k`-th regular Jonquière coefficient is `ζ(s-k) i^k / k!`.
-/

open Complex Filter Topology

namespace RHTower

theorem exp_pi_I_half : Complex.exp (↑Real.pi * I / 2) = I := by
  rw [show (↑Real.pi * I / 2 : ℂ) = (↑Real.pi / 2 : ℂ) * I by ring, Complex.exp_mul_I]
  rw [show (↑Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem exp_nat_pi_I_half (k : ℕ) : Complex.exp ((k : ℂ) * (↑Real.pi * I / 2)) = I ^ k := by
  rw [Complex.exp_nat_mul, exp_pi_I_half]

theorem exp_neg_nat_pi_I_half (k : ℕ) :
    Complex.exp (-((k : ℂ) * (↑Real.pi * I / 2))) = (-I) ^ k := by
  rw [Complex.exp_neg, exp_nat_pi_I_half, ← inv_pow, inv_I]

/-- **The Jonquière phase identity.**  The averaged boundary phase times the functional-equation
cosine is `i^k sin(π s)`. -/
theorem jonquiere_phase_identity (s : ℂ) (k : ℕ) :
    (Complex.exp (↑Real.pi * I * (1 - s) / 2)
        + (-1 : ℂ) ^ k * Complex.exp (-↑Real.pi * I * (1 - s) / 2))
      * Complex.cos (↑Real.pi * (s - (k : ℂ)) / 2)
      = I ^ k * Complex.sin (↑Real.pi * s) := by
  set E : ℂ := Complex.exp (I * ↑Real.pi * s / 2) with hE
  have hEne : E ≠ 0 := Complex.exp_ne_zero _
  have hEinv : Complex.exp (-(I * ↑Real.pi * s / 2)) = E⁻¹ := by
    rw [hE, ← Complex.exp_neg]
  have h1 : Complex.exp (↑Real.pi * I * (1 - s) / 2) = I * E⁻¹ := by
    rw [show (↑Real.pi * I * (1 - s) / 2 : ℂ)
      = (↑Real.pi * I / 2) + -(I * ↑Real.pi * s / 2) by ring, Complex.exp_add, exp_pi_I_half,
      hEinv]
  have h2 : Complex.exp (-↑Real.pi * I * (1 - s) / 2) = -I * E := by
    rw [show (-↑Real.pi * I * (1 - s) / 2 : ℂ)
      = -(↑Real.pi * I / 2) + (I * ↑Real.pi * s / 2) by ring, Complex.exp_add, Complex.exp_neg,
      exp_pi_I_half, hE, inv_I]
  have hcos : Complex.cos (↑Real.pi * (s - (k : ℂ)) / 2)
      = (E * (-I) ^ k + E⁻¹ * I ^ k) / 2 := by
    rw [Complex.cos]
    have hA : (↑Real.pi * (s - (k : ℂ)) / 2 : ℂ) * I
        = (I * ↑Real.pi * s / 2) + -((k : ℂ) * (↑Real.pi * I / 2)) := by ring
    have hB : (-(↑Real.pi * (s - (k : ℂ)) / 2 : ℂ)) * I
        = -(I * ↑Real.pi * s / 2) + ((k : ℂ) * (↑Real.pi * I / 2)) := by ring
    rw [hA, hB, Complex.exp_add, Complex.exp_add, exp_neg_nat_pi_I_half, exp_nat_pi_I_half,
      hEinv, ← hE]
  have hsin : Complex.sin (↑Real.pi * s) = (E⁻¹ * E⁻¹ - E * E) * I / 2 := by
    rw [Complex.sin]
    have hA : (↑Real.pi * s : ℂ) * I = (I * ↑Real.pi * s / 2) + (I * ↑Real.pi * s / 2) := by ring
    have hB : (-(↑Real.pi * s : ℂ)) * I
        = -(I * ↑Real.pi * s / 2) + -(I * ↑Real.pi * s / 2) := by ring
    rw [hA, hB, Complex.exp_add, Complex.exp_add, hEinv, ← hE]
  have hnegI : ((-I : ℂ)) ^ k = ((-1 : ℂ) ^ k) * I ^ k := by
    rw [← mul_pow]
    ring
  have hone : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [h1, h2, hcos, hsin, hnegI]
  linear_combination (-(I * I ^ k * E * E / 2)) * hone

/-- **The averaged singular--regular phase.**  This is the card's `(4)`. -/
theorem jonquiere_lead_avg_identity (s : ℂ) (k : ℕ) :
    ((-I) ^ k) * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
        + (-1 : ℂ) ^ k * Complex.exp (-↑Real.pi * I * (1 - s) / 2)) / 2
      = Complex.sin (↑Real.pi * (s + (k : ℂ)) / 2) := by
  set E : ℂ := Complex.exp (I * ↑Real.pi * s / 2) with hE
  have hEinv : Complex.exp (-(I * ↑Real.pi * s / 2)) = E⁻¹ := by
    rw [hE, ← Complex.exp_neg]
  have h1 : Complex.exp (↑Real.pi * I * (1 - s) / 2) = I * E⁻¹ := by
    rw [show (↑Real.pi * I * (1 - s) / 2 : ℂ)
      = (↑Real.pi * I / 2) + -(I * ↑Real.pi * s / 2) by ring, Complex.exp_add, exp_pi_I_half,
      hEinv]
  have h2 : Complex.exp (-↑Real.pi * I * (1 - s) / 2) = -I * E := by
    rw [show (-↑Real.pi * I * (1 - s) / 2 : ℂ)
      = -(↑Real.pi * I / 2) + (I * ↑Real.pi * s / 2) by ring, Complex.exp_add, Complex.exp_neg,
      exp_pi_I_half, hE, inv_I]
  have hsin : Complex.sin (↑Real.pi * (s + (k : ℂ)) / 2)
      = (E⁻¹ * (-I) ^ k - E * I ^ k) * I / 2 := by
    rw [Complex.sin]
    have hA : (↑Real.pi * (s + (k : ℂ)) / 2 : ℂ) * I
        = (I * ↑Real.pi * s / 2) + ((k : ℂ) * (↑Real.pi * I / 2)) := by ring
    have hB : (-(↑Real.pi * (s + (k : ℂ)) / 2 : ℂ)) * I
        = -(I * ↑Real.pi * s / 2) + -((k : ℂ) * (↑Real.pi * I / 2)) := by ring
    rw [hA, hB, Complex.exp_add, Complex.exp_add, exp_nat_pi_I_half, exp_neg_nat_pi_I_half,
      hEinv, ← hE]
  have hnegI : ((-I : ℂ)) ^ k = ((-1 : ℂ) ^ k) * I ^ k := by
    rw [← mul_pow]
    ring
  have hone : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [h1, h2, hsin, hnegI]
  linear_combination (-(I ^ k * I * E / 2)) * hone

end RHTower
