import GaloisForLFunctions.RHTower.HeatMultiplierReal
import GaloisForLFunctions.HTGeometry.RiemannGaussian.GaussianHarnack

/-!
# Strict Harnack comparison for the theta heat multiplier

The Poisson representation of the existing theta multiplier transfers Gaussian
Harnack comparison to the full lattice sum. The inequality is strict: equality
would require both the zero and first lattice centres to lie on the same
straight space-time characteristic. The multiplier's normalization supplies
the dimension-one time factor.
-/

namespace RHTower

open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Each Poisson bump obeys Gaussian space-time comparison. -/
theorem heatGauss_harnack (s r θ φ : ℝ) (n : ℤ) :
    heatGauss (Real.exp s) n θ ≤
      Real.exp ((θ - φ) ^ 2 / (4 * Real.pi * Real.exp r)) *
        heatGauss (Real.exp s + Real.exp r) n φ := by
  have h := gaussianHarnack (Real.log Real.pi + s) (Real.log Real.pi + r)
    θ φ (2 * Real.pi * (n : ℝ))
  simp only [Real.exp_add, Real.exp_log Real.pi_pos, Real.norm_eq_abs, sq_abs] at h
  convert h using 1 <;>
    simp only [heatGauss, neg_div, mul_add, mul_assoc]

/-- Equality for one Poisson bump fixes its lattice centre. -/
theorem heatGauss_harnack_eq_iff (s r θ φ : ℝ) (n : ℤ) :
    heatGauss (Real.exp s) n θ =
        Real.exp ((θ - φ) ^ 2 / (4 * Real.pi * Real.exp r)) *
          heatGauss (Real.exp s + Real.exp r) n φ ↔
      Real.exp r * (θ - 2 * Real.pi * n) = Real.exp s * (φ - θ) := by
  have h := gaussianHarnack_eq_iff (Real.log Real.pi + s) (Real.log Real.pi + r)
    θ φ (2 * Real.pi * (n : ℝ))
  simp only [Real.exp_add, Real.exp_log Real.pi_pos, Real.norm_eq_abs, sq_abs,
    smul_eq_mul, ← mul_assoc] at h
  have hc : Real.pi * Real.exp r * (θ - 2 * Real.pi * n) =
      Real.pi * Real.exp s * (φ - θ) ↔
      Real.exp r * (θ - 2 * Real.pi * n) = Real.exp s * (φ - θ) := by
    constructor
    · intro he
      apply mul_left_cancel₀ Real.pi_ne_zero
      simpa only [mul_assoc] using he
    · intro he
      simpa only [mul_assoc] using congrArg (Real.pi * ·) he
  rw [← hc]
  convert h using 1
  simp only [heatGauss, neg_div, mul_add, mul_assoc]

/-- The full lattice sum never attains the sharp one-source Harnack bound. -/
theorem tsum_heatGauss_harnack_strict (s r θ φ : ℝ) :
    (∑' n : ℤ, heatGauss (Real.exp s) n θ) <
      Real.exp ((θ - φ) ^ 2 / (4 * Real.pi * Real.exp r)) *
        ∑' n : ℤ, heatGauss (Real.exp s + Real.exp r) n φ := by
  have hle := heatGauss_harnack s r θ φ
  have hex : ∃ n : ℤ, heatGauss (Real.exp s) n θ <
      Real.exp ((θ - φ) ^ 2 / (4 * Real.pi * Real.exp r)) *
        heatGauss (Real.exp s + Real.exp r) n φ := by
    by_contra hn
    push Not at hn
    have h0 := (heatGauss_harnack_eq_iff s r θ φ 0).mp (le_antisymm (hle 0) (hn 0))
    have h1 := (heatGauss_harnack_eq_iff s r θ φ 1).mp (le_antisymm (hle 1) (hn 1))
    simp only [Int.cast_zero, Int.cast_one, mul_zero, sub_zero, mul_one] at h0 h1
    nlinarith [mul_pos (Real.exp_pos r) Real.pi_pos]
  obtain ⟨n, hn⟩ := hex
  have h := Summable.tsum_lt_tsum hle hn
    (summable_heatGauss (Real.exp_pos s) θ)
    ((summable_heatGauss (add_pos (Real.exp_pos s) (Real.exp_pos r)) φ).mul_left _)
  simpa only [tsum_mul_left] using h

/-- Strict space-time Harnack bound for the literal theta heat multiplier. -/
theorem heatMultiplier_harnack_strict (s r θ φ : ℝ) :
    (heatMultiplier (Real.exp s) θ).re <
      Real.exp ((Real.log (Real.exp s + Real.exp r) - s) / 2 +
        (θ - φ) ^ 2 / (4 * Real.pi * Real.exp r)) *
          (heatMultiplier (Real.exp s + Real.exp r) φ).re := by
  rw [heatMultiplier_eq_ofReal (Real.exp_pos s),
    heatMultiplier_eq_ofReal (add_pos (Real.exp_pos s) (Real.exp_pos r))]
  simp only [Complex.ofReal_re]
  have h := mul_lt_mul_of_pos_left (tsum_heatGauss_harnack_strict s r θ φ)
    (Real.rpow_pos_of_pos (Real.exp_pos s) (-(1 : ℝ) / 2))
  apply lt_of_lt_of_eq h
  rw [Real.rpow_def_of_pos (Real.exp_pos s),
    Real.rpow_def_of_pos (add_pos (Real.exp_pos s) (Real.exp_pos r)), Real.log_exp]
  rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end

end RHTower
