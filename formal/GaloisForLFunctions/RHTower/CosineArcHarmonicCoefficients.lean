import Mathlib

/-!
# Harmonic coefficients of arc sets and the threshold sweep integral

On one period `[0, 2π]` the arc set `{|cos(φ/2)| ≥ cos θ} = [0, 2θ] ∪ [2π − 2θ, 2π]` has `j`-th
harmonic coefficient `∫_{arcs} cos(jφ) dφ = (2/j) sin(2jθ)`.  When the threshold `cos θ` sweeps
`[0, 1]` uniformly (the `1/u` envelope of a large-value window), the period contributions average to
`∫_0^{π/2} sin(2jθ) sin θ dθ = (−1)^{j+1} · 2j/(4j² − 1)`, which is never zero and has modulus at
least `1/(2j)`.  These two identities are the analytic core of the harmonic-resonance law: a
factorized large-value set resonates at every admissible power of the factor's frequency.
-/

open Real intervalIntegral

namespace RHTower

noncomputable section

/-- The `j`-th harmonic coefficient of the two arcs of half-angle `θ`. -/
theorem integral_arcs_cos_harmonic {j : ℕ} (hj : 1 ≤ j) (θ : ℝ) :
    (∫ φ in (0 : ℝ)..(2 * θ), Real.cos ((j : ℝ) * φ)) +
      (∫ φ in (2 * π - 2 * θ)..(2 * π), Real.cos ((j : ℝ) * φ)) =
      2 / (j : ℝ) * Real.sin (2 * (j : ℝ) * θ) := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have h1 : (∫ φ in (0 : ℝ)..(2 * θ), Real.cos ((j : ℝ) * φ)) =
      (j : ℝ)⁻¹ * Real.sin (2 * (j : ℝ) * θ) := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hjR, integral_cos,
      smul_eq_mul, mul_zero, Real.sin_zero, sub_zero]
    ring_nf
  have h2 : (∫ φ in (2 * π - 2 * θ)..(2 * π), Real.cos ((j : ℝ) * φ)) =
      (j : ℝ)⁻¹ * Real.sin (2 * (j : ℝ) * θ) := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hjR, integral_cos, smul_eq_mul]
    have hA : (j : ℝ) * (2 * π) = 0 + (j : ℕ) * (2 * π) := by ring
    have hB : (j : ℝ) * (2 * π - 2 * θ) = -(2 * (j : ℝ) * θ) + (j : ℕ) * (2 * π) := by ring
    rw [hA, hB, Real.sin_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi, Real.sin_zero,
      Real.sin_neg]
    ring
  rw [h1, h2]; ring

/-- Product-to-sum for `sin(2jθ) sin θ`. -/
theorem sin_two_mul_mul_sin (j θ : ℝ) :
    Real.sin (2 * j * θ) * Real.sin θ =
      (Real.cos ((2 * j - 1) * θ) - Real.cos ((2 * j + 1) * θ)) / 2 := by
  have h := Real.cos_sub_cos ((2 * j - 1) * θ) ((2 * j + 1) * θ)
  have e1 : ((2 * j - 1) * θ + (2 * j + 1) * θ) / 2 = 2 * j * θ := by ring
  have e2 : ((2 * j - 1) * θ - (2 * j + 1) * θ) / 2 = -θ := by ring
  rw [e1, e2, Real.sin_neg] at h
  linarith

/-- **The sweep integral.** -/
theorem integral_sin_harmonic_mul_sin {j : ℕ} (hj : 1 ≤ j) :
    ∫ θ in (0 : ℝ)..(π / 2), Real.sin (2 * (j : ℝ) * θ) * Real.sin θ =
      (-1) ^ (j + 1) * (2 * (j : ℝ)) / (4 * (j : ℝ) ^ 2 - 1) := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ha : (2 * (j : ℝ) - 1) ≠ 0 := by linarith
  have hb : (2 * (j : ℝ) + 1) ≠ 0 := by linarith
  have hcont1 : Continuous fun θ : ℝ => Real.cos ((2 * (j : ℝ) - 1) * θ) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcont2 : Continuous fun θ : ℝ => Real.cos ((2 * (j : ℝ) + 1) * θ) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  simp_rw [sin_two_mul_mul_sin]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)]
  have h1 : (∫ θ in (0 : ℝ)..(π / 2), Real.cos ((2 * (j : ℝ) - 1) * θ)) =
      (2 * (j : ℝ) - 1)⁻¹ * (-1) ^ (j + 1) := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) ha, integral_cos, smul_eq_mul,
      mul_zero, Real.sin_zero, sub_zero]
    have : (2 * (j : ℝ) - 1) * (π / 2) = (j : ℕ) * π - π / 2 := by ring
    rw [this, Real.sin_sub_pi_div_two, Real.cos_nat_mul_pi]
    ring
  have h2 : (∫ θ in (0 : ℝ)..(π / 2), Real.cos ((2 * (j : ℝ) + 1) * θ)) =
      (2 * (j : ℝ) + 1)⁻¹ * (-1) ^ j := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hb, integral_cos, smul_eq_mul,
      mul_zero, Real.sin_zero, sub_zero]
    have : (2 * (j : ℝ) + 1) * (π / 2) = (j : ℕ) * π + π / 2 := by ring
    rw [this, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
  rw [h1, h2]
  have hden : (4 * (j : ℝ) ^ 2 - 1) = (2 * (j : ℝ) - 1) * (2 * (j : ℝ) + 1) := by ring
  rw [hden]
  field_simp
  ring

/-- The sweep coefficient is never zero and has modulus at least `1/(2j)`. -/
theorem abs_sweep_coefficient_ge {j : ℕ} (hj : 1 ≤ j) :
    1 / (2 * (j : ℝ)) ≤ |(-1) ^ (j + 1) * (2 * (j : ℝ)) / (4 * (j : ℝ) ^ 2 - 1)| := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hpos : 0 < 4 * (j : ℝ) ^ 2 - 1 := by nlinarith
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * j), abs_of_pos hpos]
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith

end

end RHTower
