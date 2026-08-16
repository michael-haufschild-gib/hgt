import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# The circle multiplier of the additive heat kernel

The additive heat kernel `H_x(m,n) = exp(-π x (m-n)^2)` on the integer lattice is a convolution
operator whose circle Fourier multiplier is

`W_x(θ) = ∑_{k ∈ ℤ} exp(-π x k²) exp(i k θ)`.

It is the two-variable Jacobi theta function at `τ = i x`, and the theta functional equation is
exactly the Poisson-summation form

`W_x(θ) = x^{-1/2} ∑_{ℓ ∈ ℤ} exp(-(θ - 2πℓ)² / (4π x))`,

which exhibits `W_x dθ/(2π)` as a Gaussian approximate identity at `θ = 0`.
-/

open Complex Filter Topology

namespace RHTower

/-- The circle Fourier multiplier of the additive heat kernel. -/
noncomputable def heatMultiplier (x θ : ℝ) : ℂ :=
  ∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * x * (k : ℂ) ^ 2 + I * (k : ℂ) * θ)

/-- The heat multiplier is the Jacobi theta function on the imaginary axis. -/
theorem heatMultiplier_eq_jacobiTheta₂ (x θ : ℝ) :
    heatMultiplier x θ = jacobiTheta₂ (((θ / (2 * Real.pi) : ℝ)) : ℂ) (I * (x : ℂ)) := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [heatMultiplier, jacobiTheta₂]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term]
  congr 1
  push_cast
  field_simp
  linear_combination (-((n : ℂ) ^ 2) * (Real.pi : ℂ) * (x : ℂ)) * Complex.I_sq

/-- **Poisson summation for the heat multiplier.** -/
theorem heatMultiplier_poisson {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    heatMultiplier x θ
      = 1 / ((x : ℂ)) ^ (1 / 2 : ℂ)
        * ∑' n : ℤ, Complex.exp (-((((θ - 2 * Real.pi * n : ℝ)) : ℂ) ^ 2 / (4 * Real.pi * x))) := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  set z : ℂ := (((θ / (2 * Real.pi) : ℝ)) : ℂ) with hz
  set τ : ℂ := I * (x : ℂ) with hτ
  have hτne : τ ≠ 0 := by
    rw [hτ]
    exact mul_ne_zero I_ne_zero hxne
  have hbase : (-I * τ) = ((x : ℝ) : ℂ) := by
    rw [hτ]
    have : (-I) * (I * (x : ℂ)) = (-(I * I)) * (x : ℂ) := by ring
    rw [this, I_mul_I]
    ring
  have hfe := jacobiTheta₂_functional_equation z τ
  rw [hbase] at hfe
  rw [heatMultiplier_eq_jacobiTheta₂, ← hz, ← hτ, hfe]
  have harg : (-(Real.pi : ℂ) * I * z ^ 2 / τ) = -((z : ℂ) ^ 2 * (Real.pi : ℂ) / (x : ℂ)) := by
    rw [hτ]
    field_simp
  have hinner : jacobiTheta₂ (z / τ) (-1 / τ)
      = ∑' n : ℤ, Complex.exp (2 * (Real.pi : ℂ) * n * z / (x : ℂ)
          - (Real.pi : ℂ) * (n : ℂ) ^ 2 / (x : ℂ)) := by
    rw [jacobiTheta₂]
    refine tsum_congr fun n => ?_
    rw [jacobiTheta₂_term, hτ]
    congr 1
    field_simp
    ring
  rw [hinner, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  have hzval : z = ((θ : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
    rw [hz]
    push_cast
    ring
  rw [hzval, hτ]
  push_cast
  field_simp
  ring

end RHTower
