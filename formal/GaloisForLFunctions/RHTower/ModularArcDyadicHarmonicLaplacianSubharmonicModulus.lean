/-
Copyright (c) 2026 Michael. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GaloisForLFunctions.RHTower.ModularArcDyadicConjugateSineCauchyRiemann

/-!
# Global Harmonic Laplacian Cancellation and Subharmonic Complex Modulus Law for the Dyadic Modular Arc Tower

In `ModularArcDyadicJointTwoVariablePowerSeries` and `ModularArcDyadicConjugateSineCauchyRiemann`,
we established the conjugate oscillatory Mellin pair
$$
  M_k(l, \tau)
    := \int_{x > 0} x^{l - 1/2} \cos(\tau \log x) V_k(x)\,dx
     = \int_{\mathbb{R}} \cosh(l v) \cos(\tau v) \Phi_k(v)\,dv,
$$
$$
  N_k(l, \tau)
    := \int_{x > 0} x^{l - 1/2} \sin(\tau \log x) V_k(x)\,dx
     = \int_{\mathbb{R}} \sinh(l v) \sin(\tau v) \Phi_k(v)\,dv,
$$
and proved that `(M_k, N_k)` satisfies the first-order Cauchy–Riemann partial differential
equations `∂_l M_k = ∂_τ N_k` and `∂_l N_k = −∂_τ M_k` across the strip `|l| < 1/8`, `τ ∈ ℝ`.

In this module we build the **second-order complex-analytic, harmonic, and subharmonic theory**
of `(M_k(l, τ), N_k(l, τ))` and of the complex oscillatory Mellin modulus squared
$$
  |F_k(l, \tau)|^2 := M_k(l, \tau)^2 + N_k(l, \tau)^2
$$
across the strip `|l| < 1/8`, `τ ∈ ℝ`:

1. **Quartic Central-Difference Kernel Estimates & Exact Directional Curvatures (`∂_l²` and `∂_τ²`)**:
   - Elementary quartic Taylor remainder bounds
     `0 ≤ cosh u − 1 − u²/2 ≤ (u⁴ / 24) exp |u|` and
     `|cos u − 1 + u²/2| ≤ (u⁴ / 24) exp |u|` for all `u ∈ ℝ`.
   - Pointwise quartic central-difference remainder bounds for `cosh`, `sinh`, `cos`, and `sin`.
   - Height-uniform quartic `O(h⁴)` central-difference remainder bounds and exact second-order
     directional curvature limits across all `|l| < 1/8`, `τ ∈ ℝ`:
     $$
       \frac{M_k(l + h, \tau) + M_k(l - h, \tau) - 2 M_k(l, \tau)}{h^2}
         \longrightarrow \int_{\mathbb{R}} v^2 \cosh(l v) \cos(\tau v) \Phi_k(v)\,dv,
     $$
     $$
       \frac{M_k(l, \tau + h) + M_k(l, \tau - h) - 2 M_k(l, \tau)}{h^2}
         \longrightarrow -\int_{\mathbb{R}} v^2 \cosh(l v) \cos(\tau v) \Phi_k(v)\,dv,
     $$
     $$
       \frac{N_k(l + h, \tau) + N_k(l - h, \tau) - 2 N_k(l, \tau)}{h^2}
         \longrightarrow \int_{\mathbb{R}} v^2 \sinh(l v) \sin(\tau v) \Phi_k(v)\,dv,
     $$
     $$
       \frac{N_k(l, \tau + h) + N_k(l, \tau - h) - 2 N_k(l, \tau)}{h^2}
         \longrightarrow -\int_{\mathbb{R}} v^2 \sinh(l v) \sin(\tau v) \Phi_k(v)\,dv.
     $$

2. **Global Five-Point Harmonic Laplacian Cancellation (`Δ M_k = 0` and `Δ N_k = 0`)**:
   - At every point `(l, τ)` with `|l| + |h| < 1/8` and `τ ∈ ℝ`, the `O(h²)` horizontal and
     vertical curvatures cancel identically in the five-point discrete Laplacian, leaving a
     height-uniform **quartic `O(h⁴)` defect bound**:
     $$
       \bigl|\Delta_l^2 M_k(l, \tau; h) + \Delta_\tau^2 M_k(l, \tau; h)\bigr|
         \le \frac{27033600 \cdot \nu(\mathrm{univ})}{1/8 - |l| - |h|} \cdot h^4,
     $$
     $$
       \bigl|\Delta_l^2 N_k(l, \tau; h) + \Delta_\tau^2 N_k(l, \tau; h)\bigr|
         \le \frac{27033600 \cdot \nu(\mathrm{univ})}{1/8 - |l| - |h|} \cdot h^4,
     $$
     and consequently `(Δ_l² M_k + Δ_τ² M_k) / h² → 0` and `(Δ_l² N_k + Δ_τ² N_k) / h² → 0`
     as `h → 0` at every `(l, τ)` in `|l| < 1/8`, `τ ∈ ℝ`.

3. **Complex Modulus Squared `|F_k(l, τ)|² = M_k(l, τ)² + N_k(l, τ)²`, Critical-Line Transverse
   Curvature, and Isotropic Conformal Zero-Opening Law**:
   - Doubly-even functional equation symmetry `|F_k(−l, τ)|² = |F_k(l, τ)|²` and
     `|F_k(l, −τ)|² = |F_k(l, τ)|²`, and critical-line / real-axis reduction
     `|F_k(0, τ)|² = M_k(0, τ)²`, `|F_k(l, 0)|² = M_k(l, 0)²`.
   - Exact critical-line transverse curvature limit as `l → 0` (`l ≠ 0`):
     $$
       \frac{M_k(l, \tau)^2 + N_k(l, \tau)^2 - M_k(0, \tau)^2}{l^2}
         \longrightarrow M_k(0, \tau) \int_{\mathbb{R}} v^2 \cos(\tau v) \Phi_k(v)\,dv
           + \left(\int_{\mathbb{R}} v \sin(\tau v) \Phi_k(v)\,dv\right)^2.
     $$
   - **Isotropic Conformal Zero-Opening Law**: At any critical-line zero `M_k(0, τ₀) = 0`, the
     horizontal off-line quadratic opening rate and the vertical critical-line quadratic opening
     rate are both equal to the non-negative conformal slope squared
     `(∫_ℝ v sin(τ₀ v) Φ_k(v) dv)² ≥ 0`.

4. **Global Five-Point Subharmonic Laplacian Law for `|F_k(l, τ)|²` and Harmonicity of
   `Re(F_k(l, τ)²) = M_k(l, τ)² − N_k(l, τ)²`**:
   - Universal five-point quadratic central-difference decomposition.
   - Across `|l| < 1/8`, `τ ∈ ℝ`:
     $$
       \frac{\Delta_l^2 (M_k^2 + N_k^2)(l, \tau; h) + \Delta_\tau^2 (M_k^2 + N_k^2)(l, \tau; h)}{h^2}
         \longrightarrow 4 \left[
           \left(\int_{\mathbb{R}} v \sinh(l v) \cos(\tau v) \Phi_k(v)\,dv\right)^2
           + \left(\int_{\mathbb{R}} v \cosh(l v) \sin(\tau v) \Phi_k(v)\,dv\right)^2
         \right] \ge 0,
     $$
     while for the real part of the holomorphic square `M_k(l, τ)² − N_k(l, τ)²`,
     $$
       \frac{\Delta_l^2 (M_k^2 - N_k^2)(l, \tau; h) + \Delta_\tau^2 (M_k^2 - N_k^2)(l, \tau; h)}{h^2}
         \longrightarrow 0.
     $$
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Section 1: Quartic Central-Difference Kernel Estimates and Second-Order Directional Curvatures -/

/-- **Non-negativity of the quadratic Taylor remainder `cosh u − 1 − u² / 2` for all `u ∈ ℝ`.** -/
theorem cosh_sub_one_sub_sq_div_two_nonneg (u : ℝ) :
    0 ≤ Real.cosh u - 1 - u ^ 2 / 2 := by
  have h1 := sum_range_even_pow_div_factorial_le_cosh 2 u
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, mul_one, Nat.factorial_two,
    Nat.cast_ofNat] at h1
  linarith

/-- **Quartic upper bound `cosh u − 1 − u² / 2 ≤ (u⁴ / 24) · exp |u|` for all `u ∈ ℝ`.** -/
theorem cosh_sub_one_sub_sq_div_two_le_pow_four_div_twenty_four_mul_exp (u : ℝ) :
    Real.cosh u - 1 - u ^ 2 / 2 ≤ (u ^ 4 / 24) * Real.exp |u| := by
  have h1 := cosh_sub_sum_range_even_pow_div_factorial_le 2 u
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, mul_one, Nat.factorial_two,
    Nat.cast_ofNat] at h1
  have hfac4 : ((2 * 2).factorial : ℝ) = 24 := by norm_num
  rw [hfac4] at h1
  linarith

/-- **Absolute value quartic bound `|cosh u − 1 − u² / 2| ≤ (u⁴ / 24) · exp |u|` for all `u ∈ ℝ`.** -/
theorem abs_cosh_sub_one_sub_sq_div_two_le (u : ℝ) :
    |Real.cosh u - 1 - u ^ 2 / 2| ≤ (u ^ 4 / 24) * Real.exp |u| := by
  rw [abs_of_nonneg (cosh_sub_one_sub_sq_div_two_nonneg u)]
  exact cosh_sub_one_sub_sq_div_two_le_pow_four_div_twenty_four_mul_exp u

/-- **Absolute value quartic bound `|cos u − 1 + u² / 2| ≤ (u⁴ / 24) · exp |u|` for all `u ∈ ℝ`.** -/
theorem abs_cos_sub_one_add_sq_div_two_le (u : ℝ) :
    |Real.cos u - 1 + u ^ 2 / 2| ≤ (u ^ 4 / 24) * Real.exp |u| := by
  have h1 := abs_cos_sub_sum_range_even_pow_div_factorial_le 2 u
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, pow_one, mul_one,
    Nat.factorial_two, Nat.cast_ofNat] at h1
  have hfac4 : ((2 * 2).factorial : ℝ) = 24 := by norm_num
  have heq : Real.cos u - (1 + -1 * u ^ 2 / 2) = Real.cos u - 1 + u ^ 2 / 2 := by ring
  rw [hfac4, heq] at h1
  exact h1

/-- **Pointwise central-difference identity for `Real.cosh`:**
`cosh((l + h)v) + cosh((l − h)v) − 2 cosh(lv) = 2 cosh(lv) (cosh(hv) − 1)`. -/
theorem cosh_add_add_cosh_sub_sub_two_mul_cosh (l h v : ℝ) :
    Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) - 2 * Real.cosh (l * v) =
      2 * Real.cosh (l * v) * (Real.cosh (h * v) - 1) := by
  rw [add_mul, sub_mul, Real.cosh_add, Real.cosh_sub]
  ring

/-- **Pointwise central-difference identity for `Real.sinh`:**
`sinh((l + h)v) + sinh((l − h)v) − 2 sinh(lv) = 2 sinh(lv) (cosh(hv) − 1)`. -/
theorem sinh_add_add_sinh_sub_sub_two_mul_sinh (l h v : ℝ) :
    Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) - 2 * Real.sinh (l * v) =
      2 * Real.sinh (l * v) * (Real.cosh (h * v) - 1) := by
  rw [add_mul, sub_mul, Real.sinh_add, Real.sinh_sub]
  ring

/-- **Pointwise central-difference identity for `Real.cos`:**
`cos((τ + h)v) + cos((τ − h)v) − 2 cos(τv) = 2 cos(τv) (cos(hv) − 1)`. -/
theorem cos_add_add_cos_sub_sub_two_mul_cos (τ h v : ℝ) :
    Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) - 2 * Real.cos (τ * v) =
      2 * Real.cos (τ * v) * (Real.cos (h * v) - 1) := by
  rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
  ring

/-- **Pointwise central-difference identity for `Real.sin`:**
`sin((τ + h)v) + sin((τ − h)v) − 2 sin(τv) = 2 sin(τv) (cos(hv) − 1)`. -/
theorem sin_add_add_sin_sub_sub_two_mul_sin (τ h v : ℝ) :
    Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) - 2 * Real.sin (τ * v) =
      2 * Real.sin (τ * v) * (Real.cos (h * v) - 1) := by
  rw [add_mul, sub_mul, Real.sin_add, Real.sin_sub]
  ring

/-- **Pointwise quartic central-difference remainder bound for `Real.cosh`:**
For all `l, h, v ∈ ℝ`,
`|cosh((l + h)v) + cosh((l − h)v) − 2 cosh(lv) − (hv)² cosh(lv)| ≤
  (h⁴ v⁴ / 12) · exp((|l| + |h|)|v|)`. -/
theorem abs_cosh_central_diff_sub_sq_mul_cosh_le (l h v : ℝ) :
    |Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) - 2 * Real.cosh (l * v) -
        (h * v) ^ 2 * Real.cosh (l * v)| ≤
      (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
  have hsplit :
      Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) - 2 * Real.cosh (l * v) -
          (h * v) ^ 2 * Real.cosh (l * v) =
        2 * Real.cosh (l * v) * (Real.cosh (h * v) - 1 - (h * v) ^ 2 / 2) := by
    rw [cosh_add_add_cosh_sub_sub_two_mul_cosh]
    ring
  have hcosh_l : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
  have hrem_h :
      |Real.cosh (h * v) - 1 - (h * v) ^ 2 / 2| ≤
        ((h * v) ^ 4 / 24) * Real.exp (|h| * |v|) := by
    rw [← abs_mul]
    exact abs_cosh_sub_one_sub_sq_div_two_le (h * v)
  rw [hsplit, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (Real.cosh_pos _)]
  have hprod :
      Real.cosh (l * v) * |Real.cosh (h * v) - 1 - (h * v) ^ 2 / 2| ≤
        Real.exp (|l| * |v|) * (((h * v) ^ 4 / 24) * Real.exp (|h| * |v|)) :=
    mul_le_mul hcosh_l hrem_h (abs_nonneg _) (Real.exp_nonneg _)
  calc 2 * Real.cosh (l * v) * |Real.cosh (h * v) - 1 - (h * v) ^ 2 / 2|
      = 2 * (Real.cosh (l * v) * |Real.cosh (h * v) - 1 - (h * v) ^ 2 / 2|) := by ring
    _ ≤ 2 * (Real.exp (|l| * |v|) * (((h * v) ^ 4 / 24) * Real.exp (|h| * |v|))) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (h ^ 4 * v ^ 4 / 12) * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
    _ = (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Pointwise quartic central-difference remainder bound for `Real.sinh`:**
For all `l, h, v ∈ ℝ`,
`|sinh((l + h)v) + sinh((l − h)v) − 2 sinh(lv) − (hv)² sinh(lv)| ≤
  (h⁴ v⁴ / 12) · exp((|l| + |h|)|v|)`. -/
theorem abs_sinh_central_diff_sub_sq_mul_sinh_le (l h v : ℝ) :
    |Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) - 2 * Real.sinh (l * v) -
        (h * v) ^ 2 * Real.sinh (l * v)| ≤
      (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
  have hsplit :
      Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) - 2 * Real.sinh (l * v) -
          (h * v) ^ 2 * Real.sinh (l * v) =
        2 * Real.sinh (l * v) * (Real.cosh (h * v) - 1 - (h * v) ^ 2 / 2) := by
    rw [sinh_add_add_sinh_sub_sub_two_mul_sinh]
    ring
  have hsinh_l : |Real.sinh (l * v)| ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact abs_sinh_le_exp_abs (l * v)
  have hrem_h :
      |Real.cosh (h * v) - 1 - (h * v) ^ 2 / 2| ≤
        ((h * v) ^ 4 / 24) * Real.exp (|h| * |v|) := by
    rw [← abs_mul]
    exact abs_cosh_sub_one_sub_sq_div_two_le (h * v)
  rw [hsplit, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hprod :
      |Real.sinh (l * v)| * |Real.cosh (h * v) - 1 - (h * v) ^ 2 / 2| ≤
        Real.exp (|l| * |v|) * (((h * v) ^ 4 / 24) * Real.exp (|h| * |v|)) :=
    mul_le_mul hsinh_l hrem_h (abs_nonneg _) (Real.exp_nonneg _)
  calc 2 * |Real.sinh (l * v)| * |Real.cosh (h * v) - 1 - (h * v) ^ 2 / 2|
      = 2 * (|Real.sinh (l * v)| * |Real.cosh (h * v) - 1 - (h * v) ^ 2 / 2|) := by ring
    _ ≤ 2 * (Real.exp (|l| * |v|) * (((h * v) ^ 4 / 24) * Real.exp (|h| * |v|))) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (h ^ 4 * v ^ 4 / 12) * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
    _ = (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Pointwise quartic central-difference remainder bound for `Real.cos`:**
For all `τ, h, v ∈ ℝ`,
`|cos((τ + h)v) + cos((τ − h)v) − 2 cos(τv) + (hv)² cos(τv)| ≤
  (h⁴ v⁴ / 12) · exp(|h| |v|)`. -/
theorem abs_cos_central_diff_add_sq_mul_cos_le (τ h v : ℝ) :
    |Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) - 2 * Real.cos (τ * v) +
        (h * v) ^ 2 * Real.cos (τ * v)| ≤
      (h ^ 4 * v ^ 4 / 12) * Real.exp (|h| * |v|) := by
  have hsplit :
      Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) - 2 * Real.cos (τ * v) +
          (h * v) ^ 2 * Real.cos (τ * v) =
        2 * Real.cos (τ * v) * (Real.cos (h * v) - 1 + (h * v) ^ 2 / 2) := by
    rw [cos_add_add_cos_sub_sub_two_mul_cos]
    ring
  have hrem_h :
      |Real.cos (h * v) - 1 + (h * v) ^ 2 / 2| ≤
        ((h * v) ^ 4 / 24) * Real.exp (|h| * |v|) := by
    rw [← abs_mul]
    exact abs_cos_sub_one_add_sq_div_two_le (h * v)
  rw [hsplit, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hprod :
      |Real.cos (τ * v)| * |Real.cos (h * v) - 1 + (h * v) ^ 2 / 2| ≤
        1 * (((h * v) ^ 4 / 24) * Real.exp (|h| * |v|)) :=
    mul_le_mul (Real.abs_cos_le_one _) hrem_h (abs_nonneg _) (by positivity)
  calc 2 * |Real.cos (τ * v)| * |Real.cos (h * v) - 1 + (h * v) ^ 2 / 2|
      = 2 * (|Real.cos (τ * v)| * |Real.cos (h * v) - 1 + (h * v) ^ 2 / 2|) := by ring
    _ ≤ 2 * (1 * (((h * v) ^ 4 / 24) * Real.exp (|h| * |v|))) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (h ^ 4 * v ^ 4 / 12) * Real.exp (|h| * |v|) := by ring

/-- **Pointwise quartic central-difference remainder bound for `Real.sin`:**
For all `τ, h, v ∈ ℝ`,
`|sin((τ + h)v) + sin((τ − h)v) − 2 sin(τv) + (hv)² sin(τv)| ≤
  (h⁴ v⁴ / 12) · exp(|h| |v|)`. -/
theorem abs_sin_central_diff_add_sq_mul_sin_le (τ h v : ℝ) :
    |Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) - 2 * Real.sin (τ * v) +
        (h * v) ^ 2 * Real.sin (τ * v)| ≤
      (h ^ 4 * v ^ 4 / 12) * Real.exp (|h| * |v|) := by
  have hsplit :
      Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) - 2 * Real.sin (τ * v) +
          (h * v) ^ 2 * Real.sin (τ * v) =
        2 * Real.sin (τ * v) * (Real.cos (h * v) - 1 + (h * v) ^ 2 / 2) := by
    rw [sin_add_add_sin_sub_sub_two_mul_sin]
    ring
  have hrem_h :
      |Real.cos (h * v) - 1 + (h * v) ^ 2 / 2| ≤
        ((h * v) ^ 4 / 24) * Real.exp (|h| * |v|) := by
    rw [← abs_mul]
    exact abs_cos_sub_one_add_sq_div_two_le (h * v)
  rw [hsplit, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hprod :
      |Real.sin (τ * v)| * |Real.cos (h * v) - 1 + (h * v) ^ 2 / 2| ≤
        1 * (((h * v) ^ 4 / 24) * Real.exp (|h| * |v|)) :=
    mul_le_mul (Real.abs_sin_le_one _) hrem_h (abs_nonneg _) (by positivity)
  calc 2 * |Real.sin (τ * v)| * |Real.cos (h * v) - 1 + (h * v) ^ 2 / 2|
      = 2 * (|Real.sin (τ * v)| * |Real.cos (h * v) - 1 + (h * v) ^ 2 / 2|) := by ring
    _ ≤ 2 * (1 * (((h * v) ^ 4 / 24) * Real.exp (|h| * |v|))) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (h ^ 4 * v ^ 4 / 12) * Real.exp (|h| * |v|) := by ring

/-- **Pointwise quartic central-difference envelope multiplied by `|Φ_k(v)|` (`k ≥ 2`):**
`((h⁴ v⁴ / 12) · exp((|l| + |h|)|v|)) · |Φ_k(v)| ≤
  6758400 · ν.real univ · h⁴ · exp(−(1/8 − |l| − |h|)|v|)`. -/
theorem quartic_shift_mul_abs_arcLineInfiniteDyadicProfile_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l h v : ℝ) :
    ((h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|)) *
        |arcLineInfiniteDyadicProfile k ν v| ≤
      6758400 * ν.real univ * h ^ 4 * Real.exp (-((1 / 8 - |l| - |h|) * |v|)) := by
  have h1 := abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν 4 v
  have hv4 : |v| ^ 4 = v ^ 4 := by
    calc |v| ^ 4 = (|v| ^ 2) ^ 2 := by ring
      _ = (v ^ 2) ^ 2 := by rw [sq_abs]
      _ = v ^ 4 := by ring
  have hfac : (4 : ℕ).factorial = 24 := by decide
  rw [hv4, hfac, Nat.cast_ofNat] at h1
  have h2 :
      ((h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|)) *
          |arcLineInfiniteDyadicProfile k ν v| =
        (h ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) *
          (v ^ 4 * |arcLineInfiniteDyadicProfile k ν v|) := by ring
  rw [h2]
  have hh4 : 0 ≤ h ^ 4 := by
    calc (0 : ℝ) ≤ (h ^ 2) ^ 2 := sq_nonneg _
      _ = h ^ 4 := by ring
  calc (h ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) *
          (v ^ 4 * |arcLineInfiniteDyadicProfile k ν v|)
      ≤ (h ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) *
          (825 * ν.real univ * 24 * 8 ^ 4 * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 6758400 * ν.real univ * h ^ 4 *
          (Real.exp ((|l| + |h|) * |v|) * Real.exp (-((1 / 8 : ℝ) * |v|))) := by ring
    _ = 6758400 * ν.real univ * h ^ 4 * Real.exp (-((1 / 8 - |l| - |h|) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Integrability of `v^n cosh(lv) cos(τv) Φ_k(v)` on `ℝ` across `|l| < 1/8` and `τ ∈ ℝ` (`k ≥ 2`, `n ∈ ℕ`).** -/
theorem integrable_pow_mul_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (n : ℕ) (τ : ℝ) :
    Integrable
      (fun v : ℝ => v ^ n * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hc : 0 < 1 / 8 - |l| := by linarith
  set B := 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  refine hdom.mono'
    ((((continuous_id.pow n).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.cosh_pos _)]
  have hcosh : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
  have hcos : |Real.cos (τ * v)| ≤ 1 := Real.abs_cos_le_one (τ * v)
  have h1 := abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν n v
  have hcc : Real.cosh (l * v) * |Real.cos (τ * v)| ≤ Real.exp (|l| * |v|) := by
    calc Real.cosh (l * v) * |Real.cos (τ * v)|
        ≤ Real.exp (|l| * |v|) * 1 := mul_le_mul hcosh hcos (abs_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (|l| * |v|) := by ring
  calc |v| ^ n * Real.cosh (l * v) * |Real.cos (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
      = (Real.cosh (l * v) * |Real.cos (τ * v)|) *
          (|v| ^ n * |arcLineInfiniteDyadicProfile k ν v|) := by ring
    _ ≤ Real.exp (|l| * |v|) * (B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
        mul_le_mul hcc h1 (by positivity) (Real.exp_nonneg _)
    _ = B * (Real.exp (|l| * |v|) * Real.exp (-((1 / 8 : ℝ) * |v|))) := by ring
    _ = B * Real.exp (-((1 / 8 - |l|) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Integrability of `v^n sinh(lv) sin(τv) Φ_k(v)` on `ℝ` across `|l| < 1/8` and `τ ∈ ℝ` (`k ≥ 2`, `n ∈ ℕ`).** -/
theorem integrable_pow_mul_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (n : ℕ) (τ : ℝ) :
    Integrable
      (fun v : ℝ => v ^ n * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hc : 0 < 1 / 8 - |l| := by linarith
  set B := 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  refine hdom.mono'
    ((((continuous_id.pow n).mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow]
  have hsinh : |Real.sinh (l * v)| ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact abs_sinh_le_exp_abs (l * v)
  have hsin : |Real.sin (τ * v)| ≤ 1 := Real.abs_sin_le_one (τ * v)
  have h1 := abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν n v
  have hss : |Real.sinh (l * v)| * |Real.sin (τ * v)| ≤ Real.exp (|l| * |v|) := by
    calc |Real.sinh (l * v)| * |Real.sin (τ * v)|
        ≤ Real.exp (|l| * |v|) * 1 := mul_le_mul hsinh hsin (abs_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (|l| * |v|) := by ring
  calc |v| ^ n * |Real.sinh (l * v)| * |Real.sin (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
      = (|Real.sinh (l * v)| * |Real.sin (τ * v)|) *
          (|v| ^ n * |arcLineInfiniteDyadicProfile k ν v|) := by ring
    _ ≤ Real.exp (|l| * |v|) * (B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
        mul_le_mul hss h1 (by positivity) (Real.exp_nonneg _)
    _ = B * (Real.exp (|l| * |v|) * Real.exp (-((1 / 8 : ℝ) * |v|))) := by ring
    _ = B * Real.exp (-((1 / 8 - |l|) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Height-uniform quartic `O(h⁴)` horizontal central-difference remainder bound for `M_k(l, τ)`
(`k ≥ 2`, `|l| + |h| < 1/8`, `τ ∈ ℝ`):**
`|(M_k(l + h, τ) + M_k(l − h, τ) − 2 M_k(l, τ)) − h² ∫_ℝ v² cosh(lv) cos(τv) Φ_k(v) dv| ≤
  (13516800 · ν.real univ / (1/8 − |l| − |h|)) · h⁴`. -/
theorem abs_oscillatoryMellin_horiz_central_diff_sub_sq_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by
  have hk1 : 1 ≤ k := by omega
  have hl_eighth : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hlh_add_half : |l + h| < 1 / 2 := by
    have := abs_add_le l h; linarith
  have hlh_sub_half : |l - h| < 1 / 2 := by
    have := abs_sub l h; linarith
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν (l + h) τ,
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hlh_add_half τ,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν (l - h) τ,
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hlh_sub_half τ,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half τ]
  have hInt1 := integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hlh_add_half τ
  have hInt2 := integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hlh_sub_half τ
  have hInt12 : Integrable
      (fun v : ℝ =>
        Real.cosh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.cosh ((l - h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    hInt1.add hInt2
  have hInt3' : Integrable
      (fun v : ℝ => 2 * (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    (integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ).const_mul 2
  have hInt123 : Integrable
      (fun v : ℝ =>
        (Real.cosh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.cosh ((l - h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          2 * (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    hInt12.sub hInt3'
  have hInt4 : Integrable
      (fun v : ℝ => h ^ 2 * (v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    (integrable_pow_mul_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_eighth 2 τ).const_mul (h ^ 2)
  rw [← integral_add hInt1 hInt2, ← integral_const_mul 2, ← integral_sub hInt12 hInt3',
    ← integral_const_mul (h ^ 2), ← integral_sub hInt123 hInt4]
  set B := 6758400 * ν.real univ * h ^ 4
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      (Real.cosh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
        Real.cosh ((l - h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
        h ^ 2 * (v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            ((Real.cosh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
              Real.cosh ((l - h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              2 * (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
              h ^ 2 * (v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))|
        ≤ B * (2 / (1 / 8 - |l| - |h|)) := h1
      _ = (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by dsimp [B]; ring
  · have hfactor :
        (Real.cosh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.cosh ((l - h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
          h ^ 2 * (v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        (Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) - 2 * Real.cosh (l * v) -
          (h * v) ^ 2 * Real.cosh (l * v)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hfactor, abs_mul, abs_mul]
    have hrem := abs_cosh_central_diff_sub_sq_mul_cosh_le l h v
    have hcos : |Real.cos (τ * v)| ≤ 1 := Real.abs_cos_le_one (τ * v)
    have hprod1 :
        |Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) - 2 * Real.cosh (l * v) -
          (h * v) ^ 2 * Real.cosh (l * v)| * |Real.cos (τ * v)| ≤
        (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
      have hh4 : 0 ≤ h ^ 4 * v ^ 4 / 12 := by
        have : 0 ≤ (h ^ 2) ^ 2 * (v ^ 2) ^ 2 / 12 := by positivity
        linarith [show (h ^ 2) ^ 2 * (v ^ 2) ^ 2 / 12 = h ^ 4 * v ^ 4 / 12 by ring]
      calc |Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) - 2 * Real.cosh (l * v) -
              (h * v) ^ 2 * Real.cosh (l * v)| * |Real.cos (τ * v)|
          ≤ ((h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|)) * 1 :=
            mul_le_mul hrem hcos (abs_nonneg _) (mul_nonneg hh4 (Real.exp_nonneg _))
        _ = (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by ring
    exact (mul_le_mul_of_nonneg_right hprod1 (abs_nonneg _)).trans
      (quartic_shift_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v)

/-- **Exact second-order horizontal curvature (`∂_l² M_k(l, τ)`) across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((M_k(l + h, τ) + M_k(l − h, τ) − 2 M_k(l, τ)) / h² → ∫_ℝ v² cosh(lv) cos(τv) Φ_k(v) dv`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_horiz_central_diff_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set δ := (1 / 8 - |l|) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  set C := 13516800 * ν.real univ / δ
  have hmaj : Tendsto (fun h : ℝ => C * h ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * h ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) hδ_pos)
  filter_upwards [hmem, self_mem_nhdsWithin] with h hh_mem hh_ne
  simp only [mem_compl_singleton_iff] at hh_ne
  have hh_lt : |h| < δ := abs_lt.mpr hh_mem
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_lt; linarith
  have hsq_pos : 0 < h ^ 2 := sq_pos_of_ne_zero hh_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2 -
      (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      (((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) /
        h ^ 2 := by
    have hne2 : h ^ 2 ≠ 0 := hsq_pos.ne'
    field_simp
  rw [hdiff_eq, abs_div, abs_of_pos hsq_pos, div_le_iff₀ hsq_pos]
  have h1 := abs_oscillatoryMellin_horiz_central_diff_sub_sq_le hk hν hlh τ
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_lt ⊢; linarith
  have hinv : 1 / (1 / 8 - |l| - |h|) ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ_pos hdenom
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hh4 : 0 ≤ h ^ 4 := by
    calc (0 : ℝ) ≤ (h ^ 2) ^ 2 := sq_nonneg _
      _ = h ^ 4 := by ring
  calc |((∫ x in Ioi (0 : ℝ),
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := h1
    _ = (1 / (1 / 8 - |l| - |h|)) * (13516800 * ν.real univ * h ^ 4) := by ring
    _ ≤ (1 / δ) * (13516800 * ν.real univ * h ^ 4) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * h ^ 2 * h ^ 2 := by dsimp [C]; ring

/-- **Height-uniform quartic `O(h⁴)` vertical central-difference remainder bound for `M_k(l, τ)`
(`k ≥ 2`, `|l| + |h| < 1/8`, `τ ∈ ℝ`):**
`|(M_k(l, τ + h) + M_k(l, τ − h) − 2 M_k(l, τ)) + h² ∫_ℝ v² cosh(lv) cos(τv) Φ_k(v) dv| ≤
  (13516800 · ν.real univ / (1/8 − |l| − |h|)) · h⁴`. -/
theorem abs_oscillatoryMellin_vert_central_diff_add_sq_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by
  have hk1 : 1 ≤ k := by omega
  have hl_eighth : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l (τ + h),
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half (τ + h),
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l (τ - h),
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half (τ - h),
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half τ]
  have hInt1 := integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half (τ + h)
  have hInt2 := integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half (τ - h)
  have hInt12 : Integrable
      (fun v : ℝ =>
        Real.cosh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.cosh (l * v) * Real.cos ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v) :=
    hInt1.add hInt2
  have hInt3' : Integrable
      (fun v : ℝ => 2 * (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    (integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ).const_mul 2
  have hInt123 : Integrable
      (fun v : ℝ =>
        (Real.cosh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.cosh (l * v) * Real.cos ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v) -
          2 * (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    hInt12.sub hInt3'
  have hInt4 : Integrable
      (fun v : ℝ => h ^ 2 * (v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    (integrable_pow_mul_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_eighth 2 τ).const_mul (h ^ 2)
  rw [← integral_add hInt1 hInt2, ← integral_const_mul 2, ← integral_sub hInt12 hInt3',
    ← integral_const_mul (h ^ 2), ← integral_add hInt123 hInt4]
  set B := 6758400 * ν.real univ * h ^ 4
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      (Real.cosh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
        Real.cosh (l * v) * Real.cos ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        h ^ 2 * (v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            ((Real.cosh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
              Real.cosh (l * v) * Real.cos ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
              2 * (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
              h ^ 2 * (v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))|
        ≤ B * (2 / (1 / 8 - |l| - |h|)) := h1
      _ = (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by dsimp [B]; ring
  · have hfactor :
        (Real.cosh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.cosh (l * v) * Real.cos ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          h ^ 2 * (v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        Real.cosh (l * v) *
          (Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) - 2 * Real.cos (τ * v) +
            (h * v) ^ 2 * Real.cos (τ * v)) *
          arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hfactor, abs_mul, abs_mul, abs_of_pos (Real.cosh_pos _)]
    have hcosh : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
      rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
    have hrem := abs_cos_central_diff_add_sq_mul_cos_le τ h v
    have hprod1 :
        Real.cosh (l * v) *
          |Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) - 2 * Real.cos (τ * v) +
            (h * v) ^ 2 * Real.cos (τ * v)| ≤
        (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
      calc Real.cosh (l * v) *
              |Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) - 2 * Real.cos (τ * v) +
                (h * v) ^ 2 * Real.cos (τ * v)|
          ≤ Real.exp (|l| * |v|) * ((h ^ 4 * v ^ 4 / 12) * Real.exp (|h| * |v|)) :=
            mul_le_mul hcosh hrem (abs_nonneg _) (Real.exp_nonneg _)
        _ = (h ^ 4 * v ^ 4 / 12) * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
        _ = (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    exact (mul_le_mul_of_nonneg_right hprod1 (abs_nonneg _)).trans
      (quartic_shift_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v)

/-- **Exact second-order vertical curvature (`∂_τ² M_k(l, τ) = −∂_l² M_k(l, τ)`) across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((M_k(l, τ + h) + M_k(l, τ − h) − 2 M_k(l, τ)) / h² → −∫_ℝ v² cosh(lv) cos(τv) Φ_k(v) dv`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_vert_central_diff_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (-(∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  set δ := (1 / 8 - |l|) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  set C := 13516800 * ν.real univ / δ
  have hmaj : Tendsto (fun h : ℝ => C * h ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * h ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) hδ_pos)
  filter_upwards [hmem, self_mem_nhdsWithin] with h hh_mem hh_ne
  simp only [mem_compl_singleton_iff] at hh_ne
  have hh_lt : |h| < δ := abs_lt.mpr hh_mem
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_lt; linarith
  have hsq_pos : 0 < h ^ 2 := sq_pos_of_ne_zero hh_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2 -
      (-(∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) =
      (((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) /
        h ^ 2 := by
    have hne2 : h ^ 2 ≠ 0 := hsq_pos.ne'
    field_simp
    ring
  rw [hdiff_eq, abs_div, abs_of_pos hsq_pos, div_le_iff₀ hsq_pos]
  have h1 := abs_oscillatoryMellin_vert_central_diff_add_sq_le hk hν hlh τ
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_lt ⊢; linarith
  have hinv : 1 / (1 / 8 - |l| - |h|) ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ_pos hdenom
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hh4 : 0 ≤ h ^ 4 := by
    calc (0 : ℝ) ≤ (h ^ 2) ^ 2 := sq_nonneg _
      _ = h ^ 4 := by ring
  calc |((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := h1
    _ = (1 / (1 / 8 - |l| - |h|)) * (13516800 * ν.real univ * h ^ 4) := by ring
    _ ≤ (1 / δ) * (13516800 * ν.real univ * h ^ 4) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * h ^ 2 * h ^ 2 := by dsimp [C]; ring

/-- **Height-uniform quartic `O(h⁴)` horizontal central-difference remainder bound for `N_k(l, τ)`
(`k ≥ 2`, `|l| + |h| < 1/8`, `τ ∈ ℝ`):**
`|(N_k(l + h, τ) + N_k(l − h, τ) − 2 N_k(l, τ)) − h² ∫_ℝ v² sinh(lv) sin(τv) Φ_k(v) dv| ≤
  (13516800 · ν.real univ / (1/8 − |l| − |h|)) · h⁴`. -/
theorem abs_sineMellin_horiz_central_diff_sub_sq_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by
  have hk1 : 1 ≤ k := by omega
  have hl_eighth : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hlh_add_half : |l + h| < 1 / 2 := by
    have := abs_add_le l h; linarith
  have hlh_sub_half : |l - h| < 1 / 2 := by
    have := abs_sub l h; linarith
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν (l + h) τ,
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hlh_add_half τ,
    setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν (l - h) τ,
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hlh_sub_half τ,
    setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hl_half τ]
  have hInt1 := integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hlh_add_half τ
  have hInt2 := integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hlh_sub_half τ
  have hInt12 : Integrable
      (fun v : ℝ =>
        Real.sinh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.sinh ((l - h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    hInt1.add hInt2
  have hInt3' : Integrable
      (fun v : ℝ => 2 * (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    (integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ).const_mul 2
  have hInt123 : Integrable
      (fun v : ℝ =>
        (Real.sinh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.sinh ((l - h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          2 * (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    hInt12.sub hInt3'
  have hInt4 : Integrable
      (fun v : ℝ => h ^ 2 * (v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    (integrable_pow_mul_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_eighth 2 τ).const_mul (h ^ 2)
  rw [← integral_add hInt1 hInt2, ← integral_const_mul 2, ← integral_sub hInt12 hInt3',
    ← integral_const_mul (h ^ 2), ← integral_sub hInt123 hInt4]
  set B := 6758400 * ν.real univ * h ^ 4
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      (Real.sinh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v +
        Real.sinh ((l - h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
        h ^ 2 * (v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            ((Real.sinh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v +
              Real.sinh ((l - h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              2 * (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
              h ^ 2 * (v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))|
        ≤ B * (2 / (1 / 8 - |l| - |h|)) := h1
      _ = (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by dsimp [B]; ring
  · have hfactor :
        (Real.sinh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.sinh ((l - h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
          h ^ 2 * (v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        (Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) - 2 * Real.sinh (l * v) -
          (h * v) ^ 2 * Real.sinh (l * v)) *
          Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hfactor, abs_mul, abs_mul]
    have hrem := abs_sinh_central_diff_sub_sq_mul_sinh_le l h v
    have hsin : |Real.sin (τ * v)| ≤ 1 := Real.abs_sin_le_one (τ * v)
    have hprod1 :
        |Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) - 2 * Real.sinh (l * v) -
          (h * v) ^ 2 * Real.sinh (l * v)| * |Real.sin (τ * v)| ≤
        (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
      have hh4 : 0 ≤ h ^ 4 * v ^ 4 / 12 := by
        have : 0 ≤ (h ^ 2) ^ 2 * (v ^ 2) ^ 2 / 12 := by positivity
        linarith [show (h ^ 2) ^ 2 * (v ^ 2) ^ 2 / 12 = h ^ 4 * v ^ 4 / 12 by ring]
      calc |Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) - 2 * Real.sinh (l * v) -
              (h * v) ^ 2 * Real.sinh (l * v)| * |Real.sin (τ * v)|
          ≤ ((h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|)) * 1 :=
            mul_le_mul hrem hsin (abs_nonneg _) (mul_nonneg hh4 (Real.exp_nonneg _))
        _ = (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by ring
    exact (mul_le_mul_of_nonneg_right hprod1 (abs_nonneg _)).trans
      (quartic_shift_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v)

/-- **Exact second-order horizontal curvature (`∂_l² N_k(l, τ)`) across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((N_k(l + h, τ) + N_k(l − h, τ) − 2 N_k(l, τ)) / h² → ∫_ℝ v² sinh(lv) sin(τv) Φ_k(v) dv`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sineMellin_horiz_central_diff_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set δ := (1 / 8 - |l|) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  set C := 13516800 * ν.real univ / δ
  have hmaj : Tendsto (fun h : ℝ => C * h ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * h ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) hδ_pos)
  filter_upwards [hmem, self_mem_nhdsWithin] with h hh_mem hh_ne
  simp only [mem_compl_singleton_iff] at hh_ne
  have hh_lt : |h| < δ := abs_lt.mpr hh_mem
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_lt; linarith
  have hsq_pos : 0 < h ^ 2 := sq_pos_of_ne_zero hh_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2 -
      (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      (((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) /
        h ^ 2 := by
    have hne2 : h ^ 2 ≠ 0 := hsq_pos.ne'
    field_simp
  rw [hdiff_eq, abs_div, abs_of_pos hsq_pos, div_le_iff₀ hsq_pos]
  have h1 := abs_sineMellin_horiz_central_diff_sub_sq_le hk hν hlh τ
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_lt ⊢; linarith
  have hinv : 1 / (1 / 8 - |l| - |h|) ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ_pos hdenom
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hh4 : 0 ≤ h ^ 4 := by
    calc (0 : ℝ) ≤ (h ^ 2) ^ 2 := sq_nonneg _
      _ = h ^ 4 := by ring
  calc |((∫ x in Ioi (0 : ℝ),
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := h1
    _ = (1 / (1 / 8 - |l| - |h|)) * (13516800 * ν.real univ * h ^ 4) := by ring
    _ ≤ (1 / δ) * (13516800 * ν.real univ * h ^ 4) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * h ^ 2 * h ^ 2 := by dsimp [C]; ring

/-- **Height-uniform quartic `O(h⁴)` vertical central-difference remainder bound for `N_k(l, τ)`
(`k ≥ 2`, `|l| + |h| < 1/8`, `τ ∈ ℝ`):**
`|(N_k(l, τ + h) + N_k(l, τ − h) − 2 N_k(l, τ)) + h² ∫_ℝ v² sinh(lv) sin(τv) Φ_k(v) dv| ≤
  (13516800 · ν.real univ / (1/8 − |l| − |h|)) · h⁴`. -/
theorem abs_sineMellin_vert_central_diff_add_sq_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by
  have hk1 : 1 ≤ k := by omega
  have hl_eighth : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l (τ + h),
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hl_half (τ + h),
    setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l (τ - h),
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hl_half (τ - h),
    setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hl_half τ]
  have hInt1 := integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_half (τ + h)
  have hInt2 := integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_half (τ - h)
  have hInt12 : Integrable
      (fun v : ℝ =>
        Real.sinh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.sinh (l * v) * Real.sin ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v) :=
    hInt1.add hInt2
  have hInt3' : Integrable
      (fun v : ℝ => 2 * (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    (integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ).const_mul 2
  have hInt123 : Integrable
      (fun v : ℝ =>
        (Real.sinh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.sinh (l * v) * Real.sin ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v) -
          2 * (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    hInt12.sub hInt3'
  have hInt4 : Integrable
      (fun v : ℝ => h ^ 2 * (v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    (integrable_pow_mul_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_eighth 2 τ).const_mul (h ^ 2)
  rw [← integral_add hInt1 hInt2, ← integral_const_mul 2, ← integral_sub hInt12 hInt3',
    ← integral_const_mul (h ^ 2), ← integral_add hInt123 hInt4]
  set B := 6758400 * ν.real univ * h ^ 4
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      (Real.sinh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
        Real.sinh (l * v) * Real.sin ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        h ^ 2 * (v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            ((Real.sinh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
              Real.sinh (l * v) * Real.sin ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
              2 * (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
              h ^ 2 * (v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))|
        ≤ B * (2 / (1 / 8 - |l| - |h|)) := h1
      _ = (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by dsimp [B]; ring
  · have hfactor :
        (Real.sinh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.sinh (l * v) * Real.sin ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          h ^ 2 * (v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        Real.sinh (l * v) *
          (Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) - 2 * Real.sin (τ * v) +
            (h * v) ^ 2 * Real.sin (τ * v)) *
          arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hfactor, abs_mul, abs_mul]
    have hsinh : |Real.sinh (l * v)| ≤ Real.exp (|l| * |v|) := by
      rw [← abs_mul]; exact abs_sinh_le_exp_abs (l * v)
    have hrem := abs_sin_central_diff_add_sq_mul_sin_le τ h v
    have hprod1 :
        |Real.sinh (l * v)| *
          |Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) - 2 * Real.sin (τ * v) +
            (h * v) ^ 2 * Real.sin (τ * v)| ≤
        (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
      calc |Real.sinh (l * v)| *
              |Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) - 2 * Real.sin (τ * v) +
                (h * v) ^ 2 * Real.sin (τ * v)|
          ≤ Real.exp (|l| * |v|) * ((h ^ 4 * v ^ 4 / 12) * Real.exp (|h| * |v|)) :=
            mul_le_mul hsinh hrem (abs_nonneg _) (Real.exp_nonneg _)
        _ = (h ^ 4 * v ^ 4 / 12) * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
        _ = (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    exact (mul_le_mul_of_nonneg_right hprod1 (abs_nonneg _)).trans
      (quartic_shift_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v)

/-- **Exact second-order vertical curvature (`∂_τ² N_k(l, τ) = −∂_l² N_k(l, τ)`) across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((N_k(l, τ + h) + N_k(l, τ − h) − 2 N_k(l, τ)) / h² → −∫_ℝ v² sinh(lv) sin(τv) Φ_k(v) dv`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sineMellin_vert_central_diff_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (-(∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  set δ := (1 / 8 - |l|) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  set C := 13516800 * ν.real univ / δ
  have hmaj : Tendsto (fun h : ℝ => C * h ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * h ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) hδ_pos)
  filter_upwards [hmem, self_mem_nhdsWithin] with h hh_mem hh_ne
  simp only [mem_compl_singleton_iff] at hh_ne
  have hh_lt : |h| < δ := abs_lt.mpr hh_mem
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_lt; linarith
  have hsq_pos : 0 < h ^ 2 := sq_pos_of_ne_zero hh_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2 -
      (-(∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) =
      (((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) /
        h ^ 2 := by
    have hne2 : h ^ 2 ≠ 0 := hsq_pos.ne'
    field_simp
    ring
  rw [hdiff_eq, abs_div, abs_of_pos hsq_pos, div_le_iff₀ hsq_pos]
  have h1 := abs_sineMellin_vert_central_diff_add_sq_le hk hν hlh τ
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_lt ⊢; linarith
  have hinv : 1 / (1 / 8 - |l| - |h|) ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ_pos hdenom
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hh4 : 0 ≤ h ^ 4 := by
    calc (0 : ℝ) ≤ (h ^ 2) ^ 2 := sq_nonneg _
      _ = h ^ 4 := by ring
  calc |((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (13516800 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := h1
    _ = (1 / (1 / 8 - |l| - |h|)) * (13516800 * ν.real univ * h ^ 4) := by ring
    _ ≤ (1 / δ) * (13516800 * ν.real univ * h ^ 4) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * h ^ 2 * h ^ 2 := by dsimp [C]; ring


/-! ## Section 2: Global Five-Point Harmonic Laplacian Cancellation for `M_k(l, τ)` and `N_k(l, τ)` -/

/-- **Height-uniform quartic `O(h⁴)` five-point discrete Laplacian bound for `M_k(l, τ)`
across all `|l| + |h| < 1/8` and `τ ∈ ℝ` (`k ≥ 2`):**
`|(M_k(l + h, τ) + M_k(l − h, τ) − 2 M_k(l, τ)) +
  (M_k(l, τ + h) + M_k(l, τ − h) − 2 M_k(l, τ))| ≤
  (27033600 · ν.real univ / (1/8 − |l| − |h|)) · h⁴`. -/
theorem abs_oscillatoryMellin_fivePoint_laplacian_le_pow_four
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)| ≤
      (27033600 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by
  have h1 := abs_oscillatoryMellin_horiz_central_diff_sub_sq_le hk hν hlh τ
  have h2 := abs_oscillatoryMellin_vert_central_diff_add_sq_le hk hν hlh τ
  have hsplit :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      (((∫ x in Ioi (0 : ℝ),
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
      (((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    ring
  rw [hsplit]
  exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

/-- **Height-uniform quartic `O(h⁴)` five-point discrete Laplacian bound for `N_k(l, τ)`
across all `|l| + |h| < 1/8` and `τ ∈ ℝ` (`k ≥ 2`):**
`|(N_k(l + h, τ) + N_k(l − h, τ) − 2 N_k(l, τ)) +
  (N_k(l, τ + h) + N_k(l, τ − h) − 2 N_k(l, τ))| ≤
  (27033600 · ν.real univ / (1/8 − |l| − |h|)) · h⁴`. -/
theorem abs_sineMellin_fivePoint_laplacian_le_pow_four
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)| ≤
      (27033600 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by
  have h1 := abs_sineMellin_horiz_central_diff_sub_sq_le hk hν hlh τ
  have h2 := abs_sineMellin_vert_central_diff_add_sq_le hk hν hlh τ
  have hsplit :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      (((∫ x in Ioi (0 : ℝ),
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
      (((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        h ^ 2 * (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    ring
  rw [hsplit]
  exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

/-- **Global harmonicity (`Δ M_k(l, τ) = 0`) of the real oscillatory Mellin transform across
`|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((M_k(l + h, τ) + M_k(l − h, τ) − 2 M_k(l, τ)) +
  (M_k(l, τ + h) + M_k(l, τ − h) − 2 M_k(l, τ))) / h² → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h1 := tendsto_div_sq_oscillatoryMellin_horiz_central_diff_nhds_zero hk hν hl τ
  have h2 := tendsto_div_sq_oscillatoryMellin_vert_central_diff_nhds_zero hk hν hl τ
  have hsum := h1.add h2
  rw [add_neg_cancel] at hsum
  exact hsum.congr fun h => by ring

/-- **Global harmonicity (`Δ N_k(l, τ) = 0`) of the conjugate sine oscillatory Mellin transform
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((N_k(l + h, τ) + N_k(l − h, τ) − 2 N_k(l, τ)) +
  (N_k(l, τ + h) + N_k(l, τ − h) − 2 N_k(l, τ))) / h² → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sineMellin_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h1 := tendsto_div_sq_sineMellin_horiz_central_diff_nhds_zero hk hν hl τ
  have h2 := tendsto_div_sq_sineMellin_vert_central_diff_nhds_zero hk hν hl τ
  have hsum := h1.add h2
  rw [add_neg_cancel] at hsum
  exact hsum.congr fun h => by ring


/-! ## Section 3: Complex Modulus Squared `|F_k(l, τ)|² = M_k(l, τ)² + N_k(l, τ)²`, Critical-Line Transverse Curvature, and Isotropic Conformal Zero-Opening Law -/

/-- **Functional equation reflection symmetry `l ↦ −l` for the complex oscillatory Mellin
modulus squared `M_k(l, τ)² + N_k(l, τ)²` (`k ≥ 1`, `l, τ ∈ ℝ`):**
`M_k(−l, τ)² + N_k(−l, τ)² = M_k(l, τ)² + N_k(l, τ)²`. -/
theorem sq_oscillatoryMellin_add_sq_sineMellin_neg_left
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 =
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  rw [setIntegral_Ioi_rpow_neg_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector hk ν l τ,
    setIntegral_Ioi_rpow_neg_mul_sin_log_eq_neg hk ν l τ, neg_sq]

/-- **Conjugation reflection symmetry `τ ↦ −τ` for the complex oscillatory Mellin
modulus squared `M_k(l, τ)² + N_k(l, τ)²` (`k ≥ 1`, `l, τ ∈ ℝ`):**
`M_k(l, −τ)² + N_k(l, −τ)² = M_k(l, τ)² + N_k(l, τ)²`. -/
theorem sq_oscillatoryMellin_add_sq_sineMellin_neg_right
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 =
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  rw [setIntegral_Ioi_rpow_mul_cos_neg_log_mul_arcLineInfiniteDyadicVector hk ν l τ,
    setIntegral_Ioi_rpow_mul_sin_neg_log_eq_neg k ν l τ, neg_sq]

/-- **Critical-line reduction (`l = 0`) of the complex oscillatory Mellin modulus squared (`k ≥ 1`, `τ ∈ ℝ`):**
`M_k(0, τ)² + N_k(0, τ)² = M_k(0, τ)²`. -/
theorem sq_oscillatoryMellin_add_sq_sineMellin_zero_left
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 =
    (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  rw [setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk ν τ]
  ring

/-- **Real-axis reduction (`τ = 0`) of the complex oscillatory Mellin modulus squared (`k : ℕ`, `l ∈ ℝ`):**
`M_k(l, 0)² + N_k(l, 0)² = (∫_{x > 0} x^{l − 1/2} V_k(x) dx)²`. -/
theorem sq_oscillatoryMellin_add_sq_sineMellin_zero_right
    (k : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (0 * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (0 * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 =
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  simp

/-- **Universal continuity helper from a punctured difference-quotient limit:**
If `(F h − F₀) / h → D` as `h → 0` (`h ≠ 0`), then `F h → F₀` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_of_tendsto_div_nhdsWithin_zero
    {F : ℝ → ℝ} {F₀ D : ℝ}
    (hD : Tendsto (fun h : ℝ => (F h - F₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D)) :
    Tendsto F (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds F₀) := by
  have hid : Tendsto (fun h : ℝ => h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hmul : Tendsto (fun h : ℝ => ((F h - F₀) / h) * h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    simpa using hD.mul hid
  have hadd : Tendsto (fun h : ℝ => F₀ + ((F h - F₀) / h) * h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds F₀) := by
    simpa using tendsto_const_nhds.add hmul
  refine hadd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh_ne
  simp only [mem_compl_singleton_iff] at hh_ne
  rw [div_mul_cancel₀ _ hh_ne, add_sub_cancel]

/-- **Exact quadratic opening rate of the conjugate sine Mellin transform squared `N_k(l, τ)²`
across the critical line `l = 0` (`k ≥ 2`, `τ ∈ ℝ`):**
`N_k(l, τ)² / l² → (∫_ℝ v sin(τv) Φ_k(v) dv)²` as `l → 0` (`l ≠ 0`). -/
theorem tendsto_div_sq_sineMellin_sq_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun l : ℝ =>
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 / l ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds ((∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by
  have h1 := (tendsto_div_sineMellin_nhds_zero hk hν τ).pow 2
  exact h1.congr fun l => div_pow _ _ 2

/-- **Exact second-order horizontal curvature of the squared real oscillatory Mellin transform
`M_k(l, τ)²` across the critical line `l = 0` (`k ≥ 2`, `τ ∈ ℝ`):**
`(M_k(l, τ)² − M_k(0, τ)²) / l² → M_k(0, τ) · (∫_ℝ v² cos(τv) Φ_k(v) dv)` as `l → 0` (`l ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_sq_sub_criticalLine_sq_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun l : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
          (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) / l ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        ((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  set M₀ := ∫ x in Ioi (0 : ℝ),
    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set I₂ := ∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v
  have hD1 :
      Tendsto
        (fun l : ℝ =>
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) - M₀) / l)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds 0) :=
    (tendsto_div_oscillatoryMellin_sub_criticalLine_nhds_zero hk hν τ).mono_left nhdsWithin_le_nhds
  have hcont :
      Tendsto
        (fun l : ℝ =>
          ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds M₀) :=
    tendsto_of_tendsto_div_nhdsWithin_zero hD1
  have hsum :
      Tendsto
        (fun l : ℝ =>
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) + M₀)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (M₀ + M₀)) :=
    hcont.add tendsto_const_nhds
  have hcurv := tendsto_div_sq_oscillatoryMellin_sub_criticalLine_nhds_zero hk hν τ
  have hprod := hsum.mul hcurv
  have htarget : (M₀ + M₀) * ((1 / 2 : ℝ) * I₂) = M₀ * I₂ := by ring
  rw [htarget] at hprod
  exact hprod.congr fun l => by ring

/-- **Exact critical-line transverse curvature of the complex oscillatory Mellin modulus squared
`|F_k(l, τ)|² = M_k(l, τ)² + N_k(l, τ)²` across `l = 0` (`k ≥ 2`, `τ ∈ ℝ`):**
`((M_k(l, τ)² + N_k(l, τ)²) − M_k(0, τ)²) / l² →
  M_k(0, τ) · (∫_ℝ v² cos(τv) Φ_k(v) dv) + (∫_ℝ v sin(τv) Φ_k(v) dv)²`
as `l → 0` (`l ≠ 0`). -/
theorem tendsto_div_sq_complexModulusSq_sub_criticalLine_sq_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun l : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) / l ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        ((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by
  have h1 := tendsto_div_sq_oscillatoryMellin_sq_sub_criticalLine_sq_nhds_zero hk hν τ
  have h2 := tendsto_div_sq_sineMellin_sq_nhds_zero hk hν τ
  exact (h1.add h2).congr fun l => by ring

/-- **Isotropic Conformal Zero-Opening Law at any critical-line zero `M_k(0, τ₀) = 0` (`k ≥ 2`):**
At any height `τ₀ ∈ ℝ` where `M_k(0, τ₀) = 0`, both the horizontal off-line quadratic opening
rate `(M_k(l, τ₀)² + N_k(l, τ₀)²) / l²` (`l → 0`, `l ≠ 0`) and the vertical critical-line
quadratic opening rate `(M_k(0, τ₀ + h)² + N_k(0, τ₀ + h)²) / h²` (`h → 0`, `h ≠ 0`) converge
to the exact same non-negative conformal slope squared `(∫_ℝ v sin(τ₀ v) Φ_k(v) dv)² ≥ 0`. -/
theorem tendsto_div_sq_complexModulusSq_isotropic_at_criticalLine_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {τ₀ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0) :
    Tendsto
      (fun l : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) / l ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds ((∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) ∧
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds ((∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by
  have hk1 : 1 ≤ k := by omega
  constructor
  · have hhoriz := tendsto_div_sq_complexModulusSq_sub_criticalLine_sq_nhds_zero hk hν τ₀
    rw [hzero, zero_mul, zero_add] at hhoriz
    exact hhoriz.congr fun l => by ring
  · have hl0 : |(0 : ℝ)| < 1 / 8 := by norm_num
    have hvert := tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl0 τ₀
    simp only [zero_sub, zero_mul, Real.cosh_zero, mul_one] at hvert
    rw [hzero] at hvert
    have hvert_sq := hvert.pow 2
    rw [neg_sq] at hvert_sq
    refine hvert_sq.congr fun h => ?_
    rw [sub_zero, div_pow, sq_oscillatoryMellin_add_sq_sineMellin_zero_left hk1 ν (τ₀ + h)]


/-! ## Section 4: Global Five-Point Subharmonic Laplacian Law for `|F_k(l, τ)|²` and Harmonicity of `Re(F_k²)` -/

/-- **Punctured-neighborhood reflection invariance `h ↦ −h` on `nhdsWithin 0 {0}ᶜ`.** -/
theorem tendsto_neg_nhdsWithin_zero :
    Tendsto (fun h : ℝ => -h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h0 : Tendsto (fun h : ℝ => -h) (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
      simpa using continuous_neg.tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [mem_compl_singleton_iff] at hh ⊢
    exact neg_ne_zero.mpr hh

/-- **Universal algebraic identity for the second central difference of a square:**
For all `x, y, z, h ∈ ℝ`,
`((x² + y² − 2 z²) / h²) = 2 z ((x + y − 2 z) / h²) + ((x − z) / h)² + ((y − z) / (−h))²`. -/
theorem central_diff_sq_div_sq_eq (x y z h : ℝ) :
    (x ^ 2 + y ^ 2 - 2 * z ^ 2) / h ^ 2 =
      2 * z * ((x + y - 2 * z) / h ^ 2) + ((x - z) / h) ^ 2 + ((y - z) / (-h)) ^ 2 := by
  rw [div_pow, div_pow, neg_sq]
  ring

/-- **Universal limit theorem for the second central difference of a squared function `F(h)²`:**
If `(F h − F₀) / h → D₁` and `(F h + F (−h) − 2 F₀) / h² → D₂` as `h → 0` (`h ≠ 0`), then
`((F h)² + (F (−h))² − 2 F₀²) / h² → 2 F₀ D₂ + 2 D₁²` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_central_diff_sq_nhdsWithin_zero
    {F : ℝ → ℝ} {F₀ D₁ D₂ : ℝ}
    (hD1 : Tendsto (fun h : ℝ => (F h - F₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D₁))
    (hD2 : Tendsto (fun h : ℝ => (F h + F (-h) - 2 * F₀) / h ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D₂)) :
    Tendsto
      (fun h : ℝ => ((F h) ^ 2 + (F (-h)) ^ 2 - 2 * F₀ ^ 2) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (2 * F₀ * D₂ + 2 * D₁ ^ 2)) := by
  have h1 : Tendsto (fun h : ℝ => 2 * F₀ * ((F h + F (-h) - 2 * F₀) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * F₀ * D₂)) :=
    hD2.const_mul (2 * F₀)
  have h2 : Tendsto (fun h : ℝ => ((F h - F₀) / h) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (D₁ ^ 2)) :=
    hD1.pow 2
  have h3 : Tendsto (fun h : ℝ => ((F (-h) - F₀) / (-h)) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (D₁ ^ 2)) :=
    (hD1.comp tendsto_neg_nhdsWithin_zero).pow 2
  have hsum := (h1.add h2).add h3
  have htarget : 2 * F₀ * D₂ + D₁ ^ 2 + D₁ ^ 2 = 2 * F₀ * D₂ + 2 * D₁ ^ 2 := by ring
  rw [htarget] at hsum
  exact hsum.congr fun h => (central_diff_sq_div_sq_eq (F h) (F (-h)) F₀ h).symm

/-- **Global five-point subharmonic Laplacian limit for `M_k(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((M_k(l + h, τ)² + M_k(l − h, τ)² − 2 M_k(l, τ)²) +
  (M_k(l, τ + h)² + M_k(l, τ − h)² − 2 M_k(l, τ)²)) / h² →
  2 ((∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv)² + (∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv)²) ≥ 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_sq_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
            2 * (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
            2 * (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  have hD1_l := tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ
  have hD2_l :
      Tendsto
        (fun h : ℝ =>
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l + -h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    (tendsto_div_sq_oscillatoryMellin_horiz_central_diff_nhds_zero hk hν hl τ).congr fun h => by
      rw [← sub_eq_add_neg]
  have h_horiz := tendsto_div_sq_central_diff_sq_nhdsWithin_zero hD1_l hD2_l
  have hD1_τ := tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ
  have hD2_τ :
      Tendsto
        (fun h : ℝ =>
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + -h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (-(∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) :=
    (tendsto_div_sq_oscillatoryMellin_vert_central_diff_nhds_zero hk hν hl τ).congr fun h => by
      rw [← sub_eq_add_neg]
  have h_vert := tendsto_div_sq_central_diff_sq_nhdsWithin_zero hD1_τ hD2_τ
  have hsum := h_horiz.add h_vert
  refine (hsum.congr fun h => ?_).trans_eq ?_
  · rw [← sub_eq_add_neg, ← sub_eq_add_neg]
    ring
  · congr 1
    ring

/-- **Global five-point subharmonic Laplacian limit for `N_k(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((N_k(l + h, τ)² + N_k(l − h, τ)² − 2 N_k(l, τ)²) +
  (N_k(l, τ + h)² + N_k(l, τ − h)² − 2 N_k(l, τ)²)) / h² →
  2 ((∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv)² + (∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv)²) ≥ 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sineMellin_sq_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
            2 * (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
            2 * (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  have hD1_l := tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ
  have hD2_l :
      Tendsto
        (fun h : ℝ =>
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l + -h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    (tendsto_div_sq_sineMellin_horiz_central_diff_nhds_zero hk hν hl τ).congr fun h => by
      rw [← sub_eq_add_neg]
  have h_horiz := tendsto_div_sq_central_diff_sq_nhdsWithin_zero hD1_l hD2_l
  have hD1_τ := tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ
  have hD2_τ :
      Tendsto
        (fun h : ℝ =>
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + -h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h ^ 2)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (-(∫ v : ℝ, v ^ 2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) :=
    (tendsto_div_sq_sineMellin_vert_central_diff_nhds_zero hk hν hl τ).congr fun h => by
      rw [← sub_eq_add_neg]
  have h_vert := tendsto_div_sq_central_diff_sq_nhdsWithin_zero hD1_τ hD2_τ
  have hsum := h_horiz.add h_vert
  refine (hsum.congr fun h => ?_).trans_eq ?_
  · rw [← sub_eq_add_neg, ← sub_eq_add_neg]
    ring
  · congr 1
    ring

/-- **Global Five-Point Subharmonic Laplacian Law (`Δ |F_k(l, τ)|² = 4 (|∂_l M_k|² + |∂_l N_k|²) ≥ 0`)
for the complex oscillatory Mellin modulus squared `M_k(l, τ)² + N_k(l, τ)²` across
`|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(((|F_k(l + h, τ)|² + |F_k(l − h, τ)|² − 2 |F_k(l, τ)|²) +
   (|F_k(l, τ + h)|² + |F_k(l, τ − h)|² − 2 |F_k(l, τ)|²)) / h²) →
  4 ((∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv)² + (∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv)²) ≥ 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_complexModulusSq_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
            ((∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
            2 * ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
          (((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
            ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
            2 * ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  have h1 := tendsto_div_sq_oscillatoryMellin_sq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have h2 := tendsto_div_sq_sineMellin_sq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hsum := h1.add h2
  refine (hsum.congr fun h => by ring).trans_eq ?_
  congr 1
  ring

/-- **Global Harmonicity (`Δ (M_k(l, τ)² − N_k(l, τ)²) = 0`) of the real part of the holomorphic
square `Re(F_k(l, τ)²) = M_k(l, τ)² − N_k(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):** -/
theorem tendsto_div_sq_realPartSq_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
              (∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
            ((∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
            2 * ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
          (((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
            ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
            2 * ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h1 := tendsto_div_sq_oscillatoryMellin_sq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have h2 := tendsto_div_sq_sineMellin_sq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hsub := h1.sub h2
  rw [sub_self] at hsub
  exact hsub.congr fun h => by ring

/-- **Master Harmonic Laplacian & Subharmonic Complex Modulus Witness Theorem for the
Infinite-Horizon Dyadic Modular Arc Tower:**
There exists a symmetric finite non-zero Borel measure `ν` on `ArcParam` such that for every
integer generator `k ≥ 2`:
1. (**Height-uniform quartic `O(h⁴)` five-point discrete Laplacian bounds across `|l| + |h| < 1/8`, `τ ∈ ℝ`**):
   `|(M_k(l + h, τ) + M_k(l − h, τ) − 2 M_k(l, τ)) + (M_k(l, τ + h) + M_k(l, τ − h) − 2 M_k(l, τ))| ≤
     (27033600 · ν.real univ / (1/8 − |l| − |h|)) · h⁴`
   and
   `|(N_k(l + h, τ) + N_k(l − h, τ) − 2 N_k(l, τ)) + (N_k(l, τ + h) + N_k(l, τ − h) − 2 N_k(l, τ))| ≤
     (27033600 · ν.real univ / (1/8 − |l| − |h|)) · h⁴`.
2. (**Critical-line transverse curvature of the complex modulus squared `|F_k(l, τ)|² = M_k(l, τ)² + N_k(l, τ)²`**):
   For every `τ ∈ ℝ`, as `l → 0` (`l ≠ 0`),
   `((M_k(l, τ)² + N_k(l, τ)²) − M_k(0, τ)²) / l² →
     M_k(0, τ) (∫_ℝ v² cos(τv) Φ_k(v) dv) + (∫_ℝ v sin(τv) Φ_k(v) dv)²`.
3. (**Global five-point subharmonic Laplacian law for `|F_k(l, τ)|² = M_k(l, τ)² + N_k(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ`**):
   `((Δ_l² (M_k² + N_k²)(l, τ; h) + Δ_τ² (M_k² + N_k²)(l, τ; h)) / h²) →
     4 ((∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv)² + (∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv)²) ≥ 0`
   as `h → 0` (`h ≠ 0`). -/
theorem exists_dyadic_harmonicLaplacian_subharmonicModulus_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l h : ℝ⦄, |l| + |h| < 1 / 8 → ∀ τ : ℝ,
          |((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              2 * ∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              2 * ∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)| ≤
            (27033600 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 ∧
          |((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              2 * ∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              2 * ∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)| ≤
            (27033600 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4) ∧
        (∀ τ : ℝ,
          Tendsto
            (fun l : ℝ =>
              (((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                (∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) / l ^ 2)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              ((((∫ x in Ioi (0 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                  ((∫ x in Ioi (0 : ℝ),
                      x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                  2 * ((∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                (((∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                  ((∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                  2 * ((∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)))) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk => ?_⟩
  refine ⟨fun l h hlh τ =>
    ⟨abs_oscillatoryMellin_fivePoint_laplacian_le_pow_four hk hν hlh τ,
     abs_sineMellin_fivePoint_laplacian_le_pow_four hk hν hlh τ⟩,
    fun τ => tendsto_div_sq_complexModulusSq_sub_criticalLine_sq_nhds_zero hk hν τ,
    fun l hl τ => tendsto_div_sq_complexModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ⟩

end

end RHTower
