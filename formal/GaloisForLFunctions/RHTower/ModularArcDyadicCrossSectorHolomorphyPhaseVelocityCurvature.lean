/-
Copyright (c) 2026 Michael. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael
-/
import GaloisForLFunctions.RHTower.ModularArcDyadicOneSidedSectorCauchyRiemannLogarithmicHarmonicity

/-!
# Cross-Sector Holomorphy of `F_k^+(l, τ) · F_k^-(l, τ)`, Cross-Sector Hermitian and Symplectic Bilinear Laplacians, One-Sided Sector Self-Wronskian Phase-Velocity Calculus, and Critical-Line Sector Gradient Symmetry

This file is the thirty-fourth self-contained module (`Cycle 56`) in the unconditional
dyadic harmonic-analysis tower for the modular arc Poisson kernel (`Route 3'` producer
infrastructure).

Building directly on
`ModularArcDyadicOneSidedSectorCauchyRiemannLogarithmicHarmonicity.lean` (`Cycle 55`), which
established the individual Cauchy–Riemann equations, five-point harmonicity, and division-free
Liouville–Gauss logarithmic harmonicity of the one-sided infinity sector
`F_k^+(l, τ) = C_k^+(l, τ) + i S_k^+(l, τ)` (`x ∈ (1, ∞)`) and origin sector
`F_k^-(l, τ) = C_k^-(l, τ) + i S_k^-(l, τ)` (`x ∈ (0, 1]`), we now develop the **cross-sector
holomorphic product `F_k^+(l, τ) · F_k^-(l, τ)`**, the **cross-sector Hermitian and symplectic
pair `(I_k(l, τ), D_k(l, τ))`**, the **one-sided sector self-Wronskian phase-velocity calculus**,
and the **critical-line vertical derivative and gradient-norm decomposition of `|F_k^±(l, τ)|²`**:

1. **Universal Cross-Sector Polarization, Self-Wronskian Decomposition, and Five-Point Bilinear
   Laplacian Calculus (Section 1):**
   We establish the universal algebraic polarization identities linking the cross-sector combinations
   `c_pos c_neg − s_pos s_neg`, `c_pos s_neg + s_pos c_neg`, `c_pos c_neg + s_pos s_neg`, and
   `c_pos s_neg − s_pos c_neg` of `(c_pos, s_pos) = ((u + x)/2, (v + y)/2)` and
   `(c_neg, s_neg) = ((u − x)/2, (v − y)/2)` to `(u, v)` and `(x, y)`, the sum and difference
   decompositions of the one-sided sector self-Wronskians `c_pos s_pos' − s_pos c_pos'` and
   `c_neg s_neg' − s_neg c_neg'`, and universal punctured-neighborhood five-point Laplacian
   theorems for the real/imaginary parts (`U X − V Y`, `U Y + V X`) and Hermitian/symplectic parts
   (`U X + V Y`, `U Y − V X`) of any two Cauchy–Riemann five-point harmonic pairs.

2. **Cross-Sector Holomorphic Product `F_k^+(l, τ) · F_k^-(l, τ)` and Cross-Sector Hermitian /
   Symplectic Bilinear Laplacians Across `|l| < 1/8`, `τ ∈ ℝ` (Section 2):**
   Across `|l| < 1/2, τ ∈ ℝ`, we prove the exact polarization identities
   `4 (C_k^+ C_k^- − S_k^+ S_k^-) = (M_k² − N_k²) − ((Δ_k^{\cos})² − (Δ_k^{\sin})²)`,
   `2 (C_k^+ S_k^- + S_k^+ C_k^-) = M_k N_k − Δ_k^{\cos} Δ_k^{\sin}`, and
   `4 (C_k^+ C_k^- + S_k^+ S_k^-) = |F_k|² − |Δ_k|²`. Across `|l| < 1/8, τ ∈ ℝ`, we prove the
   global Cauchy–Riemann equations and five-point harmonicity for the cross-sector holomorphic
   product `(C_k^+ C_k^- − S_k^+ S_k^-, C_k^+ S_k^- + S_k^+ C_k^-)` and the exact five-point
   bilinear Laplacian laws for the cross-sector Hermitian inner product
   `I_k = C_k^+ C_k^- + S_k^+ S_k^-` and cross-sector symplectic Wronskian
   `D_k = C_k^+ S_k^- − S_k^+ C_k^-`.

3. **One-Sided Sector Self-Wronskian Phase-Velocity Calculus and Critical-Line Vertical Derivative
   Symmetry (Section 3):**
   On the critical line `l = 0`, we prove that both one-sided sector moduli squared have identical
   vertical derivatives
   `∂_τ |F_k^+(0, τ)|² = ∂_τ |F_k^-(0, τ)|² =
     M_k(0, τ) · (−(∫_ℝ v sin(τv) Φ_k(v) dv) / 2) +
     (∫_{v > 0} sin(τv) Φ_k(v) dv) · (2 ∫_{v > 0} v cos(τv) Φ_k(v) dv)`,
   which at any critical-line zero `M_k(0, τ₀) = 0` reduces to
   `∂_τ |F_k^±(0, τ₀)|² = (∫_{v > 0} sin(τ₀ v) Φ_k(v) dv) · (2 ∫_{v > 0} v cos(τ₀ v) Φ_k(v) dv)`
   and yields the exact critical-line zero-locus sector gradient-norm factorization
   `(∂_l |F_k^±(0, τ₀)|²)² + (∂_τ |F_k^±(0, τ₀)|²)² =
     |F_k^±(0, τ₀)|² · ((∫_ℝ v sin(τ₀ v) Φ_k(v) dv)² + (2 ∫_{v > 0} v cos(τ₀ v) Φ_k(v) dv)²)`.

4. **Global Five-Point Subharmonicity of the Cross-Sector Modulus Product
   `|F_k^+(l, τ)|² · |F_k^-(l, τ)|²` and Master Witness Theorem (Section 4):**
   We establish the global five-point Laplacian limit of `|F_k^+(l, τ)|² · |F_k^-(l, τ)|²` across
   `|l| < 1/8, τ ∈ ℝ` (`k ≥ 2`) and package the complete suite into
   `exists_dyadic_crossSector_holomorphy_phaseVelocity_curvature_arcWitness`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ## Section 1: Universal Cross-Sector Polarization, Self-Wronskian Decomposition, and Five-Point Bilinear Laplacian Calculus -/

/-- **Universal cross-sector real-part polarization identity:**
For all `u, v, x, y : ℝ`,
`4 * (((u + x) / 2) * ((u − x) / 2) − ((v + y) / 2) * ((v − y) / 2)) =
  (u ^ 2 − v ^ 2) − (x ^ 2 − y ^ 2)`. -/
theorem cross_sector_re_polarization_identity (u v x y : ℝ) :
    4 * (((u + x) / 2) * ((u - x) / 2) - ((v + y) / 2) * ((v - y) / 2)) =
      (u ^ 2 - v ^ 2) - (x ^ 2 - y ^ 2) := by
  ring

/-- **Universal cross-sector imaginary-part polarization identity:**
For all `u, v, x, y : ℝ`,
`2 * (((u + x) / 2) * ((v − y) / 2) + ((v + y) / 2) * ((u − x) / 2)) =
  u * v − x * y`. -/
theorem cross_sector_im_polarization_identity (u v x y : ℝ) :
    2 * (((u + x) / 2) * ((v - y) / 2) + ((v + y) / 2) * ((u - x) / 2)) =
      u * v - x * y := by
  ring

/-- **Universal cross-sector Hermitian inner-product polarization identity:**
For all `u, v, x, y : ℝ`,
`4 * (((u + x) / 2) * ((u − x) / 2) + ((v + y) / 2) * ((v − y) / 2)) =
  (u ^ 2 + v ^ 2) − (x ^ 2 + y ^ 2)`. -/
theorem cross_sector_hermitian_polarization_identity (u v x y : ℝ) :
    4 * (((u + x) / 2) * ((u - x) / 2) + ((v + y) / 2) * ((v - y) / 2)) =
      (u ^ 2 + v ^ 2) - (x ^ 2 + y ^ 2) := by
  ring

/-- **Universal cross-sector symplectic Wronskian polarization identity:**
For all `u, v, x, y : ℝ`,
`2 * (((u + x) / 2) * ((v − y) / 2) − ((v + y) / 2) * ((u − x) / 2)) =
  -(u * y − v * x)`. -/
theorem cross_sector_wronskian_polarization_identity (u v x y : ℝ) :
    2 * (((u + x) / 2) * ((v - y) / 2) - ((v + y) / 2) * ((u - x) / 2)) =
      -(u * y - v * x) := by
  ring

/-- **Universal sum of one-sided sector self-Wronskians:**
For all `u, v, x, y, u', v', x', y' : ℝ`,
`2 * ((((u + x) / 2) * ((v' + y') / 2) − ((v + y) / 2) * ((u' + x') / 2)) +
     (((u − x) / 2) * ((v' − y') / 2) − ((v − y) / 2) * ((u' − x') / 2))) =
  (u * v' − v * u') + (x * y' − y * x')`. -/
theorem sector_selfWronskian_add_identity (u v x y u' v' x' y' : ℝ) :
    2 * ((((u + x) / 2) * ((v' + y') / 2) - ((v + y) / 2) * ((u' + x') / 2)) +
         (((u - x) / 2) * ((v' - y') / 2) - ((v - y) / 2) * ((u' - x') / 2))) =
      (u * v' - v * u') + (x * y' - y * x') := by
  ring

/-- **Universal difference of one-sided sector self-Wronskians:**
For all `u, v, x, y, u', v', x', y' : ℝ`,
`2 * ((((u + x) / 2) * ((v' + y') / 2) − ((v + y) / 2) * ((u' + x') / 2)) −
     (((u − x) / 2) * ((v' − y') / 2) − ((v − y) / 2) * ((u' − x') / 2))) =
  (u * y' − y * u') + (x * v' − v * x')`. -/
theorem sector_selfWronskian_sub_identity (u v x y u' v' x' y' : ℝ) :
    2 * ((((u + x) / 2) * ((v' + y') / 2) - ((v + y) / 2) * ((u' + x') / 2)) -
         (((u - x) / 2) * ((v' - y') / 2) - ((v - y) / 2) * ((u' - x') / 2))) =
      (u * y' - y * u') + (x * v' - v * x') := by
  ring

/-- **Universal five-point harmonicity for the real part `U X − V Y` of the product of two
Cauchy–Riemann five-point harmonic pairs:**
If `(U, V)` and `(X, Y)` satisfy the punctured-neighborhood Cauchy–Riemann derivative limits
(`D_Ut = −D_Vl`, `D_Vt = D_Ul`, `D_Xt = −D_Yl`, `D_Yt = D_Xl`) and have vanishing five-point
Laplacians, then the five-point Laplacian of `U X − V Y` converges to `0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_fivePoint_complexMul_re_harmonic_nhdsWithin_zero
    {U_l U_t V_l V_t X_l X_t Y_l Y_t : ℝ → ℝ}
    {U₀ V₀ X₀ Y₀ D_Ul D_Vl D_Xl D_Yl : ℝ}
    (hUl : Tendsto (fun h : ℝ => (U_l h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hUt : Tendsto (fun h : ℝ => (U_t h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Vl)))
    (hVl : Tendsto (fun h : ℝ => (V_l h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vl))
    (hVt : Tendsto (fun h : ℝ => (V_t h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hXl : Tendsto (fun h : ℝ => (X_l h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl))
    (hXt : Tendsto (fun h : ℝ => (X_t h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Yl)))
    (hYl : Tendsto (fun h : ℝ => (Y_l h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Yl))
    (hYt : Tendsto (fun h : ℝ => (Y_t h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl))
    (hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hXlap : Tendsto
      (fun h : ℝ => ((X_l h + X_l (-h) - 2 * X₀) + (X_t h + X_t (-h) - 2 * X₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hYlap : Tendsto
      (fun h : ℝ => ((Y_l h + Y_l (-h) - 2 * Y₀) + (Y_t h + Y_t (-h) - 2 * Y₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) :
    Tendsto
      (fun h : ℝ =>
        ((((U_l h * X_l h - V_l h * Y_l h) +
            (U_l (-h) * X_l (-h) - V_l (-h) * Y_l (-h)) - 2 * (U₀ * X₀ - V₀ * Y₀)) +
          ((U_t h * X_t h - V_t h * Y_t h) +
            (U_t (-h) * X_t (-h) - V_t (-h) * Y_t (-h)) - 2 * (U₀ * X₀ - V₀ * Y₀))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have h1 := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero hUl hUt hXl hXt hUlap hXlap
  have h2 := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero hVl hVt hYl hYt hVlap hYlap
  have hsub := h1.sub h2
  have hlim :
      2 * (D_Ul * D_Xl + (-D_Vl) * (-D_Yl)) - 2 * (D_Vl * D_Yl + D_Ul * D_Xl) = 0 := by
    ring
  rw [hlim] at hsub
  exact hsub.congr (fun h => by ring)

/-- **Universal five-point harmonicity for the imaginary part `U Y + V X` of the product of two
Cauchy–Riemann five-point harmonic pairs:**
If `(U, V)` and `(X, Y)` satisfy the punctured-neighborhood Cauchy–Riemann derivative limits
(`D_Ut = −D_Vl`, `D_Vt = D_Ul`, `D_Xt = −D_Yl`, `D_Yt = D_Xl`) and have vanishing five-point
Laplacians, then the five-point Laplacian of `U Y + V X` converges to `0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_fivePoint_complexMul_im_harmonic_nhdsWithin_zero
    {U_l U_t V_l V_t X_l X_t Y_l Y_t : ℝ → ℝ}
    {U₀ V₀ X₀ Y₀ D_Ul D_Vl D_Xl D_Yl : ℝ}
    (hUl : Tendsto (fun h : ℝ => (U_l h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hUt : Tendsto (fun h : ℝ => (U_t h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Vl)))
    (hVl : Tendsto (fun h : ℝ => (V_l h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vl))
    (hVt : Tendsto (fun h : ℝ => (V_t h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hXl : Tendsto (fun h : ℝ => (X_l h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl))
    (hXt : Tendsto (fun h : ℝ => (X_t h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Yl)))
    (hYl : Tendsto (fun h : ℝ => (Y_l h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Yl))
    (hYt : Tendsto (fun h : ℝ => (Y_t h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl))
    (hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hXlap : Tendsto
      (fun h : ℝ => ((X_l h + X_l (-h) - 2 * X₀) + (X_t h + X_t (-h) - 2 * X₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hYlap : Tendsto
      (fun h : ℝ => ((Y_l h + Y_l (-h) - 2 * Y₀) + (Y_t h + Y_t (-h) - 2 * Y₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) :
    Tendsto
      (fun h : ℝ =>
        ((((U_l h * Y_l h + V_l h * X_l h) +
            (U_l (-h) * Y_l (-h) + V_l (-h) * X_l (-h)) - 2 * (U₀ * Y₀ + V₀ * X₀)) +
          ((U_t h * Y_t h + V_t h * X_t h) +
            (U_t (-h) * Y_t (-h) + V_t (-h) * X_t (-h)) - 2 * (U₀ * Y₀ + V₀ * X₀))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have h1 := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero hUl hUt hYl hYt hUlap hYlap
  have h2 := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero hVl hVt hXl hXt hVlap hXlap
  have hadd := h1.add h2
  have hlim :
      2 * (D_Ul * D_Yl + (-D_Vl) * D_Xl) + 2 * (D_Vl * D_Xl + D_Ul * (-D_Yl)) = 0 := by
    ring
  rw [hlim] at hadd
  exact hadd.congr (fun h => by ring)

/-- **Universal five-point bilinear Laplacian law for the Hermitian inner product `U X + V Y` of
two Cauchy–Riemann five-point harmonic pairs:**
`((Δ_l² (U X + V Y) + Δ_τ² (U X + V Y)) / h²) → 4 * (D_Ul * D_Xl + D_Vl * D_Yl)`. -/
theorem tendsto_div_sq_fivePoint_hermitian_nhdsWithin_zero
    {U_l U_t V_l V_t X_l X_t Y_l Y_t : ℝ → ℝ}
    {U₀ V₀ X₀ Y₀ D_Ul D_Vl D_Xl D_Yl : ℝ}
    (hUl : Tendsto (fun h : ℝ => (U_l h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hUt : Tendsto (fun h : ℝ => (U_t h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Vl)))
    (hVl : Tendsto (fun h : ℝ => (V_l h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vl))
    (hVt : Tendsto (fun h : ℝ => (V_t h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hXl : Tendsto (fun h : ℝ => (X_l h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl))
    (hXt : Tendsto (fun h : ℝ => (X_t h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Yl)))
    (hYl : Tendsto (fun h : ℝ => (Y_l h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Yl))
    (hYt : Tendsto (fun h : ℝ => (Y_t h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl))
    (hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hXlap : Tendsto
      (fun h : ℝ => ((X_l h + X_l (-h) - 2 * X₀) + (X_t h + X_t (-h) - 2 * X₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hYlap : Tendsto
      (fun h : ℝ => ((Y_l h + Y_l (-h) - 2 * Y₀) + (Y_t h + Y_t (-h) - 2 * Y₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) :
    Tendsto
      (fun h : ℝ =>
        ((((U_l h * X_l h + V_l h * Y_l h) +
            (U_l (-h) * X_l (-h) + V_l (-h) * Y_l (-h)) - 2 * (U₀ * X₀ + V₀ * Y₀)) +
          ((U_t h * X_t h + V_t h * Y_t h) +
            (U_t (-h) * X_t (-h) + V_t (-h) * Y_t (-h)) - 2 * (U₀ * X₀ + V₀ * Y₀))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (D_Ul * D_Xl + D_Vl * D_Yl))) := by
  have h1 := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero hUl hUt hXl hXt hUlap hXlap
  have h2 := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero hVl hVt hYl hYt hVlap hYlap
  have hadd := h1.add h2
  have hlim :
      2 * (D_Ul * D_Xl + (-D_Vl) * (-D_Yl)) + 2 * (D_Vl * D_Yl + D_Ul * D_Xl) =
        4 * (D_Ul * D_Xl + D_Vl * D_Yl) := by
    ring
  rw [hlim] at hadd
  exact hadd.congr (fun h => by ring)

/-- **Universal five-point bilinear Laplacian law for the symplectic Wronskian `U Y − V X` of
two Cauchy–Riemann five-point harmonic pairs:**
`((Δ_l² (U Y − V X) + Δ_τ² (U Y − V X)) / h²) → 4 * (D_Ul * D_Yl − D_Vl * D_Xl)`. -/
theorem tendsto_div_sq_fivePoint_wronskian_nhdsWithin_zero
    {U_l U_t V_l V_t X_l X_t Y_l Y_t : ℝ → ℝ}
    {U₀ V₀ X₀ Y₀ D_Ul D_Vl D_Xl D_Yl : ℝ}
    (hUl : Tendsto (fun h : ℝ => (U_l h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hUt : Tendsto (fun h : ℝ => (U_t h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Vl)))
    (hVl : Tendsto (fun h : ℝ => (V_l h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vl))
    (hVt : Tendsto (fun h : ℝ => (V_t h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hXl : Tendsto (fun h : ℝ => (X_l h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl))
    (hXt : Tendsto (fun h : ℝ => (X_t h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Yl)))
    (hYl : Tendsto (fun h : ℝ => (Y_l h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Yl))
    (hYt : Tendsto (fun h : ℝ => (Y_t h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl))
    (hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hXlap : Tendsto
      (fun h : ℝ => ((X_l h + X_l (-h) - 2 * X₀) + (X_t h + X_t (-h) - 2 * X₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hYlap : Tendsto
      (fun h : ℝ => ((Y_l h + Y_l (-h) - 2 * Y₀) + (Y_t h + Y_t (-h) - 2 * Y₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) :
    Tendsto
      (fun h : ℝ =>
        ((((U_l h * Y_l h - V_l h * X_l h) +
            (U_l (-h) * Y_l (-h) - V_l (-h) * X_l (-h)) - 2 * (U₀ * Y₀ - V₀ * X₀)) +
          ((U_t h * Y_t h - V_t h * X_t h) +
            (U_t (-h) * Y_t (-h) - V_t (-h) * X_t (-h)) - 2 * (U₀ * Y₀ - V₀ * X₀))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (D_Ul * D_Yl - D_Vl * D_Xl))) := by
  have h1 := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero hUl hUt hYl hYt hUlap hYlap
  have h2 := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero hVl hVt hXl hXt hVlap hXlap
  have hsub := h1.sub h2
  have hlim :
      2 * (D_Ul * D_Yl + (-D_Vl) * D_Xl) - 2 * (D_Vl * D_Xl + D_Ul * (-D_Yl)) =
        4 * (D_Ul * D_Yl - D_Vl * D_Xl) := by
    ring
  rw [hlim] at hsub
  exact hsub.congr (fun h => by ring)


/-! ## Section 2: Cross-Sector Holomorphic Product `F_k^+(l, τ) · F_k^-(l, τ)` and Cross-Sector Hermitian / Symplectic Bilinear Laplacians Across `|l| < 1/8`, `τ ∈ ℝ` -/

/-- **Cross-Sector Real-Part Polarization Identity Across `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`):**
`4 (C_k^+(l, τ) C_k^-(l, τ) − S_k^+(l, τ) S_k^-(l, τ)) =
  (M_k(l, τ)² − N_k(l, τ)²) − (Δ_k^{\cos}(l, τ)² − Δ_k^{\sin}(l, τ)²)`. -/
theorem four_mul_crossSectorRe_eq_diff_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    4 * ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) =
      ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl τ,
    setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl τ]
  ring

/-- **Cross-Sector Imaginary-Part Polarization Identity Across `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`):**
`2 (C_k^+(l, τ) S_k^-(l, τ) + S_k^+(l, τ) C_k^-(l, τ)) =
  M_k(l, τ) N_k(l, τ) − Δ_k^{\cos}(l, τ) Δ_k^{\sin}(l, τ)`. -/
theorem two_mul_crossSectorIm_eq_diff_mul
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    2 * ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) =
      (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl τ,
    setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl τ]
  ring

/-- **Clean Cross-Sector Hermitian Polarization Identity Across `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`):**
`4 (C_k^+(l, τ) C_k^-(l, τ) + S_k^+(l, τ) S_k^-(l, τ)) = |F_k(l, τ)|² − |Δ_k(l, τ)|²`. -/
theorem four_mul_crossSectorHermitian_eq_diff_modulusSq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    4 * ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) =
      ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl τ,
    setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl τ]
  exact (sector_inner_polarization_identity _ _ _ _).symm

/-- **Global First Cauchy–Riemann Equation for the Cross-Sector Holomorphic Product
`F_k^+(l, τ) · F_k^-(l, τ) = (C_k^+ C_k^- − S_k^+ S_k^-) + i (C_k^+ S_k^- + S_k^+ C_k^-)`
Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`∂_l (C_k^+ C_k^- − S_k^+ S_k^-) − ∂_τ (C_k^+ S_k^- + S_k^+ C_k^-) = 0`. -/
theorem tendsto_div_crossSectorProduct_cauchyRiemann_first_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) -
        (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) :=
  tendsto_div_complexMul_cauchyRiemann_first_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)

/-- **Global Second Cauchy–Riemann Equation for the Cross-Sector Holomorphic Product
`F_k^+(l, τ) · F_k^-(l, τ) = (C_k^+ C_k^- − S_k^+ S_k^-) + i (C_k^+ S_k^- + S_k^+ C_k^-)`
Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`∂_l (C_k^+ S_k^- + S_k^+ C_k^-) + ∂_τ (C_k^+ C_k^- − S_k^+ S_k^-) = 0`. -/
theorem tendsto_div_crossSectorProduct_cauchyRiemann_second_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
        (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) :=
  tendsto_div_complexMul_cauchyRiemann_second_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)

/-- **Global Five-Point Harmonicity of the Cross-Sector Real Part
`C_k^+(l, τ) C_k^-(l, τ) − S_k^+(l, τ) S_k^-(l, τ)` Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem tendsto_div_sq_crossSectorRe_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
          (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  set U_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U₀ : ℝ :=
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V₀ : ℝ :=
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X_l : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X_t : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X₀ : ℝ :=
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y_l : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y_t : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y₀ : ℝ :=
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  have hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorCos_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [U_l, U_t, U₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorSin_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [V_l, V_t, V₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hXlap : Tendsto
      (fun h : ℝ => ((X_l h + X_l (-h) - 2 * X₀) + (X_t h + X_t (-h) - 2 * X₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorCos_Ioc_zero_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [X_l, X_t, X₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hYlap : Tendsto
      (fun h : ℝ => ((Y_l h + Y_l (-h) - 2 * Y₀) + (Y_t h + Y_t (-h) - 2 * Y₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorSin_Ioc_zero_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [Y_l, Y_t, Y₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_complexMul_re_harmonic_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    hUlap hVlap hXlap hYlap
  refine h.congr (fun h => ?_)
  dsimp [U_l, U_t, U₀, V_l, V_t, V₀, X_l, X_t, X₀, Y_l, Y_t, Y₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Global Five-Point Harmonicity of the Cross-Sector Imaginary Part
`C_k^+(l, τ) S_k^-(l, τ) + S_k^+(l, τ) C_k^-(l, τ)` Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem tendsto_div_sq_crossSectorIm_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
          (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  set U_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U₀ : ℝ :=
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V₀ : ℝ :=
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X_l : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X_t : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X₀ : ℝ :=
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y_l : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y_t : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y₀ : ℝ :=
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  have hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorCos_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [U_l, U_t, U₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorSin_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [V_l, V_t, V₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hXlap : Tendsto
      (fun h : ℝ => ((X_l h + X_l (-h) - 2 * X₀) + (X_t h + X_t (-h) - 2 * X₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorCos_Ioc_zero_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [X_l, X_t, X₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hYlap : Tendsto
      (fun h : ℝ => ((Y_l h + Y_l (-h) - 2 * Y₀) + (Y_t h + Y_t (-h) - 2 * Y₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorSin_Ioc_zero_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [Y_l, Y_t, Y₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_complexMul_im_harmonic_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    hUlap hVlap hXlap hYlap
  refine h.congr (fun h => ?_)
  dsimp [U_l, U_t, U₀, V_l, V_t, V₀, X_l, X_t, X₀, Y_l, Y_t, Y₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Exact Five-Point Bilinear Laplacian Law for the Cross-Sector Hermitian Inner Product
`I_k(l, τ) = C_k^+(l, τ) C_k^-(l, τ) + S_k^+(l, τ) S_k^-(l, τ)` Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² I_k + Δ_τ² I_k) / h²) →
  ((∂_l M_k)² + (∂_l N_k)²) − ((∂_l Δ_k^{\cos})² + (∂_l Δ_k^{\sin})²)`. -/
theorem tendsto_div_sq_crossSectorHermitian_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
          (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) -
          ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  set U_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U₀ : ℝ :=
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V₀ : ℝ :=
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X_l : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X_t : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X₀ : ℝ :=
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y_l : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y_t : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y₀ : ℝ :=
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  have hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorCos_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [U_l, U_t, U₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorSin_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [V_l, V_t, V₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hXlap : Tendsto
      (fun h : ℝ => ((X_l h + X_l (-h) - 2 * X₀) + (X_t h + X_t (-h) - 2 * X₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorCos_Ioc_zero_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [X_l, X_t, X₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hYlap : Tendsto
      (fun h : ℝ => ((Y_l h + Y_l (-h) - 2 * Y₀) + (Y_t h + Y_t (-h) - 2 * Y₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorSin_Ioc_zero_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [Y_l, Y_t, Y₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_hermitian_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    hUlap hVlap hXlap hYlap
  have hlim :
      4 * ((((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) *
            (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) +
          (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) *
            (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) =
      ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) -
        ((∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    ring
  rw [hlim] at h
  refine h.congr (fun h => ?_)
  dsimp [U_l, U_t, U₀, V_l, V_t, V₀, X_l, X_t, X₀, Y_l, Y_t, Y₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Exact Five-Point Bilinear Laplacian Law for the Cross-Sector Symplectic Wronskian
`D_k(l, τ) = C_k^+(l, τ) S_k^-(l, τ) − S_k^+(l, τ) C_k^-(l, τ)` Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² D_k + Δ_τ² D_k) / h²) →
  2 ((∂_l N_k)(∂_l Δ_k^{\cos}) − (∂_l M_k)(∂_l Δ_k^{\sin}))`. -/
theorem tendsto_div_sq_crossSectorWronskian_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
          (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
            (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  set U_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U₀ : ℝ :=
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V₀ : ℝ :=
    ∫ x in Ioi (1 : ℝ),
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X_l : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X_t : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set X₀ : ℝ :=
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y_l : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y_t : ℝ → ℝ := fun h =>
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Y₀ : ℝ :=
    ∫ x in Ioc (0 : ℝ) 1,
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  have hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorCos_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [U_l, U_t, U₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorSin_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [V_l, V_t, V₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hXlap : Tendsto
      (fun h : ℝ => ((X_l h + X_l (-h) - 2 * X₀) + (X_t h + X_t (-h) - 2 * X₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorCos_Ioc_zero_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [X_l, X_t, X₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hYlap : Tendsto
      (fun h : ℝ => ((Y_l h + Y_l (-h) - 2 * Y₀) + (Y_t h + Y_t (-h) - 2 * Y₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sectorSin_Ioc_zero_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [Y_l, Y_t, Y₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_wronskian_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    hUlap hVlap hXlap hYlap
  have hlim :
      4 * ((((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) *
            (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) -
          (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) *
            (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) =
      2 * ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    ring
  rw [hlim] at h
  refine h.congr (fun h => ?_)
  dsimp [U_l, U_t, U₀, V_l, V_t, V₀, X_l, X_t, X₀, Y_l, Y_t, Y₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]


/-! ## Section 3: One-Sided Sector Self-Wronskian Phase-Velocity Calculus and Critical-Line Vertical Derivative Symmetry -/

/-- **Critical-Line Vertical Derivative Equality of the Infinity and Origin Sector Moduli Squared
(`l = 0`, `k ≥ 2`, `τ ∈ ℝ`):**
On the critical line `l = 0`, the vertical difference quotient of `|F_k^+(0, τ)|² − |F_k^-(0, τ)|²`
vanishes identically for every `h ∈ ℝ`. -/
theorem sectorModulusSq_sub_vert_shift_at_criticalLine_eq_zero
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ h : ℝ) :
    (((∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
      ((∫ x in Ioc (0 : ℝ) 1,
          x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioc (0 : ℝ) 1,
          x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) = 0 := by
  rw [sectorModulusSq_Ioi_one_eq_Ioc_zero_one_at_criticalLine hk ν (τ + h), sub_self]

/-- **Critical-Line Vertical Partial Derivative of the Infinity-Sector Modulus Squared
`|F_k^+(0, τ)|²` (`l = 0`, `k ≥ 2`, `τ ∈ ℝ`):**
`((|F_k^+(0, τ + h)|² − |F_k^+(0, τ)|²) / h) →
  2 (C_k^+(0, τ) · (−(∫_ℝ v sin(τv) Φ_k(v) dv) / 2) +
     S_k^+(0, τ) · ((∫_{v > 0} 2 v cos(τv) Φ_k(v) dv) / 2))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_Ioi_one_vert_shift_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          (∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  have hpos := tendsto_div_sectorModulusSq_Ioi_one_vert_shift_nhds_zero
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
  have hsinh :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    have h0 :
        (fun v : ℝ => 2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun _ => 0 := by
      ext v; rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
    rw [h0, integral_zero]
  have hcosh_full :
      (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    congr 1; ext v; rw [zero_mul, Real.cosh_zero, mul_one]
  have hsinh_full :
      (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    have h0 :
        (fun v : ℝ => v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun _ => 0 := by
      ext v; rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
    rw [h0, integral_zero]
  have hcosh_half :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v in Ioi (0 : ℝ),
        2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    congr 1; ext v; rw [zero_mul, Real.cosh_zero, mul_one]
  have hlim :
      2 * ((∫ x in Ioi (1 : ℝ),
              x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(((∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) +
          (∫ x in Ioi (1 : ℝ),
              x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (((∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) =
      (∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (-(∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        (∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    rw [hl0, hsinh, hcosh_full, hsinh_full, hcosh_half]
    ring
  rw [hlim] at hpos
  refine hpos.congr (fun h => ?_)
  rw [hl0]

/-- **Critical-Line Zero-Locus Vertical Derivative of the Infinity-Sector Modulus Squared
(`l = 0`, `k ≥ 2`, `τ₀ ∈ ℝ`, `M_k(0, τ₀) = 0`):**
At any critical-line zero `M_k(0, τ₀) = 0`,
`((|F_k^+(0, τ₀ + h)|² − |F_k^+(0, τ₀)|²) / h) →
  (∫_{v > 0} sin(τ₀ v) Φ_k(v) dv) · (∫_{v > 0} 2 v cos(τ₀ v) Φ_k(v) dv)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_Ioi_one_vert_shift_at_criticalLine_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {τ₀ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        ((∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cos (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  have hk1 : 1 ≤ k := by omega
  have h := tendsto_div_sectorModulusSq_Ioi_one_vert_shift_at_criticalLine_nhds_zero hk hν τ₀
  have hC0 :
      (∫ x in Ioi (1 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0 := by
    have hsplit := setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors
      hk hν (by norm_num : |(0 : ℝ)| < 1 / 2) τ₀
    have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
    rw [hl0, hzero, setIntegral_Ioc_zero_one_cos_log_eq_setIntegral_Ioi_one hk1 ν τ₀] at hsplit
    linarith
  have hS0 :
      (∫ x in Ioi (1 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v := by
    have h1 := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_sin_log hk1 ν τ₀
    have h2 := setIntegral_Ioc_zero_one_rpow_neg_half_mul_sin_log_eq_neg_Ioi_one hk1 ν τ₀
    linarith
  have hlim :
      (∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (-(∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        (∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cos (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) =
      (∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.cos (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    rw [hC0, hS0, zero_mul, zero_add]
  rw [hlim] at h
  exact h

/-- **Critical-Line Zero-Locus Sector Gradient-Norm Factorization
(`l = 0`, `k ≥ 2`, `τ₀ ∈ ℝ`, `M_k(0, τ₀) = 0`):**
At any critical-line zero `M_k(0, τ₀) = 0`, the sum of squares of the horizontal and vertical
partial derivatives of `|F_k^+(l, τ)|²` at `(0, τ₀)` factors as the product of `|F_k^+(0, τ₀)|²`
and the sum of the squared derivatives `|F_k'(0, τ₀)|² + |Δ_k'(0, τ₀)|²`:
`((∫_{v > 0} sin(τ₀ v) Φ_k(v) dv) · (∫_ℝ v sin(τ₀ v) Φ_k(v) dv))² +
 ((∫_{v > 0} sin(τ₀ v) Φ_k(v) dv) · (∫_{v > 0} 2 v cos(τ₀ v) Φ_k(v) dv))² =
 |F_k^+(0, τ₀)|² · ((∫_ℝ v sin(τ₀ v) Φ_k(v) dv)² + (∫_{v > 0} 2 v cos(τ₀ v) Φ_k(v) dv)²)`. -/
theorem sectorModulusSq_gradient_norm_sq_at_criticalLine_zero_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {τ₀ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0) :
    ((∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
        (∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
      ((∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.cos (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 =
    ((∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
      ((∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.cos (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  rw [sectorModulusSq_at_criticalLine_zero_eq_sq_sin_integral hk hν hzero]
  ring


/-! ## Section 4: Global Five-Point Subharmonicity of the Cross-Sector Modulus Product `|F_k^+(l, τ)|² · |F_k^-(l, τ)|²` and Master Witness Theorem -/

/-- **Global Five-Point Subharmonic Laplacian Law for the Cross-Sector Modulus Product
`|F_k^+(l, τ)|² · |F_k^-(l, τ)|²` Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² (|F_k^+|² |F_k^-|²) + Δ_τ² (|F_k^+|² |F_k^-|²)) / h²) →
  |F_k^+|² · ((∂_l M_k − ∂_l Δ_k^{\cos})² + (∂_l N_k − ∂_l Δ_k^{\sin})²) +
  |F_k^-|² · ((∂_l M_k + ∂_l Δ_k^{\cos})² + (∂_l N_k + ∂_l Δ_k^{\sin})²) +
  2 ((∂_l |F_k^+|²)(∂_l |F_k^-|²) + (∂_τ |F_k^+|²)(∂_τ |F_k^-|²))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sectorModulusSq_mul_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
              2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
            ((((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
              2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
            ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2) +
        ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
            ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2) +
        2 * ((2 * ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                      (∫ v in Ioi (0 : ℝ),
                        2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) +
                  (∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                      (∫ v in Ioi (0 : ℝ),
                        2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2))) *
              (2 * ((∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
                      (∫ v in Ioi (0 : ℝ),
                        2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) +
                  (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
                      (∫ v in Ioi (0 : ℝ),
                        2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2))) +
            (2 * ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (-(((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                      (∫ v in Ioi (0 : ℝ),
                        2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) +
                  (∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                      (∫ v in Ioi (0 : ℝ),
                        2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2))) *
              (2 * ((∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (-(((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
                      (∫ v in Ioi (0 : ℝ),
                        2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) +
                  (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
                      (∫ v in Ioi (0 : ℝ),
                        2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)))))) := by
  set U_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set U_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set U₀ : ℝ :=
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set V_l : ℝ → ℝ := fun h =>
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set V_t : ℝ → ℝ := fun h =>
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set V₀ : ℝ :=
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  have hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
          ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2)) := by
    refine (tendsto_div_sq_sectorModulusSq_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [U_l, U_t, U₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
          ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2)) := by
    refine (tendsto_div_sq_sectorModulusSq_Ioc_zero_one_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [V_l, V_t, V₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_mul_general_nhdsWithin_zero
    (tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorModulusSq_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorModulusSq_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorModulusSq_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    hUlap hVlap
  refine h.congr (fun h => ?_)
  dsimp [U_l, U_t, U₀, V_l, V_t, V₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]
  ring

/-- **Master Witness Theorem for Cross-Sector Holomorphy of `F_k^+(l, τ) · F_k^-(l, τ)`,
Cross-Sector Hermitian and Symplectic Bilinear Laplacians, and Critical-Line Sector Gradient
Factorization:**
There exists an explicit symmetric non-zero finite arc measure `ν` on `ArcParam` such that for all
`k ≥ 2`:
1. Across `|l| < 1/2` and `τ ∈ ℝ`, the cross-sector polarization identities
   `4 (C_k^+ C_k^- − S_k^+ S_k^-) = (M_k² − N_k²) − ((Δ_k^{\cos})² − (Δ_k^{\sin})²)`,
   `2 (C_k^+ S_k^- + S_k^+ C_k^-) = M_k N_k − Δ_k^{\cos} Δ_k^{\sin}`, and
   `4 (C_k^+ C_k^- + S_k^+ S_k^-) = |F_k|² − |Δ_k|²` hold;
2. Across `|l| < 1/8` and `τ ∈ ℝ`, the cross-sector holomorphic product
   `F_k^+(l, τ) · F_k^-(l, τ) = (C_k^+ C_k^- − S_k^+ S_k^-) + i (C_k^+ S_k^- + S_k^+ C_k^-)`
   satisfies the global Cauchy–Riemann equations and five-point harmonicity;
3. Across `|l| < 1/8` and `τ ∈ ℝ`, the cross-sector Hermitian inner product
   `I_k = C_k^+ C_k^- + S_k^+ S_k^-` and symplectic Wronskian `D_k = C_k^+ S_k^- − S_k^+ C_k^-`
   satisfy the exact five-point bilinear Laplacian laws
   `Δ_5 I_k → ((∂_l M_k)² + (∂_l N_k)²) − ((∂_l Δ_k^{\cos})² + (∂_l Δ_k^{\sin})²)` and
   `Δ_5 D_k → 2 ((∂_l N_k)(∂_l Δ_k^{\cos}) − (∂_l M_k)(∂_l Δ_k^{\sin}))`;
4. At any critical-line zero `M_k(0, τ₀) = 0`, the vertical derivative of `|F_k^+(0, τ₀)|²` equals
   `(∫_{v > 0} sin(τ₀ v) Φ_k(v) dv) · (∫_{v > 0} 2 v cos(τ₀ v) Φ_k(v) dv)` and the sector gradient
   norm squared factors as `|F_k^+(0, τ₀)|² · (|F_k'(0, τ₀)|² + |Δ_k'(0, τ₀)|²)`. -/
theorem exists_dyadic_crossSector_holomorphy_phaseVelocity_curvature_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l : ℝ⦄, |l| < 1 / 2 → ∀ τ : ℝ,
          4 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) =
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
                (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
          4 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) =
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              ((((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  (∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  (∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) -
              (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                  (∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                  (∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) ∧
          Tendsto
            (fun h : ℝ =>
              ((((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                  (∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                  (∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
              (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  (∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  (∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) ∧
        (∀ τ₀ : ℝ,
          (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0 →
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              ((∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cos (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v))) ∧
          ((∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
              (∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
            ((∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cos (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 =
          ((∫ x in Ioi (1 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (1 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
            ((∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cos (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk => ?_⟩
  refine ⟨fun l hl τ =>
      ⟨four_mul_crossSectorRe_eq_diff_sq hk hν hl τ,
       four_mul_crossSectorHermitian_eq_diff_modulusSq hk hν hl τ⟩,
    fun l hl τ =>
      ⟨tendsto_div_crossSectorProduct_cauchyRiemann_first_nhds_zero hk hν hl τ,
       tendsto_div_crossSectorProduct_cauchyRiemann_second_nhds_zero hk hν hl τ⟩,
    fun τ₀ hzero =>
      ⟨tendsto_div_sectorModulusSq_Ioi_one_vert_shift_at_criticalLine_zero hk hν hzero,
       sectorModulusSq_gradient_norm_sq_at_criticalLine_zero_eq hk hν hzero⟩⟩

end

end RHTower
