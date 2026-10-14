/-
Copyright (c) 2026 Michael. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael
-/
import GaloisForLFunctions.RHTower.ModularArcDyadicOriginInfinitySectorHolomorphy

/-!
# Universal Five-Point Bilinear Product Laplacian, Holomorphic Sector Product, Origin–Infinity Sector Wronskian, and One-Sided Sector Subharmonicity

This file is the thirty-first self-contained module (`Cycle 53`) in the unconditional
dyadic harmonic-analysis tower for the modular arc Poisson kernel (`Route 3'` producer
infrastructure).

Building directly on `ModularArcDyadicOriginInfinitySectorHolomorphy.lean` (`Cycle 52`), which
established the Cauchy–Riemann holomorphy and five-point subharmonicity of the origin–infinity
complex Mellin imbalance `Δ_k(l, τ) = (Δ_k^{\cos}(l, τ), Δ_k^{\sin}(l, τ))` alongside the
parallelogram and polarization laws for the `(1, ∞)` and `(0, 1]` sector moduli squared, we now
develop the **universal five-point bilinear product Laplacian calculus**, the **holomorphic
product `F_k(l, τ) · Δ_k(l, τ) = P_k(l, τ) + i Q_k(l, τ)`**, the **Hermitian/symplectic
origin–infinity sector Wronskian `(H_k(l, τ), W_k(l, τ))`**, and **one-sided `(1, ∞)` / `(0, 1]`
sector holomorphy and subharmonicity**:

1. **Universal Five-Point Bilinear Product Central-Difference Identity & Laplacian Limit Theorem
   (Section 1):**
   For any real numbers `a, b, c, d, e, f, h ∈ ℝ`, we establish the exact algebraic identity
   `(a d + b e − 2 c f) / h² =
     c ((d + e − 2 f) / h²) + f ((a + b − 2 c) / h²) +
       ((a − c) / h) ((d − f) / h) + ((b − c) / (−h)) ((e − f) / (−h))`,
   its two-dimensional five-point Laplacian generalization, the universal punctured-neighborhood
   product rule `(U h · V h − U₀ · V₀) / h → U₀ D_V + V₀ D_U`, and the universal five-point
   bilinear Laplacian limit theorem for products of five-point harmonic functions:
   `((U_l h V_l h + U_l (−h) V_l (−h) − 2 U₀ V₀) +
     (U_t h V_t h + U_t (−h) V_t (−h) − 2 U₀ V₀)) / h² → 2 (D_{U,l} D_{V,l} + D_{U,t} D_{V,t})`.

2. **Harmonicity of `Im(F_k²) = 2 M_k N_k` and `Im(Δ_k²) = 2 Δ_k^{\cos} Δ_k^{\sin}`, and the
   Holomorphic Product `F_k · Δ_k = P_k + i Q_k` (Section 2):**
   - Applying the universal bilinear five-point Laplacian law together with the Cauchy–Riemann
     orthogonality `∇M_k · ∇N_k = 0` and `∇Δ_k^{\cos} · ∇Δ_k^{\sin} = 0`, we prove that both
     `M_k(l, τ) N_k(l, τ)` and `Δ_k^{\cos}(l, τ) Δ_k^{\sin}(l, τ)` (as well as
     `Δ_k^{\cos}(l, τ)² − Δ_k^{\sin}(l, τ)²`) have vanishing five-point Laplacian across
     `|l| < 1/8`, `τ ∈ ℝ`.
   - For the bilinear cross-products `M_k Δ_k^{\cos}`, `N_k Δ_k^{\sin}`, `M_k Δ_k^{\sin}`, and
     `N_k Δ_k^{\cos}`, we compute their exact five-point Laplacian limits and prove that the
     holomorphic product components
     `P_k(l, τ) = M_k(l, τ) Δ_k^{\cos}(l, τ) − N_k(l, τ) Δ_k^{\sin}(l, τ)` and
     `Q_k(l, τ) = M_k(l, τ) Δ_k^{\sin}(l, τ) + N_k(l, τ) Δ_k^{\cos}(l, τ)`
     have vanishing five-point Laplacians (`Δ P_k = 0`, `Δ Q_k = 0`) and obey the exact
     Cauchy–Riemann equations `∂_l P_k = ∂_τ Q_k` and `∂_l Q_k = −∂_τ P_k`.

3. **Exact Five-Point Bilinear Laplacian of the Sector Modulus Imbalance `H_k = |F_k^+|² − |F_k^-|²`
   and Origin–Infinity Sector Wronskian `W_k` (Section 3):**
   - We establish the exact algebraic polarization identities relating `(P_k, Q_k)` and the
     Hermitian/symplectic pairings
     `H_k(l, τ) = M_k Δ_k^{\cos} + N_k Δ_k^{\sin} = |F_k^+(l, τ)|² − |F_k^-(l, τ)|²` and
     `W_k(l, τ) = M_k Δ_k^{\sin} − N_k Δ_k^{\cos} = −2 (C_k^+ S_k^- − C_k^- S_k^+)`,
     including the norm identity `P_k² + Q_k² = H_k² + W_k² = |F_k|² · |Δ_k|²`.
   - We prove the exact five-point Laplacian limit for the sector modulus imbalance
     `(Δ_l² (|F_k^+|² − |F_k^-|²) + Δ_τ² (|F_k^+|² − |F_k^-|²)) / h² →
       4 ((∂_l M_k)(∂_l Δ_k^{\cos}) + (∂_l N_k)(∂_l Δ_k^{\sin}))`
     and for the origin–infinity sector Wronskian `W_k`, as well as the critical-line transversal
     derivative of `P_k(l, τ)`.

4. **One-Sided `(1, ∞)` and `(0, 1]` Sector Holomorphy, Sector Subharmonicity, and Critical-Line
   Sector Modulus Decomposition (Section 4):**
   - We establish the exact Cauchy–Riemann equations and five-point subharmonicity for the
     individual `(1, ∞)` and `(0, 1]` sector Mellin transforms `(C_k^+, S_k^+)` and `(C_k^-, S_k^-)`.
   - On the critical line `l = 0`, we prove the exact identity
     `4 (C_k^+(0, τ)² + S_k^+(0, τ)²) = 4 (C_k^-(0, τ)² + S_k^-(0, τ)²) =
       M_k(0, τ)² + (2 ∫_{v > 0} sin(τv) Φ_k(v) dv)²`,
     and bundle the entire theory into the unconditional master witness theorem
     `exists_dyadic_bilinearProductLaplacian_sectorWronskian_arcWitness`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Section 1: Universal Five-Point Bilinear Product Central-Difference Identity and Laplacian Limit Theorem -/

/-- **Universal 1D bilinear central-difference identity:**
For all `a, b, c, d, e, f, h : ℝ`,
`(a * d + b * e − 2 * c * f) / h² =
  c * ((d + e − 2 * f) / h²) + f * ((a + b − 2 * c) / h²) +
    ((a − c) / h) * ((d − f) / h) + ((b − c) / (−h)) * ((e − f) / (−h))`. -/
theorem central_diff_mul_div_sq_eq (a b c d e f h : ℝ) :
    (a * d + b * e - 2 * c * f) / h ^ 2 =
      c * ((d + e - 2 * f) / h ^ 2) +
        f * ((a + b - 2 * c) / h ^ 2) +
        ((a - c) / h) * ((d - f) / h) +
        ((b - c) / (-h)) * ((e - f) / (-h)) := by
  ring

/-- **Universal 2D five-point bilinear product central-difference identity:**
For all `a₁, b₁, a₂, b₂, c, d₁, e₁, d₂, e₂, f, h : ℝ`,
`((a₁ * d₁ + b₁ * e₁ − 2 * c * f) + (a₂ * d₂ + b₂ * e₂ − 2 * c * f)) / h² =
  c * (((d₁ + e₁ − 2 * f) + (d₂ + e₂ − 2 * f)) / h²) +
    f * (((a₁ + b₁ − 2 * c) + (a₂ + b₂ − 2 * c)) / h²) +
    (((a₁ − c) / h) * ((d₁ − f) / h) + ((b₁ − c) / (−h)) * ((e₁ − f) / (−h))) +
    (((a₂ − c) / h) * ((d₂ − f) / h) + ((b₂ − c) / (−h)) * ((e₂ − f) / (−h)))`. -/
theorem fivePoint_mul_div_sq_eq (a₁ b₁ a₂ b₂ c d₁ e₁ d₂ e₂ f h : ℝ) :
    ((a₁ * d₁ + b₁ * e₁ - 2 * c * f) + (a₂ * d₂ + b₂ * e₂ - 2 * c * f)) / h ^ 2 =
      c * (((d₁ + e₁ - 2 * f) + (d₂ + e₂ - 2 * f)) / h ^ 2) +
        f * (((a₁ + b₁ - 2 * c) + (a₂ + b₂ - 2 * c)) / h ^ 2) +
        (((a₁ - c) / h) * ((d₁ - f) / h) + ((b₁ - c) / (-h)) * ((e₁ - f) / (-h))) +
        (((a₂ - c) / h) * ((d₂ - f) / h) + ((b₂ - c) / (-h)) * ((e₂ - f) / (-h))) := by
  have h1 := central_diff_mul_div_sq_eq a₁ b₁ c d₁ e₁ f h
  have h2 := central_diff_mul_div_sq_eq a₂ b₂ c d₂ e₂ f h
  rw [add_div, h1, h2, add_div, add_div]
  ring

/-- **Universal product rule for punctured-neighborhood difference quotients:**
If `(U h − U₀) / h → D_U` and `(V h − V₀) / h → D_V` as `h → 0` (`h ≠ 0`), then
`(U h * V h − U₀ * V₀) / h → U₀ * D_V + V₀ * D_U`. -/
theorem tendsto_div_mul_sub_nhdsWithin_zero
    {U V : ℝ → ℝ} {U₀ V₀ D_U D_V : ℝ}
    (hU : Tendsto (fun h : ℝ => (U h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_U))
    (hV : Tendsto (fun h : ℝ => (V h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_V)) :
    Tendsto (fun h : ℝ => (U h * V h - U₀ * V₀) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (U₀ * D_V + V₀ * D_U)) := by
  have hU_cont : Tendsto U (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds U₀) :=
    tendsto_of_tendsto_div_nhdsWithin_zero hU
  have hcomb := (hU_cont.mul hV).add ((tendsto_const_nhds (x := V₀)).mul hU)
  refine hcomb.congr (fun h => ?_)
  ring

/-- **Universal 1D bilinear central-difference limit theorem:**
If `(U h − U₀) / h → D_U`, `(V h − V₀) / h → D_V`,
`(U h + U (−h) − 2 U₀) / h² → L_U`, and `(V h + V (−h) − 2 V₀) / h² → L_V`
as `h → 0` (`h ≠ 0`), then
`(U h * V h + U (−h) * V (−h) − 2 * U₀ * V₀) / h² → U₀ * L_V + V₀ * L_U + 2 * D_U * D_V`. -/
theorem tendsto_div_sq_central_diff_mul_nhdsWithin_zero
    {U V : ℝ → ℝ} {U₀ V₀ D_U D_V L_U L_V : ℝ}
    (hU1 : Tendsto (fun h : ℝ => (U h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_U))
    (hV1 : Tendsto (fun h : ℝ => (V h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_V))
    (hU2 : Tendsto (fun h : ℝ => (U h + U (-h) - 2 * U₀) / h ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds L_U))
    (hV2 : Tendsto (fun h : ℝ => (V h + V (-h) - 2 * V₀) / h ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds L_V)) :
    Tendsto
      (fun h : ℝ => (U h * V h + U (-h) * V (-h) - 2 * U₀ * V₀) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (U₀ * L_V + V₀ * L_U + 2 * D_U * D_V)) := by
  have hneg : Tendsto (fun h : ℝ => -h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℝ)}ᶜ) :=
    tendsto_neg_nhdsWithin_zero
  have hU1m : Tendsto (fun h : ℝ => (U (-h) - U₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_U) :=
    hU1.comp hneg
  have hV1m : Tendsto (fun h : ℝ => (V (-h) - V₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_V) :=
    hV1.comp hneg
  have hcomb := (((hV2.const_mul U₀).add (hU2.const_mul V₀)).add (hU1.mul hV1)).add (hU1m.mul hV1m)
  have hlim : U₀ * L_V + V₀ * L_U + D_U * D_V + D_U * D_V =
      U₀ * L_V + V₀ * L_U + 2 * D_U * D_V := by ring
  rw [hlim] at hcomb
  exact hcomb.congr (fun h => (central_diff_mul_div_sq_eq (U h) (U (-h)) U₀ (V h) (V (-h)) V₀ h).symm)

/-- **Universal 2D five-point bilinear product Laplacian limit theorem for five-point harmonic
functions:**
If `(U_l h − U₀) / h → D_Ul`, `(U_t h − U₀) / h → D_Ut`,
`(V_l h − V₀) / h → D_Vl`, `(V_t h − V₀) / h → D_Vt`, and both five-point Laplacians
`((U_l h + U_l (−h) − 2 U₀) + (U_t h + U_t (−h) − 2 U₀)) / h² → 0` and
`((V_l h + V_l (−h) − 2 V₀) + (V_t h + V_t (−h) − 2 V₀)) / h² → 0` as `h → 0` (`h ≠ 0`), then
`((U_l h * V_l h + U_l (−h) * V_l (−h) − 2 * U₀ * V₀) +
  (U_t h * V_t h + U_t (−h) * V_t (−h) − 2 * U₀ * V₀)) / h² →
  2 * (D_Ul * D_Vl + D_Ut * D_Vt)`. -/
theorem tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero
    {U_l U_t V_l V_t : ℝ → ℝ} {U₀ V₀ D_Ul D_Ut D_Vl D_Vt : ℝ}
    (hUl : Tendsto (fun h : ℝ => (U_l h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hUt : Tendsto (fun h : ℝ => (U_t h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ut))
    (hVl : Tendsto (fun h : ℝ => (V_l h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vl))
    (hVt : Tendsto (fun h : ℝ => (V_t h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vt))
    (hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) :
    Tendsto
      (fun h : ℝ =>
        ((U_l h * V_l h + U_l (-h) * V_l (-h) - 2 * U₀ * V₀) +
          (U_t h * V_t h + U_t (-h) * V_t (-h) - 2 * U₀ * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (2 * (D_Ul * D_Vl + D_Ut * D_Vt))) := by
  have hneg : Tendsto (fun h : ℝ => -h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℝ)}ᶜ) :=
    tendsto_neg_nhdsWithin_zero
  have hUlm : Tendsto (fun h : ℝ => (U_l (-h) - U₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul) :=
    hUl.comp hneg
  have hUtm : Tendsto (fun h : ℝ => (U_t (-h) - U₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ut) :=
    hUt.comp hneg
  have hVlm : Tendsto (fun h : ℝ => (V_l (-h) - V₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vl) :=
    hVl.comp hneg
  have hVtm : Tendsto (fun h : ℝ => (V_t (-h) - V₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vt) :=
    hVt.comp hneg
  have hcomb :=
    (((hVlap.const_mul U₀).add (hUlap.const_mul V₀)).add
      ((hUl.mul hVl).add (hUlm.mul hVlm))).add
      ((hUt.mul hVt).add (hUtm.mul hVtm))
  have hlim :
      U₀ * 0 + V₀ * 0 + (D_Ul * D_Vl + D_Ul * D_Vl) + (D_Ut * D_Vt + D_Ut * D_Vt) =
        2 * (D_Ul * D_Vl + D_Ut * D_Vt) := by
    ring
  rw [hlim] at hcomb
  exact hcomb.congr (fun h =>
    (fivePoint_mul_div_sq_eq
      (U_l h) (U_l (-h)) (U_t h) (U_t (-h)) U₀
      (V_l h) (V_l (-h)) (V_t h) (V_t (-h)) V₀ h).symm)


/-! ## Section 2: Harmonicity of `Im(F_k²) = 2 M_k N_k` and `Im(Δ_k²) = 2 Δ_k^{\cos} Δ_k^{\sin}`, and the Holomorphic Product `F_k · Δ_k = P_k + i Q_k` -/

/-- **Global five-point harmonicity of the cross-product `M_k(l, τ) · N_k(l, τ) = (1/2) Im(F_k(l, τ)²)`
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((M_k(l + h, τ) N_k(l + h, τ) + M_k(l − h, τ) N_k(l − h, τ) − 2 M_k(l, τ) N_k(l, τ)) +
  (M_k(l, τ + h) N_k(l, τ + h) + M_k(l, τ − h) N_k(l, τ − h) − 2 M_k(l, τ) N_k(l, τ))) / h² → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_mul_sineMellin_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
          ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  set M_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set M_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set M₀ : ℝ :=
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set N_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set N_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set N₀ : ℝ :=
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  have hMlap : Tendsto
      (fun h : ℝ => ((M_l h + M_l (-h) - 2 * M₀) + (M_t h + M_t (-h) - 2 * M₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_oscillatoryMellin_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [M_l, M_t, M₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hNlap : Tendsto
      (fun h : ℝ => ((N_l h + N_l (-h) - 2 * N₀) + (N_t h + N_t (-h) - 2 * N₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sineMellin_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [N_l, N_t, N₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)
    hMlap hNlap
  have hlim :
      2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) *
          (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) = 0 := by
    ring
  rw [hlim] at h
  refine h.congr (fun h => ?_)
  dsimp [M_l, M_t, M₀, N_l, N_t, N₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Global five-point harmonicity of `Re(Δ_k(l, τ)²) = Δ_k^{\cos}(l, τ)² − Δ_k^{\sin}(l, τ)²`
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² (Δ_k^{\cos})² + Δ_τ² (Δ_k^{\cos})²) − (Δ_l² (Δ_k^{\sin})² + Δ_τ² (Δ_k^{\sin})²)) / h² → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_imbalanceCos_sq_sub_imbalanceSin_sq_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
            ((((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h1 := tendsto_div_sq_imbalanceCos_sq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have h2 := tendsto_div_sq_imbalanceSin_sq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hsub := h1.sub h2
  rw [sub_self] at hsub
  exact hsub.congr (fun h => by ring)

/-- **Global five-point harmonicity of the cross-product `Δ_k^{\cos}(l, τ) · Δ_k^{\sin}(l, τ) = (1/2) Im(Δ_k(l, τ)²)`
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_k^{\cos}(l + h, τ) Δ_k^{\sin}(l + h, τ) + Δ_k^{\cos}(l − h, τ) Δ_k^{\sin}(l − h, τ) − 2 Δ_k^{\cos}(l, τ) Δ_k^{\sin}(l, τ)) +
  (Δ_k^{\cos}(l, τ + h) Δ_k^{\sin}(l, τ + h) + Δ_k^{\cos}(l, τ − h) Δ_k^{\sin}(l, τ − h) − 2 Δ_k^{\cos}(l, τ) Δ_k^{\sin}(l, τ))) / h² → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_imbalanceCos_mul_imbalanceSin_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
          (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  set U_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U₀ : ℝ :=
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V₀ : ℝ :=
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  have hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_imbalanceCos_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [U_l, U_t, U₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_imbalanceSin_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [V_l, V_t, V₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)
    hUlap hVlap
  have hlim :
      2 * ((∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (-(∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) = 0 := by
    ring
  rw [hlim] at h
  refine h.congr (fun h => ?_)
  dsimp [U_l, U_t, U₀, V_l, V_t, V₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Universal Cauchy–Riemann closure under complex multiplication (first equation
`∂_l (U X − V Y) = ∂_τ (U Y + V X)`):**
If `(U, V)` and `(X, Y)` satisfy the punctured-neighborhood directional derivative limits with
`D_Ut = −D_Vl`, `D_Vt = D_Ul`, `D_Xt = −D_Yl`, and `D_Yt = D_Xl`, then
`(((U_l h * X_l h − V_l h * Y_l h) − (U₀ * X₀ − V₀ * Y₀)) −
  ((U_t h * Y_t h + V_t h * X_t h) − (U₀ * Y₀ + V₀ * X₀))) / h → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_complexMul_cauchyRiemann_first_nhdsWithin_zero
    {U_l U_t V_l V_t X_l X_t Y_l Y_t : ℝ → ℝ}
    {U₀ V₀ X₀ Y₀ D_Ul D_Vl D_Xl D_Yl : ℝ}
    (hUl : Tendsto (fun h : ℝ => (U_l h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hUt : Tendsto (fun h : ℝ => (U_t h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Vl)))
    (hVl : Tendsto (fun h : ℝ => (V_l h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vl))
    (hVt : Tendsto (fun h : ℝ => (V_t h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hXl : Tendsto (fun h : ℝ => (X_l h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl))
    (hXt : Tendsto (fun h : ℝ => (X_t h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Yl)))
    (hYl : Tendsto (fun h : ℝ => (Y_l h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Yl))
    (hYt : Tendsto (fun h : ℝ => (Y_t h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl)) :
    Tendsto
      (fun h : ℝ =>
        (((U_l h * X_l h - V_l h * Y_l h) - (U₀ * X₀ - V₀ * Y₀)) -
          ((U_t h * Y_t h + V_t h * X_t h) - (U₀ * Y₀ + V₀ * X₀))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h1 := (tendsto_div_mul_sub_nhdsWithin_zero hUl hXl).sub
    (tendsto_div_mul_sub_nhdsWithin_zero hVl hYl)
  have h2 := (tendsto_div_mul_sub_nhdsWithin_zero hUt hYt).add
    (tendsto_div_mul_sub_nhdsWithin_zero hVt hXt)
  have hsub := h1.sub h2
  have hlim :
      ((U₀ * D_Xl + X₀ * D_Ul) - (V₀ * D_Yl + Y₀ * D_Vl)) -
        ((U₀ * D_Xl + Y₀ * (-D_Vl)) + (V₀ * (-D_Yl) + X₀ * D_Ul)) = 0 := by
    ring
  rw [hlim] at hsub
  exact hsub.congr (fun h => by ring)

/-- **Universal Cauchy–Riemann closure under complex multiplication (second equation
`∂_l (U Y + V X) = −∂_τ (U X − V Y)`):**
If `(U, V)` and `(X, Y)` satisfy the punctured-neighborhood directional derivative limits with
`D_Ut = −D_Vl`, `D_Vt = D_Ul`, `D_Xt = −D_Yl`, and `D_Yt = D_Xl`, then
`(((U_l h * Y_l h + V_l h * X_l h) − (U₀ * Y₀ + V₀ * X₀)) +
  ((U_t h * X_t h − V_t h * Y_t h) − (U₀ * X₀ − V₀ * Y₀))) / h → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_complexMul_cauchyRiemann_second_nhdsWithin_zero
    {U_l U_t V_l V_t X_l X_t Y_l Y_t : ℝ → ℝ}
    {U₀ V₀ X₀ Y₀ D_Ul D_Vl D_Xl D_Yl : ℝ}
    (hUl : Tendsto (fun h : ℝ => (U_l h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hUt : Tendsto (fun h : ℝ => (U_t h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Vl)))
    (hVl : Tendsto (fun h : ℝ => (V_l h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vl))
    (hVt : Tendsto (fun h : ℝ => (V_t h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hXl : Tendsto (fun h : ℝ => (X_l h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl))
    (hXt : Tendsto (fun h : ℝ => (X_t h - X₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_Yl)))
    (hYl : Tendsto (fun h : ℝ => (Y_l h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Yl))
    (hYt : Tendsto (fun h : ℝ => (Y_t h - Y₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Xl)) :
    Tendsto
      (fun h : ℝ =>
        (((U_l h * Y_l h + V_l h * X_l h) - (U₀ * Y₀ + V₀ * X₀)) +
          ((U_t h * X_t h - V_t h * Y_t h) - (U₀ * X₀ - V₀ * Y₀))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h1 := (tendsto_div_mul_sub_nhdsWithin_zero hUl hYl).add
    (tendsto_div_mul_sub_nhdsWithin_zero hVl hXl)
  have h2 := (tendsto_div_mul_sub_nhdsWithin_zero hUt hXt).sub
    (tendsto_div_mul_sub_nhdsWithin_zero hVt hYt)
  have hadd := h1.add h2
  have hlim :
      ((U₀ * D_Yl + Y₀ * D_Ul) + (V₀ * D_Xl + X₀ * D_Vl)) +
        ((U₀ * (-D_Yl) + X₀ * (-D_Vl)) - (V₀ * D_Xl + Y₀ * D_Ul)) = 0 := by
    ring
  rw [hlim] at hadd
  exact hadd.congr (fun h => by ring)

/-- **Exact five-point Laplacian limit of `M_k(l, τ) · Δ_k^{\cos}(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((M_k(l + h, τ) Δ_k^{\cos}(l + h, τ) + M_k(l − h, τ) Δ_k^{\cos}(l − h, τ) − 2 M_k(l, τ) Δ_k^{\cos}(l, τ)) +
  (M_k(l, τ + h) Δ_k^{\cos}(l, τ + h) + M_k(l, τ − h) Δ_k^{\cos}(l, τ − h) − 2 M_k(l, τ) Δ_k^{\cos}(l, τ))) / h² →
  2 ((∂_l M_k)(∂_l Δ_k^{\cos}) + (∂_l N_k)(∂_l Δ_k^{\sin}))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_mul_imbalanceCos_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
          ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  set M_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set M_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set M₀ : ℝ :=
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U₀ : ℝ :=
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  have hMlap : Tendsto
      (fun h : ℝ => ((M_l h + M_l (-h) - 2 * M₀) + (M_t h + M_t (-h) - 2 * M₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_oscillatoryMellin_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [M_l, M_t, M₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_imbalanceCos_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [U_l, U_t, U₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
    hMlap hUlap
  have hlim :
      2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) *
          (-(∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) =
      2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    ring
  rw [hlim] at h
  refine h.congr (fun h => ?_)
  dsimp [M_l, M_t, M₀, U_l, U_t, U₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Exact five-point Laplacian limit of `N_k(l, τ) · Δ_k^{\sin}(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((N_k(l + h, τ) Δ_k^{\sin}(l + h, τ) + N_k(l − h, τ) Δ_k^{\sin}(l − h, τ) − 2 N_k(l, τ) Δ_k^{\sin}(l, τ)) +
  (N_k(l, τ + h) Δ_k^{\sin}(l, τ + h) + N_k(l, τ − h) Δ_k^{\sin}(l, τ − h) − 2 N_k(l, τ) Δ_k^{\sin}(l, τ))) / h² →
  2 ((∂_l M_k)(∂_l Δ_k^{\cos}) + (∂_l N_k)(∂_l Δ_k^{\sin}))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sineMellin_mul_imbalanceSin_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
          ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  set N_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set N_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set N₀ : ℝ :=
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V₀ : ℝ :=
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  have hNlap : Tendsto
      (fun h : ℝ => ((N_l h + N_l (-h) - 2 * N₀) + (N_t h + N_t (-h) - 2 * N₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sineMellin_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [N_l, N_t, N₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_imbalanceSin_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [V_l, V_t, V₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)
    hNlap hVlap
  have hlim :
      2 * ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) =
      2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    ring
  rw [hlim] at h
  refine h.congr (fun h => ?_)
  dsimp [N_l, N_t, N₀, V_l, V_t, V₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Exact five-point Laplacian limit of `M_k(l, τ) · Δ_k^{\sin}(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((M_k(l + h, τ) Δ_k^{\sin}(l + h, τ) + M_k(l − h, τ) Δ_k^{\sin}(l − h, τ) − 2 M_k(l, τ) Δ_k^{\sin}(l, τ)) +
  (M_k(l, τ + h) Δ_k^{\sin}(l, τ + h) + M_k(l, τ − h) Δ_k^{\sin}(l, τ − h) − 2 M_k(l, τ) Δ_k^{\sin}(l, τ))) / h² →
  2 ((∂_l M_k)(∂_l Δ_k^{\sin}) − (∂_l N_k)(∂_l Δ_k^{\cos}))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_mul_imbalanceSin_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
          ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  set M_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set M_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set M₀ : ℝ :=
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set V₀ : ℝ :=
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  have hMlap : Tendsto
      (fun h : ℝ => ((M_l h + M_l (-h) - 2 * M₀) + (M_t h + M_t (-h) - 2 * M₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_oscillatoryMellin_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [M_l, M_t, M₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_imbalanceSin_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [V_l, V_t, V₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)
    hMlap hVlap
  have hlim :
      2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) =
      2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
        (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    ring
  rw [hlim] at h
  refine h.congr (fun h => ?_)
  dsimp [M_l, M_t, M₀, V_l, V_t, V₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Exact five-point Laplacian limit of `N_k(l, τ) · Δ_k^{\cos}(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((N_k(l + h, τ) Δ_k^{\cos}(l + h, τ) + N_k(l − h, τ) Δ_k^{\cos}(l − h, τ) − 2 N_k(l, τ) Δ_k^{\cos}(l, τ)) +
  (N_k(l, τ + h) Δ_k^{\cos}(l, τ + h) + N_k(l, τ − h) Δ_k^{\cos}(l, τ − h) − 2 N_k(l, τ) Δ_k^{\cos}(l, τ))) / h² →
  −2 ((∂_l M_k)(∂_l Δ_k^{\sin}) − (∂_l N_k)(∂_l Δ_k^{\cos}))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sineMellin_mul_imbalanceCos_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
          ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-(2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))))) := by
  set N_l : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set N_t : ℝ → ℝ := fun h =>
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set N₀ : ℝ :=
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set U₀ : ℝ :=
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  have hNlap : Tendsto
      (fun h : ℝ => ((N_l h + N_l (-h) - 2 * N₀) + (N_t h + N_t (-h) - 2 * N₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_sineMellin_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [N_l, N_t, N₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_imbalanceCos_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [U_l, U_t, U₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_mul_harmonic_nhdsWithin_zero
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
    hNlap hUlap
  have hlim :
      2 * ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (-(∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) =
      -(2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
        (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
    ring
  rw [hlim] at h
  refine h.congr (fun h => ?_)
  dsimp [N_l, N_t, N₀, U_l, U_t, U₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Global five-point harmonicity of the real part `P_k(l, τ) = M_k Δ_k^{\cos} − N_k Δ_k^{\sin}`
of the holomorphic product `F_k(l, τ) · Δ_k(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² (M_k Δ_k^{\cos}) + Δ_τ² (M_k Δ_k^{\cos})) − (Δ_l² (N_k Δ_k^{\sin}) + Δ_τ² (N_k Δ_k^{\sin}))) / h² → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_holomorphicProductRe_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
          (((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h1 := tendsto_div_sq_oscillatoryMellin_mul_imbalanceCos_fivePoint_laplacian_nhds_zero hk hν hl τ
  have h2 := tendsto_div_sq_sineMellin_mul_imbalanceSin_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hsub := h1.sub h2
  rw [sub_self] at hsub
  exact hsub.congr (fun h => by ring)

/-- **Global five-point harmonicity of the imaginary part `Q_k(l, τ) = M_k Δ_k^{\sin} + N_k Δ_k^{\cos}`
of the holomorphic product `F_k(l, τ) · Δ_k(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² (M_k Δ_k^{\sin}) + Δ_τ² (M_k Δ_k^{\sin})) + (Δ_l² (N_k Δ_k^{\cos}) + Δ_τ² (N_k Δ_k^{\cos}))) / h² → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_holomorphicProductIm_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
          (((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h1 := tendsto_div_sq_oscillatoryMellin_mul_imbalanceSin_fivePoint_laplacian_nhds_zero hk hν hl τ
  have h2 := tendsto_div_sq_sineMellin_mul_imbalanceCos_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hadd := h1.add h2
  rw [add_neg_cancel] at hadd
  exact hadd.congr (fun h => by ring)

/-- **First Cauchy–Riemann Equation `∂_l P_k(l, τ) = ∂_τ Q_k(l, τ)` for the holomorphic product
`(P_k, Q_k) = (M_k Δ_k^{\cos} − N_k Δ_k^{\sin}, M_k Δ_k^{\sin} + N_k Δ_k^{\cos})` across
`|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((P_k(l + h, τ) − P_k(l, τ)) − (Q_k(l, τ + h) − Q_k(l, τ))) / h → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_holomorphicProduct_cauchyRiemann_first_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) -
          (((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_div_complexMul_cauchyRiemann_first_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)

/-- **Second Cauchy–Riemann Equation `∂_l Q_k(l, τ) = −∂_τ P_k(l, τ)` for the holomorphic product
`(P_k, Q_k) = (M_k Δ_k^{\cos} − N_k Δ_k^{\sin}, M_k Δ_k^{\sin} + N_k Δ_k^{\cos})` across
`|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Q_k(l + h, τ) − Q_k(l, τ)) + (P_k(l, τ + h) − P_k(l, τ))) / h → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_holomorphicProduct_cauchyRiemann_second_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
          (((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_div_complexMul_cauchyRiemann_second_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)


/-! ## Section 3: Exact Five-Point Bilinear Laplacian of the Sector Modulus Imbalance `H_k = |F_k^+|² − |F_k^-|²` and Origin–Infinity Sector Wronskian `W_k` -/

/-- **Universal sector Wronskian polarization identity:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`(c_pos + c_neg) * (s_pos − s_neg) − (s_pos + s_neg) * (c_pos − c_neg) =
  −2 * (c_pos * s_neg − c_neg * s_pos)`. -/
theorem sector_wronskian_polarization_identity (c_pos s_pos c_neg s_neg : ℝ) :
    (c_pos + c_neg) * (s_pos - s_neg) - (s_pos + s_neg) * (c_pos - c_neg) =
      -2 * (c_pos * s_neg - c_neg * s_pos) := by
  ring

/-- **Universal holomorphic-product real-part sector identity:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`(c_pos + c_neg) * (c_pos − c_neg) − (s_pos + s_neg) * (s_pos − s_neg) =
  (c_pos ^ 2 − s_pos ^ 2) − (c_neg ^ 2 − s_neg ^ 2)`. -/
theorem holomorphic_product_re_sector_identity (c_pos s_pos c_neg s_neg : ℝ) :
    (c_pos + c_neg) * (c_pos - c_neg) - (s_pos + s_neg) * (s_pos - s_neg) =
      (c_pos ^ 2 - s_pos ^ 2) - (c_neg ^ 2 - s_neg ^ 2) := by
  ring

/-- **Universal holomorphic-product imaginary-part sector identity:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`(c_pos + c_neg) * (s_pos − s_neg) + (s_pos + s_neg) * (c_pos − c_neg) =
  2 * (c_pos * s_pos − c_neg * s_neg)`. -/
theorem holomorphic_product_im_sector_identity (c_pos s_pos c_neg s_neg : ℝ) :
    (c_pos + c_neg) * (s_pos - s_neg) + (s_pos + s_neg) * (c_pos - c_neg) =
      2 * (c_pos * s_pos - c_neg * s_neg) := by
  ring

/-- **Universal norm equality between the holomorphic product `(M Δc − N Δs, M Δs + N Δc)` and
the Hermitian/Wronskian pairing `(M Δc + N Δs, M Δs − N Δc)`:**
For all `M, N, Δc, Δs : ℝ`,
`(M * Δc − N * Δs)² + (M * Δs + N * Δc)² = (M * Δc + N * Δs)² + (M * Δs − N * Δc)²`
and both equal `(M² + N²) * (Δc² + Δs²)`. -/
theorem holomorphic_product_modulus_sq_eq_hermitian_wronskian_sq (M N Δc Δs : ℝ) :
    (M * Δc - N * Δs) ^ 2 + (M * Δs + N * Δc) ^ 2 =
      (M * Δc + N * Δs) ^ 2 + (M * Δs - N * Δc) ^ 2 ∧
    (M * Δc - N * Δs) ^ 2 + (M * Δs + N * Δc) ^ 2 =
      (M ^ 2 + N ^ 2) * (Δc ^ 2 + Δs ^ 2) := by
  constructor <;> ring

/-- **Origin–Infinity Sector Wronskian Determinant Identity (`k ≥ 2`, `|l| < 1/2`, `τ ∈ ℝ`):**
`M_k(l, τ) Δ_k^{\sin}(l, τ) − N_k(l, τ) Δ_k^{\cos}(l, τ) =
  −2 (C_k^+(l, τ) S_k^-(l, τ) − C_k^-(l, τ) S_k^+(l, τ))`. -/
theorem sectorWronskian_eq_neg_two_mul_sector_det
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
    -2 * ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        (∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        (∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl τ,
    setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl τ]
  exact sector_wronskian_polarization_identity _ _ _ _

/-- **Holomorphic-Product Real-Part Sector Identity (`k ≥ 2`, `|l| < 1/2`, `τ ∈ ℝ`):**
`M_k(l, τ) Δ_k^{\cos}(l, τ) − N_k(l, τ) Δ_k^{\sin}(l, τ) =
  (C_k^+(l, τ)² − S_k^+(l, τ)²) − (C_k^-(l, τ)² − S_k^-(l, τ)²)`. -/
theorem holomorphicProductRe_eq_sector_diff
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
    ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
        (∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
      ((∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
        (∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl τ,
    setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl τ]
  exact holomorphic_product_re_sector_identity _ _ _ _

/-- **Exact Five-Point Bilinear Laplacian Law for the Hermitian Pairing
`H_k(l, τ) = M_k(l, τ) Δ_k^{\cos}(l, τ) + N_k(l, τ) Δ_k^{\sin}(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² H_k + Δ_τ² H_k) / h²) → 4 ((∂_l M_k)(∂_l Δ_k^{\cos}) + (∂_l N_k)(∂_l Δ_k^{\sin}))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_hermitianPairing_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
          (((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  have h1 := tendsto_div_sq_oscillatoryMellin_mul_imbalanceCos_fivePoint_laplacian_nhds_zero hk hν hl τ
  have h2 := tendsto_div_sq_sineMellin_mul_imbalanceSin_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hadd := h1.add h2
  have hlim :
      2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
      2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) =
      4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    ring
  rw [hlim] at hadd
  exact hadd.congr (fun h => by ring)

/-- **Exact Five-Point Bilinear Laplacian Law for the Origin–Infinity Sector Modulus Imbalance
`|F_k^+(l, τ)|² − |F_k^-(l, τ)|²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² (|F_k^+|² − |F_k^-|²) + Δ_τ² (|F_k^+|² − |F_k^-|²)) / h²) →
  4 ((∂_l M_k)(∂_l Δ_k^{\cos}) + (∂_l N_k)(∂_l Δ_k^{\sin}))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sectorModulusSq_sub_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
              2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
            ((((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
              2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  refine (tendsto_div_sq_hermitianPairing_fivePoint_laplacian_nhds_zero hk hν hl τ).congr' ?_
  have hmem : Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem] with h hh_mem
  have hh_eighth : |h| < 1 / 8 := abs_lt.mpr hh_mem
  have hl_half : |l| < 1 / 2 := by linarith
  have hlh_pos : |l + h| < 1 / 2 := by
    have := abs_add_le l h
    linarith
  have hlh_neg : |l - h| < 1 / 2 := by
    have := abs_sub l h
    linarith
  rw [sectorModulusSq_sub_eq_oscillatoryMellin_mul_imbalance hk hν hlh_pos τ,
    sectorModulusSq_sub_eq_oscillatoryMellin_mul_imbalance hk hν hlh_neg τ,
    sectorModulusSq_sub_eq_oscillatoryMellin_mul_imbalance hk hν hl_half τ,
    sectorModulusSq_sub_eq_oscillatoryMellin_mul_imbalance hk hν hl_half (τ + h),
    sectorModulusSq_sub_eq_oscillatoryMellin_mul_imbalance hk hν hl_half (τ - h)]

/-- **Exact Five-Point Bilinear Laplacian Law for the Origin–Infinity Sector Wronskian
`W_k(l, τ) = M_k(l, τ) Δ_k^{\sin}(l, τ) − N_k(l, τ) Δ_k^{\cos}(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² W_k + Δ_τ² W_k) / h²) → 4 ((∂_l M_k)(∂_l Δ_k^{\sin}) − (∂_l N_k)(∂_l Δ_k^{\cos}))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sectorWronskian_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
          (((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  have h1 := tendsto_div_sq_oscillatoryMellin_mul_imbalanceSin_fivePoint_laplacian_nhds_zero hk hν hl τ
  have h2 := tendsto_div_sq_sineMellin_mul_imbalanceCos_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hsub := h1.sub h2
  have hlim :
      2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
        (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
      (-(2 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
        (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) =
      4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
        (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    ring
  rw [hlim] at hsub
  exact hsub.congr (fun h => by ring)

/-- **Exact first-order horizontal transversal derivative of the holomorphic product real part
`P_k(l, τ) = M_k(l, τ) Δ_k^{\cos}(l, τ) − N_k(l, τ) Δ_k^{\sin}(l, τ)` on the critical line `l = 0` (`k ≥ 2`, `τ ∈ ℝ`):**
`P_k(l, τ) / l →
  M_k(0, τ) · (2 ∫_{v > 0} v cos(τv) Φ_k(v) dv) −
  (∫_ℝ v sin(τv) Φ_k(v) dv) · (2 ∫_{v > 0} sin(τv) Φ_k(v) dv)`
as `l → 0` (`l ≠ 0`). -/
theorem tendsto_div_holomorphicProductRe_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun l : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / l)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        ((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (2 * ∫ v in Ioi (0 : ℝ),
            v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (2 * ∫ v in Ioi (0 : ℝ),
            Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  have hk1 : 1 ≤ k := by omega
  have hM_cont :
      Tendsto
        (fun l : ℝ =>
          ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds
          (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) :=
    tendsto_of_tendsto_div_nhdsWithin_zero
      ((tendsto_div_oscillatoryMellin_sub_criticalLine_nhds_zero hk hν τ).mono_left
        nhdsWithin_le_nhds)
  have hΔc_div := tendsto_div_oscillatoryMellin_imbalance_nhds_zero hk hν τ
  have hN_div := tendsto_div_sineMellin_nhds_zero hk hν τ
  have hΔs_div :
      Tendsto
        (fun l : ℝ =>
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (2 * ∫ v in Ioi (0 : ℝ), Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / l)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds 0) := by
    have h0 := tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
    have hlim0 :
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
      simp [Real.sinh_zero]
    rw [hlim0] at h0
    refine h0.congr (fun l => ?_)
    rw [zero_add, setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_sin_log hk1 ν τ]
  have hΔs_cont := tendsto_of_tendsto_div_nhdsWithin_zero hΔs_div
  have hcomb := (hM_cont.mul hΔc_div).sub (hN_div.mul hΔs_cont)
  exact hcomb.congr (fun l => by ring)


/-! ## Section 4: One-Sided `(1, ∞)` and `(0, 1]` Sector Subharmonicity and Critical-Line Sector Modulus Decomposition -/

/-- **Universal infinity-sector modulus decomposition from parallelogram + polarization:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`4 * (c_pos ^ 2 + s_pos ^ 2) =
  ((c_pos + c_neg) ^ 2 + (s_pos + s_neg) ^ 2) +
    ((c_pos − c_neg) ^ 2 + (s_pos − s_neg) ^ 2) +
    2 * ((c_pos ^ 2 + s_pos ^ 2) − (c_neg ^ 2 + s_neg ^ 2))`. -/
theorem four_mul_sector_pos_modulus_sq_eq (c_pos s_pos c_neg s_neg : ℝ) :
    4 * (c_pos ^ 2 + s_pos ^ 2) =
      ((c_pos + c_neg) ^ 2 + (s_pos + s_neg) ^ 2) +
        ((c_pos - c_neg) ^ 2 + (s_pos - s_neg) ^ 2) +
        2 * ((c_pos ^ 2 + s_pos ^ 2) - (c_neg ^ 2 + s_neg ^ 2)) := by
  ring

/-- **Universal origin-sector modulus decomposition from parallelogram − polarization:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`4 * (c_neg ^ 2 + s_neg ^ 2) =
  ((c_pos + c_neg) ^ 2 + (s_pos + s_neg) ^ 2) +
    ((c_pos − c_neg) ^ 2 + (s_pos − s_neg) ^ 2) −
    2 * ((c_pos ^ 2 + s_pos ^ 2) − (c_neg ^ 2 + s_neg ^ 2))`. -/
theorem four_mul_sector_neg_modulus_sq_eq (c_pos s_pos c_neg s_neg : ℝ) :
    4 * (c_neg ^ 2 + s_neg ^ 2) =
      ((c_pos + c_neg) ^ 2 + (s_pos + s_neg) ^ 2) +
        ((c_pos - c_neg) ^ 2 + (s_pos - s_neg) ^ 2) -
        2 * ((c_pos ^ 2 + s_pos ^ 2) - (c_neg ^ 2 + s_neg ^ 2)) := by
  ring

/-- **Critical-Line Sector Modulus Decomposition (`l = 0`, `k ≥ 2`, `τ ∈ ℝ`):**
On the critical line `l = 0`, four times the `(1, ∞)` sector modulus squared (and four times the
`(0, 1]` sector modulus squared) equals the sum of the squared full-line cosine Mellin transform
`M_k(0, τ)²` and the squared origin–infinity sine imbalance `Δ_k^{\sin}(0, τ)²`:
`4 (C_k^+(0, τ)² + S_k^+(0, τ)²) = M_k(0, τ)² + (2 ∫_{v > 0} sin(τv) Φ_k(v) dv)²`. -/
theorem four_mul_sectorModulusSq_Ioi_one_at_criticalLine_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    4 * ((∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) =
      (∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (2 * ∫ v in Ioi (0 : ℝ),
          Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hpara := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 2) τ
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  have hΔs0 := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_sin_log hk1 ν τ
  rw [hl0] at hpara hΔs0
  rw [setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk1 ν τ,
    setIntegral_Ioc_zero_one_cos_log_eq_setIntegral_Ioi_one hk1 ν τ,
    sub_self, hΔs0,
    setIntegral_Ioc_zero_one_rpow_neg_half_mul_sin_log_eq_neg_Ioi_one hk1 ν τ,
    neg_sq] at hpara
  linarith

/-- **Critical-Line Zero Sector Modulus Formula (`l = 0`, `k ≥ 2`, `τ₀ ∈ ℝ`):**
At any critical-line zero `M_k(0, τ₀) = 0`, both one-sided sector moduli squared equal the squared
half-line sine integral:
`C_k^+(0, τ₀)² + S_k^+(0, τ₀)² = C_k^-(0, τ₀)² + S_k^-(0, τ₀)² =
  (∫_{v > 0} sin(τ₀ v) Φ_k(v) dv)²`. -/
theorem sectorModulusSq_at_criticalLine_zero_eq_sq_sin_integral
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {τ₀ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (1 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 =
    (∫ v in Ioi (0 : ℝ),
      Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have h := four_mul_sectorModulusSq_Ioi_one_at_criticalLine_eq hk hν τ₀
  rw [hzero] at h
  linarith

private theorem fivePoint_sector_pos_div_sq_eq
    {F₁ F₂ F₀ F₃ F₄ Δ₁ Δ₂ Δ₀ Δ₃ Δ₄ P₁ P₂ P₀ P₃ P₄ N₁ N₂ N₀ N₃ N₄ h : ℝ}
    (hp1 : F₁ + Δ₁ = 2 * (P₁ + N₁))
    (hp2 : F₂ + Δ₂ = 2 * (P₂ + N₂))
    (hp0 : F₀ + Δ₀ = 2 * (P₀ + N₀))
    (hp3 : F₃ + Δ₃ = 2 * (P₃ + N₃))
    (hp4 : F₄ + Δ₄ = 2 * (P₄ + N₄)) :
    (1 / 4 : ℝ) *
      ((((F₁ + F₂ - 2 * F₀) + (F₃ + F₄ - 2 * F₀)) / h ^ 2 +
        ((Δ₁ + Δ₂ - 2 * Δ₀) + (Δ₃ + Δ₄ - 2 * Δ₀)) / h ^ 2) +
       2 * ((((P₁ - N₁) + (P₂ - N₂) - 2 * (P₀ - N₀)) +
             ((P₃ - N₃) + (P₄ - N₄) - 2 * (P₀ - N₀))) / h ^ 2)) =
    ((P₁ + P₂ - 2 * P₀) + (P₃ + P₄ - 2 * P₀)) / h ^ 2 := by
  have hnum :
      ((F₁ + F₂ - 2 * F₀) + (F₃ + F₄ - 2 * F₀)) +
      ((Δ₁ + Δ₂ - 2 * Δ₀) + (Δ₃ + Δ₄ - 2 * Δ₀)) +
      2 * (((P₁ - N₁) + (P₂ - N₂) - 2 * (P₀ - N₀)) +
           ((P₃ - N₃) + (P₄ - N₄) - 2 * (P₀ - N₀))) =
      4 * ((P₁ + P₂ - 2 * P₀) + (P₃ + P₄ - 2 * P₀)) := by
    linarith
  calc (1 / 4 : ℝ) *
        ((((F₁ + F₂ - 2 * F₀) + (F₃ + F₄ - 2 * F₀)) / h ^ 2 +
          ((Δ₁ + Δ₂ - 2 * Δ₀) + (Δ₃ + Δ₄ - 2 * Δ₀)) / h ^ 2) +
         2 * ((((P₁ - N₁) + (P₂ - N₂) - 2 * (P₀ - N₀)) +
               ((P₃ - N₃) + (P₄ - N₄) - 2 * (P₀ - N₀))) / h ^ 2))
      = (1 / 4 : ℝ) *
        ((((F₁ + F₂ - 2 * F₀) + (F₃ + F₄ - 2 * F₀)) +
          ((Δ₁ + Δ₂ - 2 * Δ₀) + (Δ₃ + Δ₄ - 2 * Δ₀)) +
          2 * (((P₁ - N₁) + (P₂ - N₂) - 2 * (P₀ - N₀)) +
               ((P₃ - N₃) + (P₄ - N₄) - 2 * (P₀ - N₀)))) / h ^ 2) := by ring
    _ = (1 / 4 : ℝ) * ((4 * ((P₁ + P₂ - 2 * P₀) + (P₃ + P₄ - 2 * P₀))) / h ^ 2) := by
        rw [hnum]
    _ = ((P₁ + P₂ - 2 * P₀) + (P₃ + P₄ - 2 * P₀)) / h ^ 2 := by ring

private theorem fivePoint_sector_neg_div_sq_eq
    {F₁ F₂ F₀ F₃ F₄ Δ₁ Δ₂ Δ₀ Δ₃ Δ₄ P₁ P₂ P₀ P₃ P₄ N₁ N₂ N₀ N₃ N₄ h : ℝ}
    (hp1 : F₁ + Δ₁ = 2 * (P₁ + N₁))
    (hp2 : F₂ + Δ₂ = 2 * (P₂ + N₂))
    (hp0 : F₀ + Δ₀ = 2 * (P₀ + N₀))
    (hp3 : F₃ + Δ₃ = 2 * (P₃ + N₃))
    (hp4 : F₄ + Δ₄ = 2 * (P₄ + N₄)) :
    (1 / 4 : ℝ) *
      ((((F₁ + F₂ - 2 * F₀) + (F₃ + F₄ - 2 * F₀)) / h ^ 2 +
        ((Δ₁ + Δ₂ - 2 * Δ₀) + (Δ₃ + Δ₄ - 2 * Δ₀)) / h ^ 2) -
       2 * ((((P₁ - N₁) + (P₂ - N₂) - 2 * (P₀ - N₀)) +
             ((P₃ - N₃) + (P₄ - N₄) - 2 * (P₀ - N₀))) / h ^ 2)) =
    ((N₁ + N₂ - 2 * N₀) + (N₃ + N₄ - 2 * N₀)) / h ^ 2 := by
  have hnum :
      ((F₁ + F₂ - 2 * F₀) + (F₃ + F₄ - 2 * F₀)) +
      ((Δ₁ + Δ₂ - 2 * Δ₀) + (Δ₃ + Δ₄ - 2 * Δ₀)) -
      2 * (((P₁ - N₁) + (P₂ - N₂) - 2 * (P₀ - N₀)) +
           ((P₃ - N₃) + (P₄ - N₄) - 2 * (P₀ - N₀))) =
      4 * ((N₁ + N₂ - 2 * N₀) + (N₃ + N₄ - 2 * N₀)) := by
    linarith
  calc (1 / 4 : ℝ) *
        ((((F₁ + F₂ - 2 * F₀) + (F₃ + F₄ - 2 * F₀)) / h ^ 2 +
          ((Δ₁ + Δ₂ - 2 * Δ₀) + (Δ₃ + Δ₄ - 2 * Δ₀)) / h ^ 2) -
         2 * ((((P₁ - N₁) + (P₂ - N₂) - 2 * (P₀ - N₀)) +
               ((P₃ - N₃) + (P₄ - N₄) - 2 * (P₀ - N₀))) / h ^ 2))
      = (1 / 4 : ℝ) *
        ((((F₁ + F₂ - 2 * F₀) + (F₃ + F₄ - 2 * F₀)) +
          ((Δ₁ + Δ₂ - 2 * Δ₀) + (Δ₃ + Δ₄ - 2 * Δ₀)) -
          2 * (((P₁ - N₁) + (P₂ - N₂) - 2 * (P₀ - N₀)) +
               ((P₃ - N₃) + (P₄ - N₄) - 2 * (P₀ - N₀)))) / h ^ 2) := by ring
    _ = (1 / 4 : ℝ) * ((4 * ((N₁ + N₂ - 2 * N₀) + (N₃ + N₄ - 2 * N₀))) / h ^ 2) := by
        rw [hnum]
    _ = ((N₁ + N₂ - 2 * N₀) + (N₃ + N₄ - 2 * N₀)) / h ^ 2 := by ring

/-- **Global Five-Point Subharmonic Laplacian Law for the Infinity-Sector Modulus Squared
`|F_k^+(l, τ)|² = C_k^+(l, τ)² + S_k^+(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² |F_k^+|² + Δ_τ² |F_k^+|²) / h²) →
  (∂_l M_k + ∂_l Δ_k^{\cos})² + (∂_l N_k + ∂_l Δ_k^{\sin})² ≥ 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sectorModulusSq_Ioi_one_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
          ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2)) := by
  have hF := tendsto_div_sq_complexModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hΔ := tendsto_div_sq_imbalanceModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hH := tendsto_div_sq_sectorModulusSq_sub_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hcomb := ((hF.add hΔ).add (hH.const_mul 2)).const_mul (1 / 4 : ℝ)
  have hlim :
      (1 / 4 : ℝ) *
        ((4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) +
            4 * ((∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) +
          2 * (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) =
      ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
        ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 := by
    ring
  rw [hlim] at hcomb
  refine hcomb.congr' ?_
  have hmem : Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem] with h hh_mem
  have hh_eighth : |h| < 1 / 8 := abs_lt.mpr hh_mem
  have hl_half : |l| < 1 / 2 := by linarith
  have hlh_pos : |l + h| < 1 / 2 := by
    have := abs_add_le l h
    linarith
  have hlh_neg : |l - h| < 1 / 2 := by
    have := abs_sub l h
    linarith
  have hp1 := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq hk hν hlh_pos τ
  have hp2 := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq hk hν hlh_neg τ
  have hp0 := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq hk hν hl_half τ
  have hp3 := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq hk hν hl_half (τ + h)
  have hp4 := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq hk hν hl_half (τ - h)
  exact fivePoint_sector_pos_div_sq_eq hp1 hp2 hp0 hp3 hp4

/-- **Global Five-Point Subharmonic Laplacian Law for the Origin-Sector Modulus Squared
`|F_k^-(l, τ)|² = C_k^-(l, τ)² + S_k^-(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² |F_k^-|² + Δ_τ² |F_k^-|²) / h²) →
  (∂_l M_k − ∂_l Δ_k^{\cos})² + (∂_l N_k − ∂_l Δ_k^{\sin})² ≥ 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_sectorModulusSq_Ioc_zero_one_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
              ((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              2 * ((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
            (((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
              ((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              2 * ((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
          ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2)) := by
  have hF := tendsto_div_sq_complexModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hΔ := tendsto_div_sq_imbalanceModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hH := tendsto_div_sq_sectorModulusSq_sub_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hcomb := ((hF.add hΔ).sub (hH.const_mul 2)).const_mul (1 / 4 : ℝ)
  have hlim :
      (1 / 4 : ℝ) *
        ((4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) +
            4 * ((∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) -
          2 * (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) =
      ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
        ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 := by
    ring
  rw [hlim] at hcomb
  refine hcomb.congr' ?_
  have hmem : Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem] with h hh_mem
  have hh_eighth : |h| < 1 / 8 := abs_lt.mpr hh_mem
  have hl_half : |l| < 1 / 2 := by linarith
  have hlh_pos : |l + h| < 1 / 2 := by
    have := abs_add_le l h
    linarith
  have hlh_neg : |l - h| < 1 / 2 := by
    have := abs_sub l h
    linarith
  have hp1 := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq hk hν hlh_pos τ
  have hp2 := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq hk hν hlh_neg τ
  have hp0 := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq hk hν hl_half τ
  have hp3 := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq hk hν hl_half (τ + h)
  have hp4 := complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq hk hν hl_half (τ - h)
  exact fivePoint_sector_neg_div_sq_eq hp1 hp2 hp0 hp3 hp4

/-- **Master Witness Theorem for the Universal Five-Point Bilinear Product Laplacian, Holomorphic
Sector Product `(P_k, Q_k)`, Origin–Infinity Sector Wronskian `(H_k, W_k)`, and One-Sided Sector
Subharmonicity:**
There exists an explicit symmetric non-zero finite arc measure `ν` on `ArcParam` such that for all
`k ≥ 2`:
1. Across `|l| < 1/8` and `τ ∈ ℝ`, the cross-products `M_k(l, τ) N_k(l, τ)` and
   `Δ_k^{\cos}(l, τ) Δ_k^{\sin}(l, τ)` have vanishing five-point Laplacians;
2. Across `|l| < 1/8` and `τ ∈ ℝ`, the holomorphic product
   `F_k(l, τ) · Δ_k(l, τ) = P_k(l, τ) + i Q_k(l, τ)` satisfies both Cauchy–Riemann equations
   `∂_l P_k = ∂_τ Q_k` and `∂_l Q_k = −∂_τ P_k` and has vanishing five-point Laplacian;
3. Across `|l| < 1/8` and `τ ∈ ℝ`, the sector modulus imbalance `|F_k^+(l, τ)|² − |F_k^-(l, τ)|²`
   satisfies the exact five-point bilinear Laplacian law
   `((Δ_l² + Δ_τ²) (|F_k^+|² − |F_k^-|²)) / h² →
     4 ((∂_l M_k)(∂_l Δ_k^{\cos}) + (∂_l N_k)(∂_l Δ_k^{\sin}))`;
4. Across `|l| < 1/8` and `τ ∈ ℝ`, both one-sided sector moduli squared `|F_k^+(l, τ)|²` and
   `|F_k^-(l, τ)|²` satisfy the global five-point subharmonic Laplacian laws with non-negative
   limits `(∂_l M_k ± ∂_l Δ_k^{\cos})² + (∂_l N_k ± ∂_l Δ_k^{\sin})² ≥ 0`, and on the critical
   line `l = 0` satisfy `4 |F_k^+(0, τ)|² = M_k(0, τ)² + (2 ∫_{v > 0} sin(τv) Φ_k(v) dv)²`. -/
theorem exists_dyadic_bilinearProductLaplacian_sectorWronskian_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              ((((∫ x in Ioi (0 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                  (∫ x in Ioi (0 : ℝ),
                      x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  2 * (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
                ((∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                  (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  2 * (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h ^ 2))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) ∧
          Tendsto
            (fun h : ℝ =>
              ((((∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                  ((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) -
                (((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                  ((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              ((((((∫ x in Ioi (1 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      ((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                         (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                    (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      ((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
                    2 * (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      ((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
                  ((((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      ((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                    (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      ((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
                    2 * (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      ((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                  (∫ v in Ioi (0 : ℝ),
                     2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))))) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              (((((∫ x in Ioi (1 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (1 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (1 : ℝ),
                        x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                    2 * ((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                  (((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                    2 * ((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
                ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2))) ∧
        (∀ τ : ℝ,
          4 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) =
            (∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (2 * ∫ v in Ioi (0 : ℝ),
                Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk => ?_⟩
  refine ⟨fun l hl τ =>
      ⟨tendsto_div_sq_oscillatoryMellin_mul_sineMellin_fivePoint_laplacian_nhds_zero hk hν hl τ,
       tendsto_div_holomorphicProduct_cauchyRiemann_first_nhds_zero hk hν hl τ⟩,
    fun l hl τ => tendsto_div_sq_sectorModulusSq_sub_fivePoint_laplacian_nhds_zero hk hν hl τ,
    fun l hl τ => tendsto_div_sq_sectorModulusSq_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ,
    fun τ => four_mul_sectorModulusSq_Ioi_one_at_criticalLine_eq hk hν τ⟩

end

end RHTower
