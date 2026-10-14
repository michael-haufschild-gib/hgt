import GaloisForLFunctions.RHTower.ModularArcDyadicCrossSectorHolomorphyPhaseVelocityCurvature

/-!
# Division-free quotient Cauchy–Riemann equations, Wirtinger decomposition and Dirichlet energy of `(H_k, W_k)`, holomorphic Wronskian factorization, and multiplicative Liouville–Gauss logarithmic harmonicity of composite sector moduli

In `ModularArcDyadicLogarithmicSubharmonicityWronskianJacobian`,
`ModularArcDyadicOneSidedSectorCauchyRiemannLogarithmicHarmonicity`, and
`ModularArcDyadicCrossSectorHolomorphyPhaseVelocityCurvature`, we established the division-free
Liouville–Gauss logarithmic harmonicity of the individual moduli squared `|F_k(l, τ)|²`,
`|Δ_k(l, τ)|²`, `|F_k^+(l, τ)|²`, and `|F_k^-(l, τ)|²`, the Jacobian determinant of the
Hermitian–symplectic sector pair `(H_k, W_k)`, and the global five-point subharmonicity of the
composite moduli `|F_k(l, τ)|² · |Δ_k(l, τ)|² = H_k(l, τ)² + W_k(l, τ)²` and
`|F_k^+(l, τ)|² · |F_k^-(l, τ)|²`.

In this module we complete the **second-order Wirtinger, Dirichlet-energy, quotient Cauchy–Riemann,
holomorphic-Wronskian, and multiplicative Liouville–Gauss calculus** for `(H_k, W_k)` and the
composite sector moduli:

1. **Section 1 — Universal division-free quotient Cauchy–Riemann calculus, Wirtinger decomposition,
   complex Wronskian factorization, and multiplicative closure of Liouville–Gauss logarithmic
   harmonicity:**
   - Universal polynomial identities for the division-free Cauchy–Riemann equations of a quotient
     `(H − i W) / V = (M + i N) / (C + i S)`:
     `V (∂_l H + ∂_τ W) = H ∂_l V − W ∂_τ V` (`quotient_cauchyRiemann_first_identity`) and
     `V (∂_l W − ∂_τ H) = W ∂_l V − H ∂_τ V` (`quotient_cauchyRiemann_second_identity`).
   - Universal Wirtinger decomposition of `(H, W)`:
     `(∂_l H + ∂_τ W)² + (∂_l W − ∂_τ H)² = 4 (M² + N²)(C_l² + S_l²)`
     (`wirtinger_hermitian_symplectic_antiHolomorphic_norm_sq`) and
     `(∂_l H − ∂_τ W)² + (∂_l W + ∂_τ H)² = 4 (C² + S²)(M_l² + N_l²)`
     (`wirtinger_hermitian_symplectic_holomorphic_norm_sq`), together with the holomorphic product
     vs. complex Wronskian parallelogram law (`holomorphic_product_wronskian_parallelogram_identity`)
     and logarithmic-product / logarithmic-ratio gradient norm squared factorizations
     (`logarithmic_product_gradient_norm_sq_identity`,
     `logarithmic_ratio_gradient_norm_sq_identity`).
   - Universal limit theorems (`tendsto_quotient_cauchyRiemann_first_nhdsWithin_zero`,
     `tendsto_quotient_cauchyRiemann_second_nhdsWithin_zero`,
     `tendsto_wirtinger_antiHolomorphic_norm_sq_nhdsWithin_zero`,
     `tendsto_wirtinger_holomorphic_norm_sq_nhdsWithin_zero`,
     `tendsto_hermitian_symplectic_dirichlet_energy_nhdsWithin_zero`,
     `tendsto_liouville_gauss_mul_nhdsWithin_zero`).

2. **Section 2 — Global division-free quotient Cauchy–Riemann equations, Wirtinger decomposition,
   and Dirichlet energy for `(H_k, W_k)` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
   - Full-strip division-free quotient Cauchy–Riemann equations
     `|Δ_k|² (∂_l H_k + ∂_τ W_k) − (H_k ∂_l |Δ_k|² − W_k ∂_τ |Δ_k|²) = 0` and
     `|Δ_k|² (∂_l W_k − ∂_τ H_k) − (W_k ∂_l |Δ_k|² − H_k ∂_τ |Δ_k|²) = 0`.
   - Full-strip anti-holomorphic and holomorphic Wirtinger norm squared limits
     `(∂_l H_k + ∂_τ W_k)² + (∂_l W_k − ∂_τ H_k)² = 4 |F_k|² |Δ_k'|²` and
     `(∂_l H_k − ∂_τ W_k)² + (∂_l W_k + ∂_τ H_k)² = 4 |Δ_k|² |F_k'|²`, and total Dirichlet energy
     `(∂_l H_k)² + (∂_τ H_k)² + (∂_l W_k)² + (∂_τ W_k)² = 2 (|Δ_k|² |F_k'|² + |F_k|² |Δ_k'|²)`.

3. **Section 3 — Full-strip partial derivatives and division-free Liouville–Gauss logarithmic
   harmonicity of the composite moduli `|F_k(l, τ)|² · |Δ_k(l, τ)|²` and
   `|F_k^+(l, τ)|² · |F_k^-(l, τ)|²` (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
   - Horizontal and vertical partial derivatives and exact division-free Liouville–Gauss
     logarithmic harmonicity
     `(|F_k|² |Δ_k|²) Δ_5(|F_k|² |Δ_k|²) − ((∂_l(|F_k|² |Δ_k|²))² + (∂_τ(|F_k|² |Δ_k|²))²) → 0`
     and
     `(|F_k^+|² |F_k^-|²) Δ_5(|F_k^+|² |F_k^-|²) − ((∂_l(|F_k^+|² |F_k^-|²))² + (∂_τ(|F_k^+|² |F_k^-|²))²) → 0`.

4. **Section 4 — Critical-line (`l = 0`) pure reality of the complex Wronskian
   `F_k'(0, τ) Δ_k(0, τ) − F_k(0, τ) Δ_k'(0, τ)`, critical-line zero-locus Wirtinger reduction,
   and master witness theorem:**
   - Identical vanishing of the imaginary part of the complex Wronskian on `l = 0`, equality of its
     real part with `−∂_l H_k(0, τ)`, and vanishing of the anti-holomorphic Wirtinger norm squared
     `(∂_l H_k + ∂_τ W_k)² + (∂_l W_k − ∂_τ H_k)² → 0` at every zero of `F_k(l, τ)`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ## Section 1: Universal Division-Free Quotient Cauchy–Riemann Calculus, Wirtinger Decomposition, Complex Wronskian Factorization, and Multiplicative Closure of Liouville–Gauss Logarithmic Harmonicity -/

/-- **Universal First Division-Free Quotient Cauchy–Riemann Identity:**
For any `M, N, C, S, M_l, N_l, C_l, S_l : ℝ`, with `H = M C + N S`, `W = M S − N C`, and
`V = C² + S²` under Cauchy–Riemann (`M_t = −N_l`, `N_t = M_l`, `C_t = −S_l`, `S_t = C_l`),
`V (H_l + W_t) − (H V_l + W V_t) = 0`. -/
theorem quotient_cauchyRiemann_first_identity (M N C S M_l N_l C_l S_l : ℝ) :
    (C ^ 2 + S ^ 2) *
        (((M * C_l + C * M_l) + (N * S_l + S * N_l)) +
          ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))) -
      ((M * C + N * S) * (2 * (C * C_l + S * S_l)) +
        (M * S - N * C) * (2 * (C * (-S_l) + S * C_l))) = 0 := by
  ring

/-- **Universal Second Division-Free Quotient Cauchy–Riemann Identity:**
For any `M, N, C, S, M_l, N_l, C_l, S_l : ℝ`, with `H = M C + N S`, `W = M S − N C`, and
`V = C² + S²` under Cauchy–Riemann,
`V (W_l − H_t) − (W V_l − H V_t) = 0`. -/
theorem quotient_cauchyRiemann_second_identity (M N C S M_l N_l C_l S_l : ℝ) :
    (C ^ 2 + S ^ 2) *
        (((M * S_l + S * M_l) - (N * C_l + C * N_l)) -
          ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) -
      ((M * S - N * C) * (2 * (C * C_l + S * S_l)) -
        (M * C + N * S) * (2 * (C * (-S_l) + S * C_l))) = 0 := by
  ring

/-- **Universal Anti-Holomorphic Wirtinger Norm Squared Identity for `(H, W)`:**
`(H_l + W_t)² + (W_l − H_t)² = 4 (M² + N²)(C_l² + S_l²)`. -/
theorem wirtinger_hermitian_symplectic_antiHolomorphic_norm_sq (M N C S M_l N_l C_l S_l : ℝ) :
    (((M * C_l + C * M_l) + (N * S_l + S * N_l)) +
        ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))) ^ 2 +
      (((M * S_l + S * M_l) - (N * C_l + C * N_l)) -
        ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) ^ 2 =
    4 * (M ^ 2 + N ^ 2) * (C_l ^ 2 + S_l ^ 2) := by
  ring

/-- **Universal Holomorphic Wirtinger Norm Squared Identity for `(H, W)`:**
`(H_l − W_t)² + (W_l + H_t)² = 4 (C² + S²)(M_l² + N_l²)`. -/
theorem wirtinger_hermitian_symplectic_holomorphic_norm_sq (M N C S M_l N_l C_l S_l : ℝ) :
    (((M * C_l + C * M_l) + (N * S_l + S * N_l)) -
        ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))) ^ 2 +
      (((M * S_l + S * M_l) - (N * C_l + C * N_l)) +
        ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) ^ 2 =
    4 * (C ^ 2 + S ^ 2) * (M_l ^ 2 + N_l ^ 2) := by
  ring

/-- **Universal Total Dirichlet Energy Identity for `(H, W)`:**
`(H_l² + H_t²) + (W_l² + W_t²) = 2 ((M² + N²)(C_l² + S_l²) + (C² + S²)(M_l² + N_l²))`. -/
theorem hermitian_symplectic_dirichlet_energy_identity (M N C S M_l N_l C_l S_l : ℝ) :
    (((M * C_l + C * M_l) + (N * S_l + S * N_l)) ^ 2 +
        ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) ^ 2) +
      (((M * S_l + S * M_l) - (N * C_l + C * N_l)) ^ 2 +
        ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) ^ 2) =
    2 * ((M ^ 2 + N ^ 2) * (C_l ^ 2 + S_l ^ 2) +
      (C ^ 2 + S ^ 2) * (M_l ^ 2 + N_l ^ 2)) := by
  ring

/-- **Universal Parallelogram Law for the Holomorphic Product Derivative `F' G + F G'` and
Complex Wronskian `F' G − F G'`:**
`|F' G + F G'|² + |F' G − F G'|² = 2 (|F|² |G'|² + |G|² |F'|²)`. -/
theorem holomorphic_product_wronskian_parallelogram_identity (M N C S M_l N_l C_l S_l : ℝ) :
    (((M_l * C - N_l * S) + (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) + (M * S_l + N * C_l)) ^ 2) +
      (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) =
    2 * ((M ^ 2 + N ^ 2) * (C_l ^ 2 + S_l ^ 2) +
      (C ^ 2 + S ^ 2) * (M_l ^ 2 + N_l ^ 2)) := by
  ring

/-- **Universal Logarithmic-Product Gradient Norm Squared Factorization:**
`(U V_l + V U_l)² + (U V_t + V U_t)² = 4 U V |F' G + F G'|²`. -/
theorem logarithmic_product_gradient_norm_sq_identity (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) * (2 * (C * C_l + S * S_l)) +
        (C ^ 2 + S ^ 2) * (2 * (M * M_l + N * N_l))) ^ 2 +
      ((M ^ 2 + N ^ 2) * (2 * (C * (-S_l) + S * C_l)) +
        (C ^ 2 + S ^ 2) * (2 * (M * (-N_l) + N * M_l))) ^ 2 =
    4 * (M ^ 2 + N ^ 2) * (C ^ 2 + S ^ 2) *
      (((M_l * C - N_l * S) + (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) + (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Logarithmic-Ratio Gradient Norm Squared Factorization:**
`(V U_l − U V_l)² + (V U_t − U V_t)² = 4 U V |F' G − F G'|²`. -/
theorem logarithmic_ratio_gradient_norm_sq_identity (M N C S M_l N_l C_l S_l : ℝ) :
    ((C ^ 2 + S ^ 2) * (2 * (M * M_l + N * N_l)) -
        (M ^ 2 + N ^ 2) * (2 * (C * C_l + S * S_l))) ^ 2 +
      ((C ^ 2 + S ^ 2) * (2 * (M * (-N_l) + N * M_l)) -
        (M ^ 2 + N ^ 2) * (2 * (C * (-S_l) + S * C_l))) ^ 2 =
    4 * (M ^ 2 + N ^ 2) * (C ^ 2 + S ^ 2) *
      (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Sector Skew-Duality for the Real Part of the Complex Wronskian:**
`\text{Re}(F' Δ − F Δ') = −2 \text{Re}(F^{+\prime} F^- − F^+ F^{-\prime})`. -/
theorem sector_holomorphic_wronskian_re_skew_identity
    (Cp Cm Sp Sm Cp_l Cm_l Sp_l Sm_l : ℝ) :
    (((Cp_l + Cm_l) * (Cp - Cm) - (Sp_l + Sm_l) * (Sp - Sm)) -
        ((Cp + Cm) * (Cp_l - Cm_l) - (Sp + Sm) * (Sp_l - Sm_l))) =
      -2 * ((Cp_l * Cm - Sp_l * Sm) - (Cp * Cm_l - Sp * Sm_l)) := by
  ring

/-- **Universal Sector Skew-Duality for the Imaginary Part of the Complex Wronskian:**
`\text{Im}(F' Δ − F Δ') = −2 \text{Im}(F^{+\prime} F^- − F^+ F^{-\prime})`. -/
theorem sector_holomorphic_wronskian_im_skew_identity
    (Cp Cm Sp Sm Cp_l Cm_l Sp_l Sm_l : ℝ) :
    (((Cp_l + Cm_l) * (Sp - Sm) + (Sp_l + Sm_l) * (Cp - Cm)) -
        ((Cp + Cm) * (Sp_l - Sm_l) + (Sp + Sm) * (Cp_l - Cm_l))) =
      -2 * ((Cp_l * Sm + Sp_l * Cm) - (Cp * Sm_l + Sp * Cm_l)) := by
  ring

/-- **Universal First Division-Free Quotient Cauchy–Riemann Limit Theorem:**
`V₀ (∂_l^h H + ∂_τ^h W) − (H₀ ∂_l^h V + W₀ ∂_τ^h V) → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_quotient_cauchyRiemann_first_nhdsWithin_zero
    {H_l W_t V_l V_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))))
    (hVl : Tendsto (fun h : ℝ => (V_l h - (C ^ 2 + S ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (C * C_l + S * S_l))))
    (hVt : Tendsto (fun h : ℝ => (V_t h - (C ^ 2 + S ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        (C ^ 2 + S ^ 2) * (((H_l h - (M * C + N * S)) / h) + ((W_t h - (M * S - N * C)) / h)) -
          ((M * C + N * S) * ((V_l h - (C ^ 2 + S ^ 2)) / h) +
            (M * S - N * C) * ((V_t h - (C ^ 2 + S ^ 2)) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hcomb :=
    ((hHl.add hWt).const_mul (C ^ 2 + S ^ 2)).sub
      ((hVl.const_mul (M * C + N * S)).add (hVt.const_mul (M * S - N * C)))
  rw [quotient_cauchyRiemann_first_identity M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Second Division-Free Quotient Cauchy–Riemann Limit Theorem:**
`V₀ (∂_l^h W − ∂_τ^h H) − (W₀ ∂_l^h V − H₀ ∂_τ^h V) → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_quotient_cauchyRiemann_second_nhdsWithin_zero
    {W_l H_t V_l V_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l))))
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hVl : Tendsto (fun h : ℝ => (V_l h - (C ^ 2 + S ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (C * C_l + S * S_l))))
    (hVt : Tendsto (fun h : ℝ => (V_t h - (C ^ 2 + S ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        (C ^ 2 + S ^ 2) * (((W_l h - (M * S - N * C)) / h) - ((H_t h - (M * C + N * S)) / h)) -
          ((M * S - N * C) * ((V_l h - (C ^ 2 + S ^ 2)) / h) -
            (M * C + N * S) * ((V_t h - (C ^ 2 + S ^ 2)) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hcomb :=
    ((hWl.sub hHt).const_mul (C ^ 2 + S ^ 2)).sub
      ((hVl.const_mul (M * S - N * C)).sub (hVt.const_mul (M * C + N * S)))
  rw [quotient_cauchyRiemann_second_identity M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Anti-Holomorphic Wirtinger Norm Squared Limit Theorem for `(H, W)`:**
`(∂_l^h H + ∂_τ^h W)² + (∂_l^h W − ∂_τ^h H)² → 4 (M² + N²)(C_l² + S_l²)`. -/
theorem tendsto_wirtinger_antiHolomorphic_norm_sq_nhdsWithin_zero
    {H_l H_t W_l W_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)))) :
    Tendsto
      (fun h : ℝ =>
        (((H_l h - (M * C + N * S)) / h) + ((W_t h - (M * S - N * C)) / h)) ^ 2 +
          (((W_l h - (M * S - N * C)) / h) - ((H_t h - (M * C + N * S)) / h)) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (4 * (M ^ 2 + N ^ 2) * (C_l ^ 2 + S_l ^ 2))) := by
  have hcomb := ((hHl.add hWt).pow 2).add ((hWl.sub hHt).pow 2)
  rw [wirtinger_hermitian_symplectic_antiHolomorphic_norm_sq M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Holomorphic Wirtinger Norm Squared Limit Theorem for `(H, W)`:**
`(∂_l^h H − ∂_τ^h W)² + (∂_l^h W + ∂_τ^h H)² → 4 (C² + S²)(M_l² + N_l²)`. -/
theorem tendsto_wirtinger_holomorphic_norm_sq_nhdsWithin_zero
    {H_l H_t W_l W_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)))) :
    Tendsto
      (fun h : ℝ =>
        (((H_l h - (M * C + N * S)) / h) - ((W_t h - (M * S - N * C)) / h)) ^ 2 +
          (((W_l h - (M * S - N * C)) / h) + ((H_t h - (M * C + N * S)) / h)) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (4 * (C ^ 2 + S ^ 2) * (M_l ^ 2 + N_l ^ 2))) := by
  have hcomb := ((hHl.sub hWt).pow 2).add ((hWl.add hHt).pow 2)
  rw [wirtinger_hermitian_symplectic_holomorphic_norm_sq M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Total Dirichlet Energy Limit Theorem for `(H, W)`:**
`((∂_l^h H)² + (∂_τ^h H)²) + ((∂_l^h W)² + (∂_τ^h W)²) →
  2 ((M² + N²)(C_l² + S_l²) + (C² + S²)(M_l² + N_l²))`. -/
theorem tendsto_hermitian_symplectic_dirichlet_energy_nhdsWithin_zero
    {H_l H_t W_l W_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)))) :
    Tendsto
      (fun h : ℝ =>
        (((H_l h - (M * C + N * S)) / h) ^ 2 + ((H_t h - (M * C + N * S)) / h) ^ 2) +
          (((W_l h - (M * S - N * C)) / h) ^ 2 + ((W_t h - (M * S - N * C)) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((M ^ 2 + N ^ 2) * (C_l ^ 2 + S_l ^ 2) +
          (C ^ 2 + S ^ 2) * (M_l ^ 2 + N_l ^ 2)))) := by
  have hcomb := ((hHl.pow 2).add (hHt.pow 2)).add ((hWl.pow 2).add (hWt.pow 2))
  rw [hermitian_symplectic_dirichlet_energy_identity M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Multiplicative Closure of Division-Free Liouville–Gauss Logarithmic Harmonicity:**
If `U` and `V` satisfy `U₀ L_U = D_l_U² + D_t_U²` and `V₀ L_V = D_l_V² + D_t_V²`, then their
product `U · V` satisfies the division-free Liouville–Gauss logarithmic harmonicity limit
`(U₀ V₀) Δ_5(U V)(h) − ((∂_l^h(U V))² + (∂_τ^h(U V))²) → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_liouville_gauss_mul_nhdsWithin_zero
    {U_l U_t V_l V_t : ℝ → ℝ} {U₀ V₀ D_l_U D_t_U D_l_V D_t_V L_U L_V : ℝ}
    (hUl : Tendsto (fun h : ℝ => (U_l h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_l_U))
    (hUt : Tendsto (fun h : ℝ => (U_t h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_t_U))
    (hVl : Tendsto (fun h : ℝ => (V_l h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_l_V))
    (hVt : Tendsto (fun h : ℝ => (V_t h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_t_V))
    (hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds L_U))
    (hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds L_V))
    (hLG_U : U₀ * L_U = D_l_U ^ 2 + D_t_U ^ 2)
    (hLG_V : V₀ * L_V = D_l_V ^ 2 + D_t_V ^ 2) :
    Tendsto
      (fun h : ℝ =>
        (U₀ * V₀) *
            ((((U_l h * V_l h + U_l (-h) * V_l (-h) - 2 * (U₀ * V₀)) +
                (U_t h * V_t h + U_t (-h) * V_t (-h) - 2 * (U₀ * V₀))) / h ^ 2)) -
          (((U_l h * V_l h - U₀ * V₀) / h) ^ 2 + ((U_t h * V_t h - U₀ * V₀) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hdl := tendsto_div_mul_sub_nhdsWithin_zero hUl hVl
  have hdt := tendsto_div_mul_sub_nhdsWithin_zero hUt hVt
  have hLap := tendsto_div_sq_fivePoint_mul_general_nhdsWithin_zero hUl hUt hVl hVt hUlap hVlap
  have hcomb := (hLap.const_mul (U₀ * V₀)).sub ((hdl.pow 2).add (hdt.pow 2))
  have hlim :
      (U₀ * V₀) * (U₀ * L_V + V₀ * L_U + 2 * (D_l_U * D_l_V + D_t_U * D_t_V)) -
        ((U₀ * D_l_V + V₀ * D_l_U) ^ 2 + (U₀ * D_t_V + V₀ * D_t_U) ^ 2) = 0 := by
    calc (U₀ * V₀) * (U₀ * L_V + V₀ * L_U + 2 * (D_l_U * D_l_V + D_t_U * D_t_V)) -
          ((U₀ * D_l_V + V₀ * D_l_U) ^ 2 + (U₀ * D_t_V + V₀ * D_t_U) ^ 2)
        = U₀ ^ 2 * (V₀ * L_V - (D_l_V ^ 2 + D_t_V ^ 2)) +
          V₀ ^ 2 * (U₀ * L_U - (D_l_U ^ 2 + D_t_U ^ 2)) := by ring
      _ = U₀ ^ 2 * 0 + V₀ ^ 2 * 0 := by rw [hLG_U, hLG_V, sub_self, sub_self]
      _ = 0 := by ring
  rw [hlim] at hcomb
  refine hcomb.congr (fun h => by ring)


/-! ## Section 2: Global Division-Free Quotient Cauchy–Riemann Equations, Wirtinger Decomposition, and Dirichlet Energy for `(H_k, W_k)` Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`) -/

/-- **Global First Division-Free Quotient Cauchy–Riemann Equation for `(H_k, W_k)` Across
`|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`|Δ_k(l, τ)|² (∂_l H_k(l, τ) + ∂_τ W_k(l, τ)) − (H_k(l, τ) ∂_l |Δ_k(l, τ)|² + W_k(l, τ) ∂_τ |Δ_k(l, τ)|²) = 0`. -/
theorem tendsto_quotient_cauchyRiemann_first_hermitianWronskian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
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
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) +
            ((((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) -
          (((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
            (((((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) +
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
            (((((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_quotient_cauchyRiemann_first_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_vert_shift_nhds_zero hk hν hl τ)

/-- **Global Second Division-Free Quotient Cauchy–Riemann Equation for `(H_k, W_k)` Across
`|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`|Δ_k(l, τ)|² (∂_l W_k(l, τ) − ∂_τ H_k(l, τ)) − (W_k(l, τ) ∂_l |Δ_k(l, τ)|² − H_k(l, τ) ∂_τ |Δ_k(l, τ)|²) = 0`. -/
theorem tendsto_quotient_cauchyRiemann_second_hermitianWronskian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
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
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) -
            ((((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) -
          (((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
            (((((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
            (((((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_quotient_cauchyRiemann_second_nhdsWithin_zero
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_vert_shift_nhds_zero hk hν hl τ)

/-- **Global Anti-Holomorphic Wirtinger Norm Squared Limit for `(H_k, W_k)` Across `|l| < 1/8`,
`τ ∈ ℝ` (`k ≥ 2`):**
`(∂_l^h H_k + ∂_τ^h W_k)² + (∂_l^h W_k − ∂_τ^h H_k)² → 4 |F_k(l, τ)|² · |Δ_k'(l, τ)|²`. -/
theorem tendsto_wirtinger_antiHolomorphic_norm_sq_hermitianWronskian_nhds_zero
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
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) +
          ((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) ^ 2 +
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
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) -
          ((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) :=
  tendsto_wirtinger_antiHolomorphic_norm_sq_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)

/-- **Global Holomorphic Wirtinger Norm Squared Limit for `(H_k, W_k)` Across `|l| < 1/8`, `τ ∈ ℝ`
(`k ≥ 2`):**
`(∂_l^h H_k − ∂_τ^h W_k)² + (∂_l^h W_k + ∂_τ^h H_k)² → 4 |Δ_k(l, τ)|² · |F_k'(l, τ)|²`. -/
theorem tendsto_wirtinger_holomorphic_norm_sq_hermitianWronskian_nhds_zero
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
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) -
          ((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) ^ 2 +
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
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) +
          ((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) :=
  tendsto_wirtinger_holomorphic_norm_sq_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)

/-- **Global Total Dirichlet Energy Limit for `(H_k, W_k)` Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((∂_l^h H_k)² + (∂_τ^h H_k)²) + ((∂_l^h W_k)² + (∂_τ^h W_k)²) →
  2 (|F_k(l, τ)|² · |Δ_k'(l, τ)|² + |Δ_k(l, τ)|² · |F_k'(l, τ)|²)`. -/
theorem tendsto_hermitianWronskian_dirichlet_energy_nhds_zero
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
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) ^ 2 +
          ((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) ^ 2) +
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
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) ^ 2 +
          ((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * (((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
              ((∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) +
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
              ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)))) :=
  tendsto_hermitian_symplectic_dirichlet_energy_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)


/-! ## Section 3: Full-Strip Partial Derivatives and Division-Free Liouville–Gauss Logarithmic Harmonicity of the Composite Moduli `|F_k(l, τ)|² · |Δ_k(l, τ)|²` and `|F_k^+(l, τ)|² · |F_k^-(l, τ)|²` -/

/-- **Global Division-Free Liouville–Gauss Logarithmic Harmonicity of the Holomorphic Product
Modulus Squared `|F_k(l, τ)|² · |Δ_k(l, τ)|² = H_k(l, τ)² + W_k(l, τ)²` Across `|l| < 1/8`,
`τ ∈ ℝ` (`k ≥ 2`):**
`(|F_k|² |Δ_k|²) · Δ_5(|F_k|² |Δ_k|²)(h) −
  ((∂_l^h(|F_k|² |Δ_k|²))² + (∂_τ^h(|F_k|² |Δ_k|²))²) → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_hermitianWronskianNormSq_liouville_gauss_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) *
          ((((((∫ x in Ioi (0 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                  (((∫ x in Ioi (1 : ℝ),
                         x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                         x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                (((∫ x in Ioi (0 : ℝ),
                      x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                  (((∫ x in Ioi (1 : ℝ),
                         x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                         x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
                2 * (((∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                  (((∫ x in Ioi (1 : ℝ),
                         x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                         x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
              ((((∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                  (((∫ x in Ioi (1 : ℝ),
                         x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                         x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                (((∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                  (((∫ x in Ioi (1 : ℝ),
                         x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                         x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
                2 * (((∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                  (((∫ x in Ioi (1 : ℝ),
                         x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                         x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                         x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2) -
          ((((((∫ x in Ioi (0 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((∫ x in Ioi (1 : ℝ),
                       x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                       x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
              (((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2 +
            (((((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
              (((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  set U_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (0 : ℝ),
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set U_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set U₀ : ℝ :=
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set V_l : ℝ → ℝ := fun h =>
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set V_t : ℝ → ℝ := fun h =>
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set V₀ : ℝ :=
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  have hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
    refine (tendsto_div_sq_complexModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [U_l, U_t, U₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
    refine (tendsto_div_sq_imbalanceModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [V_l, V_t, V₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_liouville_gauss_mul_nhdsWithin_zero
    (tendsto_div_complexModulusSq_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_complexModulusSq_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_vert_shift_nhds_zero hk hν hl τ)
    hUlap hVlap
    (by ring)
    (by ring)
  refine h.congr (fun h => ?_)
  dsimp [U_l, U_t, U₀, V_l, V_t, V₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Global Division-Free Liouville–Gauss Logarithmic Harmonicity of the Cross-Sector Modulus
Product `|F_k^+(l, τ)|² · |F_k^-(l, τ)|²` Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(|F_k^+|² |F_k^-|²) · Δ_5(|F_k^+|² |F_k^-|²)(h) −
  ((∂_l^h(|F_k^+|² |F_k^-|²))² + (∂_τ^h(|F_k^+|² |F_k^-|²))²) → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_sectorModulusSq_mul_liouville_gauss_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
            ((∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) *
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2) -
          ((((((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2 +
            (((((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
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
  have h := tendsto_liouville_gauss_mul_nhdsWithin_zero
    (tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorModulusSq_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorModulusSq_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorModulusSq_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    hUlap hVlap
    (by ring)
    (by ring)
  refine h.congr (fun h => ?_)
  dsimp [U_l, U_t, U₀, V_l, V_t, V₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]


/-! ## Section 4: Critical-Line Pure Reality of the Complex Wronskian, Zero-Locus Wirtinger Vanishing, and Master Witness Theorem -/

/-- **Zero-Locus Anti-Holomorphic Wirtinger Vanishing for `(H_k, W_k)` (`k ≥ 2`, `|l| < 1/8`,
`τ ∈ ℝ`):**
At any point `(l, τ)` in `|l| < 1/8, τ ∈ ℝ` where `M_k(l, τ)² + N_k(l, τ)² = 0`, the
anti-holomorphic Wirtinger norm squared `(∂_l^h H_k + ∂_τ^h W_k)² + (∂_l^h W_k − ∂_τ^h H_k)²`
converges to `0`. -/
theorem tendsto_wirtinger_antiHolomorphic_norm_sq_at_zero_locus
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) {τ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 = 0) :
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
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) +
          ((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) ^ 2 +
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
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) -
          ((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h := tendsto_wirtinger_antiHolomorphic_norm_sq_hermitianWronskian_nhds_zero hk hν hl τ
  rw [hzero, mul_zero, zero_mul] at h
  exact h

/-- **Critical-Line (`l = 0`) Identical Vanishing of the Imaginary Part of the Complex Wronskian
`F_k'(0, τ) Δ_k(0, τ) − F_k(0, τ) Δ_k'(0, τ)` (`k ≥ 1`, `τ ∈ ℝ`):**
On the critical line `l = 0`,
`((∂_l M_k(0, τ)) Δ_k^{\sin}(0, τ) + (∂_l N_k(0, τ)) Δ_k^{\cos}(0, τ)) −
  (M_k(0, τ) (∂_l Δ_k^{\sin}(0, τ)) + N_k(0, τ) (∂_l Δ_k^{\cos}(0, τ))) = 0`. -/
theorem holomorphicWronskian_im_at_criticalLine_eq_zero
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    ((∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
    ((∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
      (∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) = 0 := by
  have hsinh_full :
      (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    have h0 :
        (fun v : ℝ => v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun _ => 0 := by
      ext v; rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
    rw [h0, integral_zero]
  have hsinh_half :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    have h0 :
        (fun v : ℝ => 2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun _ => 0 := by
      ext v; rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
    rw [h0, integral_zero]
  have hDcos :
      (∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x = 0 := by
    rw [setIntegral_Ioc_zero_one_cos_log_eq_setIntegral_Ioi_one hk ν τ, sub_self]
  have hN0 := setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk ν τ
  rw [hsinh_full, hsinh_half, hDcos, hN0]
  ring

/-- **Critical-Line (`l = 0`) Real Part of the Complex Wronskian
`F_k'(0, τ) Δ_k(0, τ) − F_k(0, τ) Δ_k'(0, τ)` (`k ≥ 1`, `τ ∈ ℝ`):**
On the critical line `l = 0`, the real part of `F_k'(0, τ) Δ_k(0, τ) − F_k(0, τ) Δ_k'(0, τ)` equals
`−∂_l H_k(0, τ) = −(M_k(0, τ) ∫_{v > 0} 2 v cos(τ v) Φ_k(v) dv + (∫_ℝ v sin(τ v) Φ_k(v) dv)(∫_{v > 0} 2 sin(τ v) Φ_k(v) dv))`. -/
theorem holomorphicWronskian_re_at_criticalLine_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    ((∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
    ((∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
      (∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) =
    -((∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
      (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
        (∫ v in Ioi (0 : ℝ),
          2 * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  have hsinh_full :
      (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    have h0 :
        (fun v : ℝ => v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun _ => 0 := by
      ext v; rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
    rw [h0, integral_zero]
  have hcosh_full :
      (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    congr 1; ext v; rw [zero_mul, Real.cosh_zero, mul_one]
  have hcosh_half :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v in Ioi (0 : ℝ),
        2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    congr 1; ext v; rw [zero_mul, Real.cosh_zero, mul_one]
  have hN0 := setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk ν τ
  have hDsin :
      (∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x =
      ∫ v in Ioi (0 : ℝ), 2 * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    have h := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_sin_log hk ν τ
    have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
    rw [hl0] at h
    have h2 :
        (∫ v in Ioi (0 : ℝ), 2 * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        2 * ∫ v in Ioi (0 : ℝ), Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
      rw [← integral_const_mul]
      congr 1; ext v; ring
    rw [h2, h]
  rw [hsinh_full, hcosh_full, hcosh_half, hN0, hDsin]
  ring

/-- **Master Witness Theorem for Division-Free Quotient Cauchy–Riemann Equations, Wirtinger
Decomposition and Dirichlet Energy of `(H_k, W_k)`, Multiplicative Liouville–Gauss Logarithmic
Harmonicity of Composite Sector Moduli, and Critical-Line Complex Wronskian Reality:**
There exists an explicit symmetric non-zero finite arc measure `ν` on `ArcParam` such that for all
`k ≥ 2`:
1. Across `|l| < 1/8` and `τ ∈ ℝ`, the sector modulus imbalance and sector Wronskian `(H_k, W_k)`
   satisfy the global division-free quotient Cauchy–Riemann equations
   `|Δ_k|² (∂_l H_k + ∂_τ W_k) − (H_k ∂_l |Δ_k|² + W_k ∂_τ |Δ_k|²) = 0` and
   `|Δ_k|² (∂_l W_k − ∂_τ H_k) − (W_k ∂_l |Δ_k|² − H_k ∂_τ |Δ_k|²) = 0`;
2. Across `|l| < 1/8` and `τ ∈ ℝ`, the composite moduli squared
   `|F_k(l, τ)|² · |Δ_k(l, τ)|² = H_k(l, τ)² + W_k(l, τ)²` and
   `|F_k^+(l, τ)|² · |F_k^-(l, τ)|²` satisfy the division-free Liouville–Gauss logarithmic
   harmonicity laws;
3. On the critical line `l = 0`, the imaginary part of the complex Wronskian
   `F_k'(0, τ) Δ_k(0, τ) − F_k(0, τ) Δ_k'(0, τ)` vanishes identically and its real part equals
   `−∂_l H_k(0, τ)`. -/
theorem exists_dyadic_holomorphicWronskian_quotientCauchyRiemann_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
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
                            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                    ((∫ x in Ioi (0 : ℝ),
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
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) +
                  ((((∫ x in Ioi (0 : ℝ),
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
                            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                    ((∫ x in Ioi (0 : ℝ),
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
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) -
                (((∫ x in Ioi (0 : ℝ),
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
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
                  (((((∫ x in Ioi (1 : ℝ),
                            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      (((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) +
                  ((∫ x in Ioi (0 : ℝ),
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
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
                  (((((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      (((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) ∧
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                  (((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) *
                ((((((∫ x in Ioi (0 : ℝ),
                            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          (∫ x in Ioi (0 : ℝ),
                            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                        (((∫ x in Ioi (1 : ℝ),
                               x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          ((∫ x in Ioi (1 : ℝ),
                               x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                      (((∫ x in Ioi (0 : ℝ),
                            x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          (∫ x in Ioi (0 : ℝ),
                            x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                        (((∫ x in Ioi (1 : ℝ),
                               x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          ((∫ x in Ioi (1 : ℝ),
                               x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
                      2 * (((∫ x in Ioi (0 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          (∫ x in Ioi (0 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                        (((∫ x in Ioi (1 : ℝ),
                               x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          ((∫ x in Ioi (1 : ℝ),
                               x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
                    ((((∫ x in Ioi (0 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          (∫ x in Ioi (0 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                        (((∫ x in Ioi (1 : ℝ),
                               x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          ((∫ x in Ioi (1 : ℝ),
                               x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                      (((∫ x in Ioi (0 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          (∫ x in Ioi (0 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                        (((∫ x in Ioi (1 : ℝ),
                               x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          ((∫ x in Ioi (1 : ℝ),
                               x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
                      2 * (((∫ x in Ioi (0 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          (∫ x in Ioi (0 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                        (((∫ x in Ioi (1 : ℝ),
                               x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                          ((∫ x in Ioi (1 : ℝ),
                               x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                            ∫ x in Ioc (0 : ℝ) 1,
                               x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2) -
                ((((((∫ x in Ioi (0 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                      (((∫ x in Ioi (1 : ℝ),
                             x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                             x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                             x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                             x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
                    (((∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                      (((∫ x in Ioi (1 : ℝ),
                             x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                             x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                             x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                             x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2 +
                  (((((∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                      (((∫ x in Ioi (1 : ℝ),
                             x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                             x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                             x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                             x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
                    (((∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                      (((∫ x in Ioi (1 : ℝ),
                             x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                             x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                             x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                             x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) ∧
        (∀ τ : ℝ,
          ((∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) = 0) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  refine ⟨fun l hl τ =>
      ⟨tendsto_quotient_cauchyRiemann_first_hermitianWronskian_nhds_zero hk hν hl τ,
       tendsto_hermitianWronskianNormSq_liouville_gauss_nhds_zero hk hν hl τ⟩,
    fun τ => holomorphicWronskian_im_at_criticalLine_eq_zero hk1 ν τ⟩

end

end RHTower
