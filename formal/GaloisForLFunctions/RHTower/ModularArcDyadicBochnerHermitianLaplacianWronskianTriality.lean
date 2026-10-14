import GaloisForLFunctions.RHTower.ModularArcDyadicHolomorphicWronskianQuotientCauchyRiemann

/-!
# Bochner–Hermitian Laplacian Norm Factorization, Hermitian–Symplectic Self-Wronskian Calculus, and Wronskian–Holomorphic-Product Triality for the Dyadic Modular Arc Tower

In `ModularArcDyadicBilinearProductLaplacianSectorWronskian`,
`ModularArcDyadicLogarithmicSubharmonicityWronskianJacobian`, and
`ModularArcDyadicHolomorphicWronskianQuotientCauchyRiemann`, we established the five-point
Laplacian laws for the Hermitian pairing `H_k(l, τ) = M_k Δ_k^{\cos} + N_k Δ_k^{\sin}` and
symplectic Wronskian `W_k(l, τ) = M_k Δ_k^{\sin} − N_k Δ_k^{\cos}`, the Wirtinger decomposition
and total Dirichlet energy of `(H_k, W_k)`, and the division-free quotient Cauchy–Riemann equations.

In this module we build the **Bochner–Hermitian Laplacian norm factorization, the self-Wronskian
phase-velocity calculus of `(H_k, W_k)`, and the exact triality linking the holomorphic product
`(P_k, Q_k) = F_k · Δ_k`, the Hermitian–symplectic pair `(H_k, W_k) = \overline{F_k} · Δ_k`, and
the complex Wronskian `W_{k,\mathrm{re}} + i W_{k,\mathrm{im}} = F_k' Δ_k − F_k Δ_k'`**:

1. **Section 1 — Universal Wronskian–Holomorphic-Product Triality, Hermitian–Symplectic
   Self-Wronskian Calculus, and Bochner–Hermitian Laplacian Decomposition:**
   - Exact algebraic triality between `(P, Q)`, `(H, W)`, and `(W_re, W_im)`:
     `P W_re + Q W_im = W ∂_τ H − H ∂_τ W` (`holomorphic_product_wronskian_re_dot_identity`),
     `P W_im − Q W_re = W ∂_l H − H ∂_l W` (`holomorphic_product_wronskian_im_cross_identity`),
     `(H ∂_l W − W ∂_l H)² + (H ∂_τ W − W ∂_τ H)² = (H² + W²)(W_re² + W_im²)`
     (`hermitian_symplectic_selfWronskian_norm_sq_identity`), and the radial + phase-velocity
     energy split (`hermitian_symplectic_radial_selfWronskian_energy_split_identity`).
   - Universal Bochner–Hermitian Laplacian identities:
     `(Δ H)² + (Δ W)² = Δ(|F|²) · Δ(|G|²)` (`bochner_hermitian_symplectic_laplacian_norm_sq_identity`),
     `H Δ H + W Δ W = ∇(|F|²) · ∇(|G|²) = |(F G)'|² − |W|²`
     (`hermitian_symplectic_laplacian_dot_eq_modulusSq_grad_dot`,
     `holomorphic_product_deriv_sub_wronskian_norm_sq_identity`), and
     `2 |W|² = (|∇ H|² + |∇ W|²) − (H Δ H + W Δ W)`
     (`two_mul_wronskian_norm_sq_eq_dirichlet_sub_laplacian_dot`).
   - Universal limit theorems (`tendsto_hermitian_symplectic_selfWronskian_horiz_nhdsWithin_zero`,
     `tendsto_hermitian_symplectic_selfWronskian_vert_nhdsWithin_zero`,
     `tendsto_hermitian_symplectic_selfWronskian_norm_sq_nhdsWithin_zero`,
     `tendsto_bochner_hermitian_symplectic_laplacian_norm_sq_nhdsWithin_zero`,
     `tendsto_hermitian_symplectic_laplacian_dot_sub_modulusSq_grad_dot_nhdsWithin_zero`,
     `tendsto_two_mul_wronskian_norm_sq_from_dirichlet_and_laplacian_nhdsWithin_zero`).

2. **Section 2 — Global Hermitian–Symplectic Self-Wronskian Calculus and Wronskian–Holomorphic-Product
   Triality for `(H_k, W_k)` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
   - Full-strip horizontal and vertical self-Wronskians `H_k ∂_l W_k − W_k ∂_l H_k` and
     `H_k ∂_τ W_k − W_k ∂_τ H_k` and their norm-squared factorization
     `(|F_k|² |Δ_k|²)(W_{k,\mathrm{re}}² + W_{k,\mathrm{im}}²)`.

3. **Section 3 — Global Bochner–Hermitian Five-Point Laplacian Norm Factorization and
   Laplacian–Dirichlet Reconstruction of the Holomorphic Wronskian Norm Squared (`|l| < 1/8`, `τ ∈ ℝ`):**
   - Full-strip Bochner–Hermitian Laplacian norm factorization
     `((Δ_5 H_k / h²)² + (Δ_5 W_k / h²)²) − (Δ_5 |F_k|² / h²)(Δ_5 |Δ_k|² / h²) → 0`,
     Laplacian–gradient dot-product duality, and exact reconstruction of `2 |F_k' Δ_k − F_k Δ_k'|²`.

4. **Section 4 — Critical-Line (`l = 0`) Identical Discrete Five-Point Laplacian Vanishing of `H_k`,
   Critical-Line Bochner–Hermitian Wronskian Identity, and Master Witness Theorem:**
   - Odd horizontal reflection antisymmetry `H_k(−l, τ) = −H_k(l, τ)` and identical finite-step
     five-point discrete Laplacian vanishing `Δ_l² H_k(0, τ; h) + Δ_τ² H_k(0, τ; h) = 0` for all
     `h ∈ ℝ`, critical-line Bochner–Hermitian identity
     `((Δ_5 W_k(0, τ; h) / h²)² − (Δ_5 |F_k|²(0, τ; h) / h²)(Δ_5 |Δ_k|²(0, τ; h) / h²)) → 0`,
     and master witness theorem `exists_dyadic_bochnerHermitianLaplacian_wronskianTriality_arcWitness`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ## Section 1: Universal Wronskian–Holomorphic-Product Triality, Hermitian–Symplectic Self-Wronskian Calculus, and Bochner–Hermitian Laplacian Decomposition -/

/-- **Universal First Wronskian–Holomorphic-Product Triality Identity:**
For `P = M C − N S`, `Q = M S + N C`, `H = M C + N S`, `W = M S − N C`, and
`W_re + i W_im = F' G − F G'` under Cauchy–Riemann (`M_t = −N_l`, `N_t = M_l`, `C_t = −S_l`, `S_t = C_l`),
`P W_re + Q W_im = W H_t − H W_t`. -/
theorem holomorphic_product_wronskian_re_dot_identity (M N C S M_l N_l C_l S_l : ℝ) :
    (M * C - N * S) * ((M_l * C - N_l * S) - (M * C_l - N * S_l)) +
      (M * S + N * C) * ((M_l * S + N_l * C) - (M * S_l + N * C_l)) =
    (M * S - N * C) * ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) -
      (M * C + N * S) * ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) := by
  ring

/-- **Universal First Wronskian–Holomorphic-Product Modulus-Gradient Identity:**
`2 (P W_re + Q W_im) = V U_l − U V_l`. -/
theorem holomorphic_product_wronskian_re_dot_eq_modulusSq_grad (M N C S M_l N_l C_l S_l : ℝ) :
    2 * ((M * C - N * S) * ((M_l * C - N_l * S) - (M * C_l - N * S_l)) +
      (M * S + N * C) * ((M_l * S + N_l * C) - (M * S_l + N * C_l))) =
    (C ^ 2 + S ^ 2) * (2 * (M * M_l + N * N_l)) -
      (M ^ 2 + N ^ 2) * (2 * (C * C_l + S * S_l)) := by
  ring

/-- **Universal Second Wronskian–Holomorphic-Product Triality Identity:**
`P W_im − Q W_re = W H_l − H W_l`. -/
theorem holomorphic_product_wronskian_im_cross_identity (M N C S M_l N_l C_l S_l : ℝ) :
    (M * C - N * S) * ((M_l * S + N_l * C) - (M * S_l + N * C_l)) -
      (M * S + N * C) * ((M_l * C - N_l * S) - (M * C_l - N * S_l)) =
    (M * S - N * C) * ((M * C_l + C * M_l) + (N * S_l + S * N_l)) -
      (M * C + N * S) * ((M * S_l + S * M_l) - (N * C_l + C * N_l)) := by
  ring

/-- **Universal Second Wronskian–Holomorphic-Product Modulus-Gradient Identity:**
`2 (P W_im − Q W_re) = −(V U_t − U V_t)`. -/
theorem holomorphic_product_wronskian_im_cross_eq_modulusSq_grad (M N C S M_l N_l C_l S_l : ℝ) :
    2 * ((M * C - N * S) * ((M_l * S + N_l * C) - (M * S_l + N * C_l)) -
      (M * S + N * C) * ((M_l * C - N_l * S) - (M * C_l - N * S_l))) =
    -((C ^ 2 + S ^ 2) * (2 * (M * (-N_l) + N * M_l)) -
      (M ^ 2 + N ^ 2) * (2 * (C * (-S_l) + S * C_l))) := by
  ring

/-- **Universal Horizontal Self-Wronskian Identity for `(H, W)`:**
`2 (H W_l − W H_l) = V U_t − U V_t`. -/
theorem hermitian_symplectic_selfWronskian_horiz_eq_modulusSq_vert_grad
    (M N C S M_l N_l C_l S_l : ℝ) :
    2 * ((M * C + N * S) * ((M * S_l + S * M_l) - (N * C_l + C * N_l)) -
      (M * S - N * C) * ((M * C_l + C * M_l) + (N * S_l + S * N_l))) =
    (C ^ 2 + S ^ 2) * (2 * (M * (-N_l) + N * M_l)) -
      (M ^ 2 + N ^ 2) * (2 * (C * (-S_l) + S * C_l)) := by
  ring

/-- **Universal Vertical Self-Wronskian Identity for `(H, W)`:**
`2 (H W_t − W H_t) = U V_l − V U_l`. -/
theorem hermitian_symplectic_selfWronskian_vert_eq_modulusSq_horiz_grad
    (M N C S M_l N_l C_l S_l : ℝ) :
    2 * ((M * C + N * S) * ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) -
      (M * S - N * C) * ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) =
    (M ^ 2 + N ^ 2) * (2 * (C * C_l + S * S_l)) -
      (C ^ 2 + S ^ 2) * (2 * (M * M_l + N * N_l)) := by
  ring

/-- **Universal Self-Wronskian Norm Squared Factorization for `(H, W)`:**
`(H W_l − W H_l)² + (H W_t − W H_t)² = (H² + W²)(W_re² + W_im²)`. -/
theorem hermitian_symplectic_selfWronskian_norm_sq_identity (M N C S M_l N_l C_l S_l : ℝ) :
    ((M * C + N * S) * ((M * S_l + S * M_l) - (N * C_l + C * N_l)) -
        (M * S - N * C) * ((M * C_l + C * M_l) + (N * S_l + S * N_l))) ^ 2 +
      ((M * C + N * S) * ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) -
        (M * S - N * C) * ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) ^ 2 =
    ((M * C + N * S) ^ 2 + (M * S - N * C) ^ 2) *
      (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Radial and Self-Wronskian Energy Split for `(H, W)`:**
`(H H_l + W W_l)² + (H H_t + W W_t)² + (H W_l − W H_l)² + (H W_t − W H_t)² =
  (H² + W²)((H_l² + H_t²) + (W_l² + W_t²))`. -/
theorem hermitian_symplectic_radial_selfWronskian_energy_split_identity
    (H W H_l H_t W_l W_t : ℝ) :
    (H * H_l + W * W_l) ^ 2 + (H * H_t + W * W_t) ^ 2 +
      (H * W_l - W * H_l) ^ 2 + (H * W_t - W * H_t) ^ 2 =
    (H ^ 2 + W ^ 2) * ((H_l ^ 2 + H_t ^ 2) + (W_l ^ 2 + W_t ^ 2)) := by
  ring

/-- **Universal Bochner–Hermitian Laplacian Norm Squared Factorization:**
`(4 (M_l C_l + N_l S_l))² + (4 (M_l S_l − N_l C_l))² = (4 (M_l² + N_l²))(4 (C_l² + S_l²))`. -/
theorem bochner_hermitian_symplectic_laplacian_norm_sq_identity (M_l N_l C_l S_l : ℝ) :
    (4 * (M_l * C_l + N_l * S_l)) ^ 2 + (4 * (M_l * S_l - N_l * C_l)) ^ 2 =
    (4 * (M_l ^ 2 + N_l ^ 2)) * (4 * (C_l ^ 2 + S_l ^ 2)) := by
  ring

/-- **Universal Hermitian–Symplectic Laplacian Dot Product Identity:**
`H (4 (M_l C_l + N_l S_l)) + W (4 (M_l S_l − N_l C_l)) = U_l V_l + U_t V_t`. -/
theorem hermitian_symplectic_laplacian_dot_eq_modulusSq_grad_dot (M N C S M_l N_l C_l S_l : ℝ) :
    (M * C + N * S) * (4 * (M_l * C_l + N_l * S_l)) +
      (M * S - N * C) * (4 * (M_l * S_l - N_l * C_l)) =
    (2 * (M * M_l + N * N_l)) * (2 * (C * C_l + S * S_l)) +
      (2 * (M * (-N_l) + N * M_l)) * (2 * (C * (-S_l) + S * C_l)) := by
  ring

/-- **Universal Hermitian–Symplectic Laplacian Symplectic Form Identity:**
`W (4 (M_l C_l + N_l S_l)) − H (4 (M_l S_l − N_l C_l)) = U_l V_t − U_t V_l`. -/
theorem hermitian_symplectic_laplacian_symplectic_eq_modulusSq_grad_det
    (M N C S M_l N_l C_l S_l : ℝ) :
    (M * S - N * C) * (4 * (M_l * C_l + N_l * S_l)) -
      (M * C + N * S) * (4 * (M_l * S_l - N_l * C_l)) =
    (2 * (M * M_l + N * N_l)) * (2 * (C * (-S_l) + S * C_l)) -
      (2 * (M * (-N_l) + N * M_l)) * (2 * (C * C_l + S * S_l)) := by
  ring

/-- **Universal Polarization Between Holomorphic-Product Derivative Norm Squared and Complex
Wronskian Norm Squared:**
`|F' G + F G'|² − |F' G − F G'|² = H (4 (M_l C_l + N_l S_l)) + W (4 (M_l S_l − N_l C_l))`. -/
theorem holomorphic_product_deriv_sub_wronskian_norm_sq_identity (M N C S M_l N_l C_l S_l : ℝ) :
    (((M_l * C - N_l * S) + (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) + (M * S_l + N * C_l)) ^ 2) -
      (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) =
    (M * C + N * S) * (4 * (M_l * C_l + N_l * S_l)) +
      (M * S - N * C) * (4 * (M_l * S_l - N_l * C_l)) := by
  ring

/-- **Universal Dirichlet-and-Laplacian Reconstruction of the Complex Wronskian Norm Squared:**
`((H_l² + H_t²) + (W_l² + W_t²)) − (H Δ H + W Δ W) = 2 (W_re² + W_im²)`. -/
theorem two_mul_wronskian_norm_sq_eq_dirichlet_sub_laplacian_dot (M N C S M_l N_l C_l S_l : ℝ) :
    ((((M * C_l + C * M_l) + (N * S_l + S * N_l)) ^ 2 +
        ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) ^ 2) +
      (((M * S_l + S * M_l) - (N * C_l + C * N_l)) ^ 2 +
        ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) ^ 2)) -
      ((M * C + N * S) * (4 * (M_l * C_l + N_l * S_l)) +
        (M * S - N * C) * (4 * (M_l * S_l - N_l * C_l))) =
    2 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
      ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Dirichlet-and-Laplacian Reconstruction of the Holomorphic Product Derivative
Norm Squared:**
`((H_l² + H_t²) + (W_l² + W_t²)) + (H Δ H + W Δ W) = 2 |F' G + F G'|²`. -/
theorem two_mul_holomorphic_product_deriv_norm_sq_eq_dirichlet_add_laplacian_dot
    (M N C S M_l N_l C_l S_l : ℝ) :
    ((((M * C_l + C * M_l) + (N * S_l + S * N_l)) ^ 2 +
        ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) ^ 2) +
      (((M * S_l + S * M_l) - (N * C_l + C * N_l)) ^ 2 +
        ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) ^ 2)) +
      ((M * C + N * S) * (4 * (M_l * C_l + N_l * S_l)) +
        (M * S - N * C) * (4 * (M_l * S_l - N_l * C_l))) =
    2 * (((M_l * C - N_l * S) + (M * C_l - N * S_l)) ^ 2 +
      ((M_l * S + N_l * C) + (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Horizontal Self-Wronskian Limit Theorem for `(H, W)`:**
`H₀ ∂_l^h W − W₀ ∂_l^h H → −(P₀ W_im − Q₀ W_re)` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_hermitian_symplectic_selfWronskian_horiz_nhdsWithin_zero
    {H_l W_l : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l)))) :
    Tendsto
      (fun h : ℝ =>
        (M * C + N * S) * ((W_l h - (M * S - N * C)) / h) -
          (M * S - N * C) * ((H_l h - (M * C + N * S)) / h))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-((M * C - N * S) * ((M_l * S + N_l * C) - (M * S_l + N * C_l)) -
          (M * S + N * C) * ((M_l * C - N_l * S) - (M * C_l - N * S_l))))) := by
  have hcomb := (hWl.const_mul (M * C + N * S)).sub (hHl.const_mul (M * S - N * C))
  have hid :
      (M * C + N * S) * ((M * S_l + S * M_l) - (N * C_l + C * N_l)) -
        (M * S - N * C) * ((M * C_l + C * M_l) + (N * S_l + S * N_l)) =
      -((M * C - N * S) * ((M_l * S + N_l * C) - (M * S_l + N * C_l)) -
        (M * S + N * C) * ((M_l * C - N_l * S) - (M * C_l - N * S_l))) := by
    ring
  rw [hid] at hcomb
  exact hcomb

/-- **Universal Vertical Self-Wronskian Limit Theorem for `(H, W)`:**
`H₀ ∂_τ^h W − W₀ ∂_τ^h H → −(P₀ W_re + Q₀ W_im)` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_hermitian_symplectic_selfWronskian_vert_nhdsWithin_zero
    {H_t W_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)))) :
    Tendsto
      (fun h : ℝ =>
        (M * C + N * S) * ((W_t h - (M * S - N * C)) / h) -
          (M * S - N * C) * ((H_t h - (M * C + N * S)) / h))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-((M * C - N * S) * ((M_l * C - N_l * S) - (M * C_l - N * S_l)) +
          (M * S + N * C) * ((M_l * S + N_l * C) - (M * S_l + N * C_l))))) := by
  have hcomb := (hWt.const_mul (M * C + N * S)).sub (hHt.const_mul (M * S - N * C))
  have hid :
      (M * C + N * S) * ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) -
        (M * S - N * C) * ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) =
      -((M * C - N * S) * ((M_l * C - N_l * S) - (M * C_l - N * S_l)) +
        (M * S + N * C) * ((M_l * S + N_l * C) - (M * S_l + N * C_l))) := by
    ring
  rw [hid] at hcomb
  exact hcomb

/-- **Universal Self-Wronskian Norm Squared Limit Theorem for `(H, W)`:**
`(H₀ ∂_l^h W − W₀ ∂_l^h H)² + (H₀ ∂_τ^h W − W₀ ∂_τ^h H)² → (H₀² + W₀²)(W_re² + W_im²)`. -/
theorem tendsto_hermitian_symplectic_selfWronskian_norm_sq_nhdsWithin_zero
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
        ((M * C + N * S) * ((W_l h - (M * S - N * C)) / h) -
            (M * S - N * C) * ((H_l h - (M * C + N * S)) / h)) ^ 2 +
          ((M * C + N * S) * ((W_t h - (M * S - N * C)) / h) -
            (M * S - N * C) * ((H_t h - (M * C + N * S)) / h)) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((M * C + N * S) ^ 2 + (M * S - N * C) ^ 2) *
          (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
            ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2))) := by
  have h1 := ((hWl.const_mul (M * C + N * S)).sub (hHl.const_mul (M * S - N * C))).pow 2
  have h2 := ((hWt.const_mul (M * C + N * S)).sub (hHt.const_mul (M * S - N * C))).pow 2
  have hcomb := h1.add h2
  rw [hermitian_symplectic_selfWronskian_norm_sq_identity M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Bochner–Hermitian Five-Point Laplacian Norm Squared Limit Theorem:**
`((Δ_5 H / h²)² + (Δ_5 W / h²)²) − (Δ_5 U / h²)(Δ_5 V / h²) → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_bochner_hermitian_symplectic_laplacian_norm_sq_nhdsWithin_zero
    {ΔH ΔW ΔU ΔV : ℝ → ℝ} {M_l N_l C_l S_l : ℝ}
    (hΔH : Tendsto (fun h : ℝ => ΔH h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l * C_l + N_l * S_l))))
    (hΔW : Tendsto (fun h : ℝ => ΔW h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l * S_l - N_l * C_l))))
    (hΔU : Tendsto (fun h : ℝ => ΔU h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l ^ 2 + N_l ^ 2))))
    (hΔV : Tendsto (fun h : ℝ => ΔV h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (C_l ^ 2 + S_l ^ 2)))) :
    Tendsto
      (fun h : ℝ =>
        ((ΔH h / h ^ 2) ^ 2 + (ΔW h / h ^ 2) ^ 2) -
          (ΔU h / h ^ 2) * (ΔV h / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hcomb := ((hΔH.pow 2).add (hΔW.pow 2)).sub (hΔU.mul hΔV)
  rw [bochner_hermitian_symplectic_laplacian_norm_sq_identity M_l N_l C_l S_l, sub_self] at hcomb
  exact hcomb

/-- **Universal Hermitian–Symplectic Laplacian vs. Modulus-Squared Gradient Dot-Product Limit Theorem:**
`(H₀ (Δ_5 H / h²) + W₀ (Δ_5 W / h²)) − ((∂_l^h U)(∂_l^h V) + (∂_τ^h U)(∂_τ^h V)) → 0`. -/
theorem tendsto_hermitian_symplectic_laplacian_dot_sub_modulusSq_grad_dot_nhdsWithin_zero
    {ΔH ΔW U_l U_t V_l V_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hΔH : Tendsto (fun h : ℝ => ΔH h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l * C_l + N_l * S_l))))
    (hΔW : Tendsto (fun h : ℝ => ΔW h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l * S_l - N_l * C_l))))
    (hUl : Tendsto (fun h : ℝ => (U_l h - (M ^ 2 + N ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l))))
    (hUt : Tendsto (fun h : ℝ => (U_t h - (M ^ 2 + N ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l))))
    (hVl : Tendsto (fun h : ℝ => (V_l h - (C ^ 2 + S ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (C * C_l + S * S_l))))
    (hVt : Tendsto (fun h : ℝ => (V_t h - (C ^ 2 + S ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        ((M * C + N * S) * (ΔH h / h ^ 2) + (M * S - N * C) * (ΔW h / h ^ 2)) -
          (((U_l h - (M ^ 2 + N ^ 2)) / h) * ((V_l h - (C ^ 2 + S ^ 2)) / h) +
            ((U_t h - (M ^ 2 + N ^ 2)) / h) * ((V_t h - (C ^ 2 + S ^ 2)) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hcomb :=
    ((hΔH.const_mul (M * C + N * S)).add (hΔW.const_mul (M * S - N * C))).sub
      ((hUl.mul hVl).add (hUt.mul hVt))
  rw [hermitian_symplectic_laplacian_dot_eq_modulusSq_grad_dot M N C S M_l N_l C_l S_l,
    sub_self] at hcomb
  exact hcomb

/-- **Universal Dirichlet-and-Laplacian Reconstruction Limit Theorem for `2 |W|²`:**
`(((∂_l^h H)² + (∂_τ^h H)²) + ((∂_l^h W)² + (∂_τ^h W)²)) − (H₀ (Δ_5 H / h²) + W₀ (Δ_5 W / h²)) →
  2 (W_re² + W_im²)` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_two_mul_wronskian_norm_sq_from_dirichlet_and_laplacian_nhdsWithin_zero
    {H_l H_t W_l W_t ΔH ΔW : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))))
    (hΔH : Tendsto (fun h : ℝ => ΔH h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l * C_l + N_l * S_l))))
    (hΔW : Tendsto (fun h : ℝ => ΔW h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l * S_l - N_l * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        ((((H_l h - (M * C + N * S)) / h) ^ 2 + ((H_t h - (M * C + N * S)) / h) ^ 2) +
          (((W_l h - (M * S - N * C)) / h) ^ 2 + ((W_t h - (M * S - N * C)) / h) ^ 2)) -
        ((M * C + N * S) * (ΔH h / h ^ 2) + (M * S - N * C) * (ΔW h / h ^ 2)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
          ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2))) := by
  have hdir :=
    (((hHl.pow 2).add (hHt.pow 2)).add ((hWl.pow 2).add (hWt.pow 2)))
  have hlap := (hΔH.const_mul (M * C + N * S)).add (hΔW.const_mul (M * S - N * C))
  have hcomb := hdir.sub hlap
  rw [two_mul_wronskian_norm_sq_eq_dirichlet_sub_laplacian_dot M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-! ## Section 2: Global Hermitian–Symplectic Self-Wronskian Calculus and Wronskian–Holomorphic-Product Triality for `(H_k, W_k)` Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`) -/

/-- **Full-Strip Horizontal Self-Wronskian Triality Law for `(H_k, W_k)` (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`H_k ∂_l^h W_k − W_k ∂_l^h H_k → −(P_k W_{k,\mathrm{im}} − Q_k W_{k,\mathrm{re}})` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_hermitianWronskian_selfWronskian_horiz_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
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
          ((((∫ x in Ioi (0 : ℝ),
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
          ((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-(((∫ x in Ioi (0 : ℝ),
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
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
            (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) -
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
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
            (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))))) :=
  tendsto_hermitian_symplectic_selfWronskian_horiz_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip Vertical Self-Wronskian Triality Law for `(H_k, W_k)` (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`H_k ∂_τ^h W_k − W_k ∂_τ^h H_k → −(P_k W_{k,\mathrm{re}} + Q_k W_{k,\mathrm{im}})` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_hermitianWronskian_selfWronskian_vert_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) -
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-(((∫ x in Ioi (0 : ℝ),
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
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
            (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) +
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
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
            (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))))) :=
  tendsto_hermitian_symplectic_selfWronskian_vert_nhdsWithin_zero
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip Self-Wronskian Norm Squared Factorization for `(H_k, W_k)` (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`(H_k ∂_l^h W_k − W_k ∂_l^h H_k)² + (H_k ∂_τ^h W_k − W_k ∂_τ^h H_k)² →
  (H_k² + W_k²)(W_{k,\mathrm{re}}² + W_{k,\mathrm{im}}²)` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_hermitianWronskian_selfWronskian_norm_sq_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
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
            ((((∫ x in Ioi (0 : ℝ),
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
            ((((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) ^ 2 +
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
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) -
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
        ((((∫ x in Ioi (0 : ℝ),
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
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) ^ 2 +
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
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) ^ 2) *
          ((((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) ^ 2 +
            (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) ^ 2))) :=
  tendsto_hermitian_symplectic_selfWronskian_norm_sq_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)

/-! ## Section 3: Global Bochner–Hermitian Five-Point Laplacian Norm Factorization and Laplacian–Dirichlet Reconstruction of the Holomorphic Wronskian Norm Squared Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`) -/

/-- **Full-Strip Bochner–Hermitian Five-Point Laplacian Norm Squared Factorization for `(H_k, W_k)`
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`((Δ_5 H_k / h²)² + (Δ_5 W_k / h²)²) − (Δ_5 |F_k|² / h²)(Δ_5 |Δ_k|² / h²) → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_bochner_hermitianWronskian_laplacian_norm_sq_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((((∫ x in Ioi (0 : ℝ),
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2) ^ 2 +
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
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2) ^ 2) -
        ((((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2) *
          ((((((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              ((((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_bochner_hermitian_symplectic_laplacian_norm_sq_nhdsWithin_zero
    (tendsto_div_sq_hermitianPairing_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_sectorWronskian_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_complexModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_imbalanceModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ)

/-- **Full-Strip Dirichlet-and-Laplacian Reconstruction of `2 |F_k' Δ_k − F_k Δ_k'|²`
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`(((∂_l^h H_k)² + (∂_τ^h H_k)²) + ((∂_l^h W_k)² + (∂_τ^h W_k)²)) −
  (H_k (Δ_5 H_k / h²) + W_k (Δ_5 W_k / h²)) → 2 (W_{k,\mathrm{re}}² + W_{k,\mathrm{im}}²)`. -/
theorem tendsto_two_mul_holomorphicWronskian_norm_sq_from_dirichlet_and_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) ^ 2)) -
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2) +
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
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) ^ 2 +
            (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) ^ 2))) :=
  tendsto_two_mul_wronskian_norm_sq_from_dirichlet_and_laplacian_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sq_hermitianPairing_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_sectorWronskian_fivePoint_laplacian_nhds_zero hk hν hl τ)

/-! ## Section 4: Critical-Line (`l = 0`) Identical Discrete Five-Point Laplacian Vanishing of `H_k`, Critical-Line Bochner–Hermitian Wronskian Identity, and Master Witness Theorem -/

/-- **Odd Horizontal Reflection Antisymmetry `l ↦ −l` of the Hermitian Pairing
`H_k(l, τ) = M_k(l, τ) Δ_k^{\cos}(l, τ) + N_k(l, τ) Δ_k^{\sin}(l, τ)` (`k ≥ 1`, `l, τ ∈ ℝ`).** -/
theorem hermitianPairing_neg_left
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
    (∫ x in Ioi (0 : ℝ),
        x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
    -((∫ x in Ioi (0 : ℝ),
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
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  rw [setIntegral_Ioi_rpow_neg_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector hk ν l τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_cos_log hk ν l τ,
    setIntegral_Ioi_rpow_neg_mul_sin_log_eq_neg hk ν l τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_sin_log hk ν l τ]
  ring

/-- **Critical-Line (`l = 0`) Identical Vanishing of the Hermitian Pairing `H_k(0, τ) = 0`
(`k ≥ 1`, `τ ∈ ℝ`).** -/
theorem hermitianPairing_at_criticalLine_eq_zero
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
    (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0 := by
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  have hΔc0 := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_cos_log hk ν τ
  rw [hl0] at hΔc0
  rw [hΔc0, setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk ν τ]
  ring

/-- **Critical-Line (`l = 0`) Identical Finite-Step Five-Point Discrete Laplacian Vanishing of
`H_k` (`k ≥ 1`, `τ, h ∈ ℝ`):**
For every step size `h ∈ ℝ`, the five-point discrete Laplacian of `H_k` at `(0, τ)` vanishes
identically:
`(H_k(h, τ) + H_k(−h, τ) − 2 H_k(0, τ)) + (H_k(0, τ + h) + H_k(0, τ − h) − 2 H_k(0, τ)) = 0`. -/
theorem hermitianPairing_fivePoint_laplacian_at_criticalLine_eq_zero
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ h : ℝ) :
    (((∫ x in Ioi (0 : ℝ),
            x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
            x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
      ((∫ x in Ioi (0 : ℝ),
            x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
            x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
      2 * ((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
    (((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
      ((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
      2 * ((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) = 0 := by
  rw [hermitianPairing_neg_left hk ν h τ,
    hermitianPairing_at_criticalLine_eq_zero hk ν τ,
    hermitianPairing_at_criticalLine_eq_zero hk ν (τ + h),
    hermitianPairing_at_criticalLine_eq_zero hk ν (τ - h)]
  ring

/-- **Critical-Line (`l = 0`) Bochner–Hermitian Wronskian Laplacian Identity (`k ≥ 2`, `τ ∈ ℝ`):**
On the critical line `l = 0`,
`((Δ_5 W_k(0, τ; h) / h²)² − (Δ_5 |F_k|²(0, τ; h) / h²)(Δ_5 |Δ_k|²(0, τ; h) / h²)) → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_sectorWronskian_laplacian_sq_sub_modulusSq_laplacian_mul_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (0 : ℝ),
                    x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                (∫ x in Ioi (0 : ℝ),
                    x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
              ((∫ x in Ioi (0 : ℝ),
                    x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                (∫ x in Ioi (0 : ℝ),
                    x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              2 * ((∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                (∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
            (((∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                (∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
              ((∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                (∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
              2 * ((∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                (∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2) ^ 2 -
        ((((((∫ x in Ioi (0 : ℝ),
                    x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                ((∫ x in Ioi (0 : ℝ),
                    x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * ((∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              (((∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                ((∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * ((∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2) *
          ((((((∫ x in Ioi (1 : ℝ),
                      x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * (((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              ((((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * (((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hk1 : 1 ≤ k := by omega
  have h := tendsto_bochner_hermitianWronskian_laplacian_norm_sq_nhds_zero
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
  refine h.congr (fun h' => ?_)
  have hh_pos : (0 : ℝ) + h' - 1 / 2 = h' - 1 / 2 := by ring
  have hh_neg : (0 : ℝ) - h' - 1 / 2 = -h' - 1 / 2 := by ring
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  rw [hh_pos, hh_neg, hl0,
    hermitianPairing_fivePoint_laplacian_at_criticalLine_eq_zero hk1 ν τ h']
  ring

/-- **Master Witness Theorem for Bochner–Hermitian Five-Point Laplacian Norm Factorization,
Hermitian–Symplectic Self-Wronskian Triality, and Critical-Line Discrete Laplacian Vanishing:**
There exists an explicit symmetric non-zero finite arc measure `ν` on `ArcParam` such that for all
`k ≥ 2`:
1. Across `|l| < 1/8` and `τ ∈ ℝ`, the five-point discrete Laplacians of `(H_k, W_k)` satisfy the
   Bochner–Hermitian norm factorization
   `((Δ_5 H_k / h²)² + (Δ_5 W_k / h²)²) − (Δ_5 |F_k|² / h²)(Δ_5 |Δ_k|² / h²) → 0`;
2. Across `|l| < 1/8` and `τ ∈ ℝ`, the self-Wronskian norm squared of `(H_k, W_k)` converges to
   `(|F_k|² |Δ_k|²)(W_{k,\mathrm{re}}² + W_{k,\mathrm{im}}²)`;
3. On the critical line `l = 0`, the finite-step five-point discrete Laplacian of `H_k` vanishes
   identically for every step size `h ∈ ℝ`. -/
theorem exists_dyadic_bochnerHermitianLaplacian_wronskianTriality_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              ((((((∫ x in Ioi (0 : ℝ),
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
                              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2) ^ 2 +
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
                              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))) / h ^ 2) ^ 2) -
              ((((((∫ x in Ioi (0 : ℝ),
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
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2) *
                ((((((∫ x in Ioi (1 : ℝ),
                            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                      (((∫ x in Ioi (1 : ℝ),
                            x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                            x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      2 * (((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                    ((((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                      (((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      2 * (((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        ((∫ x in Ioi (1 : ℝ),
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                          ∫ x in Ioc (0 : ℝ) 1,
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2)))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) ∧
        (∀ τ h : ℝ,
          (((∫ x in Ioi (0 : ℝ),
                  x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) +
          (((∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) = 0) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  refine ⟨fun l hl τ => tendsto_bochner_hermitianWronskian_laplacian_norm_sq_nhds_zero hk hν hl τ,
    fun τ h => hermitianPairing_fivePoint_laplacian_at_criticalLine_eq_zero hk1 ν τ h⟩

end

end RHTower
