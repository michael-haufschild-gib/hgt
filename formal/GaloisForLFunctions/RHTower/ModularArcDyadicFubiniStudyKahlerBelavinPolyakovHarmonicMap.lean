/-
Copyright (c) 2026 Michael. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GaloisForLFunctions.RHTower.ModularArcDyadicHopfBlochMinkowskiConformalSphericalJacobian

/-!
# Fubini–Study Kähler Potential Curvature, Dual `Z`-Gradient Complement, Minkowski Position–Laplacian Pairing, and Belavin–Polyakov `S²` Harmonic Map Calculus for the Dyadic Mellin Tower

In `ModularArcDyadicHopfBlochMinkowskiConformalSphericalJacobian`, we lifted the two holomorphic
dyadic Mellin components
* `F_k(l, τ) = M_k(l, τ) + i N_k(l, τ)` (the full-strip complex oscillatory Mellin transform) and
* `Δ_k(l, τ) = Δ_k^{\cos}(l, τ) + i Δ_k^{\sin}(l, τ)` (the origin–infinity complex Mellin imbalance)

to the 4D Minkowski–Hopf–Bloch null-cone vector `(2 H_k, 2 W_k, Z_k, R_k) ∈ ℝ^{3,1}` where
`Z_k = |F_k|² − |Δ_k|²` and `R_k = |F_k|² + |Δ_k|²`.

In this file we develop the **second-order (Laplacian / Fubini–Study Kähler / Belavin–Polyakov `S²`
nonlinear `σ`-model)** geometry of `(2 H_k, 2 W_k, Z_k, R_k)`:

1. **Universal Fubini–Study Kähler Potential Curvature, Dual `Z`-Gradient Complement, Minkowski
   Position–Laplacian Pairing, and Belavin–Polyakov `S²` Harmonic Map Calculus (Section 1):**
   * **Fubini–Study Kähler Potential Curvature Identity for `R = |F|² + |G|²`:**
     For a single holomorphic function `F`, Liouville–Gauss logarithmic harmonicity states that
     `|F|² Δ(|F|²) − |∇(|F|²)|² = 0`. For the sum of two squared holomorphic moduli
     `R = |F|² + |G|²` (whose logarithm `log R` is the Fubini–Study Kähler potential of the
     projective curve `[F : G] : ℂ → ℂℙ¹`), the division-free logarithmic Laplacian equals **four
     times the complex Wronskian norm squared**:
     `R ΔR − (R_l² + R_t²) = 4 (W_re² + W_im²) ≥ 0`
     (`fubini_study_kahler_potential_laplacian_identity`,
      `fubini_study_kahler_potential_laplacian_nonneg`).
   * **Dual `Z`-Gradient Kähler Complement Identity for `Z = |F|² − |G|²`:**
     Replacing `|∇R|²` by `|∇Z|²` replaces the complex Wronskian `W = F' G − F G'` by the
     holomorphic product derivative `(F G)' = F' G + F G' = P_l + i Q_l`:
     `R ΔR − (Z_l² + Z_t²) = 4 (P_l² + Q_l²) ≥ 0`
     (`hopf_bloch_z_gradient_kahler_complement_identity`,
      `hopf_bloch_z_gradient_kahler_complement_nonneg`).
   * **Minkowski and Dual Position–Laplacian Pairing Identities:**
     `R ΔR − Z ΔZ − 4 (H ΔH + W ΔW) = 8 (W_re² + W_im²) ≥ 0`
     (`hopf_bloch_minkowski_position_laplacian_wronskian_identity`),
     `R ΔR − Z ΔZ + 4 (H ΔH + W ΔW) = 8 (P_l² + Q_l²) ≥ 0`
     (`hopf_bloch_dual_position_laplacian_holomorphic_product_identity`),
     `Z ΔR − R ΔZ = 8 (H_l W_t − H_t W_l)`
     (`hopf_bloch_zr_laplacian_det_eq_eight_mul_jacobian`), and
     `(Z ΔR − R ΔZ)² + 16 (H ΔW − W ΔH)² = 64 (P_l² + Q_l²)(W_re² + W_im²)`
     (`hopf_bloch_position_laplacian_quadruple_norm_identity`).
   * **Belavin–Polyakov 3D Linear Harmonic-Transport System and `S²` Nonlinear `σ`-Model Equation:**
     For the 3D Bloch vector `X = (2 H, 2 W, Z)` with radius `R = |X|`,
     `R ΔX + (ΔR) X = 2 (R_l ∂_l X + R_t ∂_τ X)`
     (`belavin_polyakov_harmonic_transport_horiz`, `belavin_polyakov_harmonic_transport_vert`,
      `belavin_polyakov_harmonic_transport_z`), and consequently `n = X / R ∈ S²` satisfies the
     division-free Belavin–Polyakov `S²` harmonic map equation
     `R (R ΔX − (ΔR) X) − 2 R (R_l ∂_l X + R_t ∂_τ X) + 2 (R_l² + R_t²) X = −8 (W_re² + W_im²) X`
     (`belavin_polyakov_nlsm_harmonic_map_horiz`, `belavin_polyakov_nlsm_harmonic_map_vert`,
      `belavin_polyakov_nlsm_harmonic_map_z`).
   * **Projective Tangent Frame `(D_l X, D_τ X) = (R ∂_l X − R_l X, R ∂_τ X − R_t X)` Isometry and
     Cross-Product Closure:**
     `|D_l X|² = |D_τ X|² = 4 R² (W_re² + W_im²)`, `D_l X · D_τ X = 0`, and
     `D_l X × D_τ X = 4 R (W_re² + W_im²) X`
     (`projective_tangent_horiz_norm_sq`, `projective_tangent_vert_norm_sq`,
      `projective_tangent_orthogonality`, `projective_tangent_cross_first`,
      `projective_tangent_cross_second`, `projective_tangent_cross_third`).
   * **Universal Limit Theorems:**
     Limit theorems for the five-point Laplacians of `Z` and `R`, the Fubini–Study Kähler potential
     curvature, the dual `Z`-gradient complement, the Minkowski position–Laplacian pairing, and the
     3D Belavin–Polyakov harmonic-transport system.

2. **Full-Strip (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`) Five-Point Laplacians of `Z_k` and `R_k`,
   Fubini–Study Kähler Potential Curvature, and Dual `Z`-Gradient Complement (Section 2):**
   * `tendsto_div_sq_hopfBlochZ_fivePoint_laplacian_nhds_zero`
   * `tendsto_div_sq_hopfBlochR_fivePoint_laplacian_nhds_zero`
   * `tendsto_fubiniStudy_kahler_potential_laplacian_nhds_zero`
   * `tendsto_hopfBloch_z_gradient_kahler_complement_nhds_zero`

3. **Full-Strip (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`) Minkowski Position–Laplacian Wronskian Pairing and
   Belavin–Polyakov 3D Harmonic-Transport System (Section 3):**
   * `tendsto_hopfBloch_minkowski_position_laplacian_wronskian_nhds_zero`
   * `tendsto_belavinPolyakov_harmonic_transport_horiz_nhds_zero`
   * `tendsto_belavinPolyakov_harmonic_transport_vert_nhds_zero`
   * `tendsto_belavinPolyakov_harmonic_transport_z_nhds_zero`

4. **Critical-Line (`l = 0`) Five-Point Laplacians of `Z_k` and `R_k`, 1D Vertical Fubini–Study
   Kähler Curvature, and Master Witness Theorem (Section 4):**
   * `tendsto_div_sq_hopfBlochR_fivePoint_laplacian_at_criticalLine_nhds_zero`
   * `tendsto_fubiniStudy_kahler_potential_laplacian_at_criticalLine_nhds_zero`
   * `exists_dyadic_fubiniStudyKahler_belavinPolyakovHarmonicMap_arcWitness`
-/

open MeasureTheory Set Filter Topology BigOperators

namespace RHTower

noncomputable section

/-! ## Section 1: Universal Fubini–Study Kähler Potential Curvature, Dual `Z`-Gradient Complement, Minkowski Position–Laplacian Pairing, and Belavin–Polyakov `S²` Harmonic Map Calculus -/

/-- **Universal Fubini–Study Kähler Potential Curvature Identity for `R = |F|² + |G|²`:**
For any `M, N, C, S, M_l, N_l, C_l, S_l ∈ ℝ`, with `R = (M² + N²) + (C² + S²)`,
`ΔR = 4 ((M_l² + N_l²) + (C_l² + S_l²))`, `R_l = 2 (M M_l + N N_l) + 2 (C C_l + S S_l)`, and
`R_t = 2 (M (−N_l) + N M_l) + 2 (C (−S_l) + S C_l)`, the division-free logarithmic Laplacian of `R`
equals four times the complex Wronskian norm squared:
`R ΔR − (R_l² + R_t²) = 4 (W_re² + W_im²)`. -/
theorem fubini_study_kahler_potential_laplacian_identity (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) -
      ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) ^ 2 +
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) ^ 2) =
    4 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
      ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Global Non-Negativity of the Fubini–Study Kähler Potential Curvature (`|∇R|² ≤ R ΔR`):** -/
theorem fubini_study_kahler_potential_laplacian_nonneg (M N C S M_l N_l C_l S_l : ℝ) :
    (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) ^ 2 +
      (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) ^ 2 ≤
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) := by
  rw [← sub_nonneg, fubini_study_kahler_potential_laplacian_identity]
  positivity

/-- **Universal Dual `Z`-Gradient Kähler Complement Identity for `Z = |F|² − |G|²`:**
Replacing `|∇R|²` by `|∇Z|²` in `R ΔR` replaces the complex Wronskian norm squared by the
holomorphic product derivative norm squared `P_l² + Q_l²`:
`R ΔR − (Z_l² + Z_t²) = 4 (P_l² + Q_l²)`. -/
theorem hopf_bloch_z_gradient_kahler_complement_identity (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) -
      ((2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) ^ 2 +
        (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) ^ 2) =
    4 * (((M_l * C - N_l * S) + (M * C_l - N * S_l)) ^ 2 +
      ((M_l * S + N_l * C) + (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Global Non-Negativity of the Dual `Z`-Gradient Kähler Complement (`|∇Z|² ≤ R ΔR`):** -/
theorem hopf_bloch_z_gradient_kahler_complement_nonneg (M N C S M_l N_l C_l S_l : ℝ) :
    (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) ^ 2 +
      (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) ^ 2 ≤
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) := by
  rw [← sub_nonneg, hopf_bloch_z_gradient_kahler_complement_identity]
  positivity

/-- **Universal `R` vs. `Z` Gradient-Norm Difference Identity:**
`(|∇R|² − |∇Z|²) = 4 ((P_l² + Q_l²) − (W_re² + W_im²))`. -/
theorem hopf_bloch_r_z_gradient_norm_diff_identity (M N C S M_l N_l C_l S_l : ℝ) :
    ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) ^ 2 +
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) ^ 2) -
      ((2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) ^ 2 +
        (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) ^ 2) =
    4 * ((((M_l * C - N_l * S) + (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) + (M * S_l + N * C_l)) ^ 2) -
      (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2)) := by
  ring

/-- **Universal Minkowski Position–Laplacian Wronskian Pairing Identity:**
The Minkowski inner product `R ΔR − Z ΔZ − 4 (H ΔH + W ΔW)` of `(2H, 2W, Z, R)` with its Laplacian
`(2 ΔH, 2 ΔW, ΔZ, ΔR)` equals `8 (W_re² + W_im²) ≥ 0`:
`R ΔR − Z ΔZ − 4 (H ΔH + W ΔW) = 8 (W_re² + W_im²)`. -/
theorem hopf_bloch_minkowski_position_laplacian_wronskian_identity
    (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) -
      ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) - (C_l ^ 2 + S_l ^ 2))) -
      4 * ((M * C + N * S) * (4 * (M_l * C_l + N_l * S_l)) +
        (M * S - N * C) * (4 * (M_l * S_l - N_l * C_l))) =
    8 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
      ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Dual Position–Laplacian Holomorphic-Product Pairing Identity:**
`R ΔR − Z ΔZ + 4 (H ΔH + W ΔW) = 8 (P_l² + Q_l²) ≥ 0`. -/
theorem hopf_bloch_dual_position_laplacian_holomorphic_product_identity
    (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) -
      ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) - (C_l ^ 2 + S_l ^ 2))) +
      4 * ((M * C + N * S) * (4 * (M_l * C_l + N_l * S_l)) +
        (M * S - N * C) * (4 * (M_l * S_l - N_l * C_l))) =
    8 * (((M_l * C - N_l * S) + (M * C_l - N * S_l)) ^ 2 +
      ((M_l * S + N_l * C) + (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal `(Z, R)` Position–Laplacian `2 × 2` Determinant vs. `(H, W)` Jacobian Identity:**
`Z ΔR − R ΔZ = 8 (H_l W_t − H_t W_l)`. -/
theorem hopf_bloch_zr_laplacian_det_eq_eight_mul_jacobian
    (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) -
      ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) - (C_l ^ 2 + S_l ^ 2))) =
    8 * (((M * C_l + C * M_l) + (N * S_l + S * N_l)) *
          ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) -
        ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) *
          ((M * S_l + S * M_l) - (N * C_l + C * N_l))) := by
  ring

/-- **Universal Position–Laplacian Quadruple Norm Factorization:**
`(Z ΔR − R ΔZ)² + 16 (H ΔW − W ΔH)² = 64 (P_l² + Q_l²)(W_re² + W_im²)`. -/
theorem hopf_bloch_position_laplacian_quadruple_norm_identity
    (M N C S M_l N_l C_l S_l : ℝ) :
    (((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) -
        ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) - (C_l ^ 2 + S_l ^ 2)))) ^ 2 +
      16 * ((M * C + N * S) * (4 * (M_l * S_l - N_l * C_l)) -
        (M * S - N * C) * (4 * (M_l * C_l + N_l * S_l))) ^ 2 =
    64 * (((M_l * C - N_l * S) + (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) + (M * S_l + N * C_l)) ^ 2) *
      (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Belavin–Polyakov 3D Linear Harmonic-Transport Law (First Component `H`):**
`R ΔH + (ΔR) H = 2 (R_l H_l + R_t H_t)`. -/
theorem belavin_polyakov_harmonic_transport_horiz (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * (M_l * C_l + N_l * S_l)) +
      (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) * (M * C + N * S) =
    2 * ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) *
          ((M * C_l + C * M_l) + (N * S_l + S * N_l)) +
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) *
          ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) := by
  ring

/-- **Universal Belavin–Polyakov 3D Linear Harmonic-Transport Law (Second Component `W`):**
`R ΔW + (ΔR) W = 2 (R_l W_l + R_t W_t)`. -/
theorem belavin_polyakov_harmonic_transport_vert (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * (M_l * S_l - N_l * C_l)) +
      (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) * (M * S - N * C) =
    2 * ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) *
          ((M * S_l + S * M_l) - (N * C_l + C * N_l)) +
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) *
          ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))) := by
  ring

/-- **Universal Belavin–Polyakov 3D Linear Harmonic-Transport Law (Third Component `Z`):**
`R ΔZ + (ΔR) Z = 2 (R_l Z_l + R_t Z_t)`. -/
theorem belavin_polyakov_harmonic_transport_z (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) - (C_l ^ 2 + S_l ^ 2))) +
      (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) * ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) =
    2 * ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) *
          (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) +
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) *
          (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l))) := by
  ring

/-- **Universal Division-Free Belavin–Polyakov `S²` Harmonic Map (NLSM) Equation (First Component `H`):**
For the unit Bloch vector `n = X / R`, the numerator `R³ Δn_1` equals `−8 (W_re² + W_im²) H`:
`R (R ΔH − (ΔR) H) − 2 R (R_l H_l + R_t H_t) + 2 (R_l² + R_t²) H = −8 (W_re² + W_im²) H`. -/
theorem belavin_polyakov_nlsm_harmonic_map_horiz (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * (M_l * C_l + N_l * S_l)) -
          (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) * (M * C + N * S)) -
      2 * ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) *
            ((M * C_l + C * M_l) + (N * S_l + S * N_l)) +
          (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) *
            ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) +
      2 * ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) ^ 2 +
          (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) ^ 2) *
        (M * C + N * S) =
    -8 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
      ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) * (M * C + N * S) := by
  ring

/-- **Universal Division-Free Belavin–Polyakov `S²` Harmonic Map (NLSM) Equation (Second Component `W`):**
`R (R ΔW − (ΔR) W) − 2 R (R_l W_l + R_t W_t) + 2 (R_l² + R_t²) W = −8 (W_re² + W_im²) W`. -/
theorem belavin_polyakov_nlsm_harmonic_map_vert (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * (M_l * S_l - N_l * C_l)) -
          (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) * (M * S - N * C)) -
      2 * ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) *
            ((M * S_l + S * M_l) - (N * C_l + C * N_l)) +
          (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) *
            ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))) +
      2 * ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) ^ 2 +
          (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) ^ 2) *
        (M * S - N * C) =
    -8 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
      ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) * (M * S - N * C) := by
  ring

/-- **Universal Division-Free Belavin–Polyakov `S²` Harmonic Map (NLSM) Equation (Third Component `Z`):**
`R (R ΔZ − (ΔR) Z) − 2 R (R_l Z_l + R_t Z_t) + 2 (R_l² + R_t²) Z = −8 (W_re² + W_im²) Z`. -/
theorem belavin_polyakov_nlsm_harmonic_map_z (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (4 * ((M_l ^ 2 + N_l ^ 2) - (C_l ^ 2 + S_l ^ 2))) -
          (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))) * ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) -
      2 * ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) *
            (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) +
          (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) *
            (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l))) +
      2 * ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) ^ 2 +
          (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) ^ 2) *
        ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) =
    -8 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
      ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) *
        ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) := by
  ring

/-- **Projective Tangent Frame Horizontal Norm-Squared Factorization:**
For `D_l X = R ∂_l X − R_l X`, `|D_l X|² = 4 R² (W_re² + W_im²)`. -/
theorem projective_tangent_horiz_norm_sq (M N C S M_l N_l C_l S_l : ℝ) :
    (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * C_l + C * M_l) + (N * S_l + S * N_l))) -
        (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) * (2 * (M * C + N * S))) ^ 2 +
      (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * S_l + S * M_l) - (N * C_l + C * N_l))) -
        (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) * (2 * (M * S - N * C))) ^ 2 +
      (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) -
        (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) * ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) ^ 2 =
    4 * ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) ^ 2 *
      (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Projective Tangent Frame Vertical Norm-Squared Factorization:**
For `D_τ X = R ∂_τ X − R_t X`, `|D_τ X|² = 4 R² (W_re² + W_im²)`. -/
theorem projective_tangent_vert_norm_sq (M N C S M_l N_l C_l S_l : ℝ) :
    (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) -
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) * (2 * (M * C + N * S))) ^ 2 +
      (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))) -
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) * (2 * (M * S - N * C))) ^ 2 +
      (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) -
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) * ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) ^ 2 =
    4 * ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) ^ 2 *
      (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Projective Tangent Frame Orthogonality (`D_l X · D_τ X = 0`):** -/
theorem projective_tangent_orthogonality (M N C S M_l N_l C_l S_l : ℝ) :
    (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * C_l + C * M_l) + (N * S_l + S * N_l))) -
        (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) * (2 * (M * C + N * S))) *
      (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) -
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) * (2 * (M * C + N * S))) +
    (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * S_l + S * M_l) - (N * C_l + C * N_l))) -
        (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) * (2 * (M * S - N * C))) *
      (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))) -
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) * (2 * (M * S - N * C))) +
    (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) -
        (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) * ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) *
      (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) -
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) * ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) = 0 := by
  ring

/-- **Projective Tangent Frame Cross-Product Closure (Third Component `(D_l X × D_τ X)_3 = 4 R |W|² Z`):** -/
theorem projective_tangent_cross_third (M N C S M_l N_l C_l S_l : ℝ) :
    (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * C_l + C * M_l) + (N * S_l + S * N_l))) -
        (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) * (2 * (M * C + N * S))) *
      (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))) -
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) * (2 * (M * S - N * C))) -
    (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * S_l + S * M_l) - (N * C_l + C * N_l))) -
        (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) * (2 * (M * S - N * C))) *
      (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (2 * ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) -
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) * (2 * (M * C + N * S))) =
    4 * ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
      (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) *
      ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) := by
  ring

/-- **Universal Five-Point Laplacian Limit Theorem for `Z = U − V`:**
If `Δ_5 U / h² → 4 (M_l² + N_l²)` and `Δ_5 V / h² → 4 (C_l² + S_l²)`, then
`(Δ_5 U − Δ_5 V) / h² → 4 ((M_l² + N_l²) − (C_l² + S_l²))`. -/
theorem tendsto_div_sq_hopf_bloch_z_fivePoint_laplacian_nhdsWithin_zero
    {ΔU ΔV : ℝ → ℝ} {M_l N_l C_l S_l : ℝ}
    (hΔU : Tendsto (fun h : ℝ => ΔU h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l ^ 2 + N_l ^ 2))))
    (hΔV : Tendsto (fun h : ℝ => ΔV h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (C_l ^ 2 + S_l ^ 2)))) :
    Tendsto
      (fun h : ℝ => (ΔU h - ΔV h) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (4 * ((M_l ^ 2 + N_l ^ 2) - (C_l ^ 2 + S_l ^ 2)))) := by
  have hcomb := hΔU.sub hΔV
  have hid : 4 * (M_l ^ 2 + N_l ^ 2) - 4 * (C_l ^ 2 + S_l ^ 2) =
      4 * ((M_l ^ 2 + N_l ^ 2) - (C_l ^ 2 + S_l ^ 2)) := by ring
  rw [hid] at hcomb
  refine hcomb.congr (fun h => ?_)
  ring

/-- **Universal Five-Point Laplacian Limit Theorem for `R = U + V`:**
If `Δ_5 U / h² → 4 (M_l² + N_l²)` and `Δ_5 V / h² → 4 (C_l² + S_l²)`, then
`(Δ_5 U + Δ_5 V) / h² → 4 ((M_l² + N_l²) + (C_l² + S_l²))`. -/
theorem tendsto_div_sq_hopf_bloch_r_fivePoint_laplacian_nhdsWithin_zero
    {ΔU ΔV : ℝ → ℝ} {M_l N_l C_l S_l : ℝ}
    (hΔU : Tendsto (fun h : ℝ => ΔU h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l ^ 2 + N_l ^ 2))))
    (hΔV : Tendsto (fun h : ℝ => ΔV h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (C_l ^ 2 + S_l ^ 2)))) :
    Tendsto
      (fun h : ℝ => (ΔU h + ΔV h) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2)))) := by
  have hcomb := hΔU.add hΔV
  have hid : 4 * (M_l ^ 2 + N_l ^ 2) + 4 * (C_l ^ 2 + S_l ^ 2) =
      4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2)) := by ring
  rw [hid] at hcomb
  refine hcomb.congr (fun h => ?_)
  ring

/-- **Universal Fubini–Study Kähler Potential Curvature Limit Theorem:**
`R₀ (Δ_5 R / h²) − ((∂_l^h R)² + (∂_τ^h R)²) → 4 (W_re² + W_im²)`. -/
theorem tendsto_fubini_study_kahler_potential_laplacian_nhdsWithin_zero
    {ΔR R_l R_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hΔR : Tendsto (fun h : ℝ => ΔR h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2)))))
    (hRl : Tendsto (fun h : ℝ => (R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l))))
    (hRt : Tendsto (fun h : ℝ => (R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (ΔR h / h ^ 2) -
          (((R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) ^ 2 +
            ((R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
          ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2))) := by
  have hcomb :=
    (hΔR.const_mul ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))).sub ((hRl.pow 2).add (hRt.pow 2))
  rw [fubini_study_kahler_potential_laplacian_identity M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Dual `Z`-Gradient Kähler Complement Limit Theorem:**
`R₀ (Δ_5 R / h²) − ((∂_l^h Z)² + (∂_τ^h Z)²) → 4 (P_l² + Q_l²)`. -/
theorem tendsto_hopf_bloch_z_gradient_kahler_complement_nhdsWithin_zero
    {ΔR Z_l Z_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hΔR : Tendsto (fun h : ℝ => ΔR h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2)))))
    (hZl : Tendsto (fun h : ℝ => (Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l))))
    (hZt : Tendsto (fun h : ℝ => (Z_t h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (ΔR h / h ^ 2) -
          (((Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) ^ 2 +
            ((Z_t h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * (((M_l * C - N_l * S) + (M * C_l - N * S_l)) ^ 2 +
          ((M_l * S + N_l * C) + (M * S_l + N * C_l)) ^ 2))) := by
  have hcomb :=
    (hΔR.const_mul ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))).sub ((hZl.pow 2).add (hZt.pow 2))
  rw [hopf_bloch_z_gradient_kahler_complement_identity M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Minkowski Position–Laplacian Wronskian Pairing Limit Theorem:**
`R₀ (Δ_5 R / h²) − Z₀ (Δ_5 Z / h²) − 4 (H₀ (Δ_5 H / h²) + W₀ (Δ_5 W / h²)) → 8 (W_re² + W_im²)`. -/
theorem tendsto_hopf_bloch_minkowski_position_laplacian_wronskian_nhdsWithin_zero
    {ΔH ΔW ΔZ ΔR : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hΔH : Tendsto (fun h : ℝ => ΔH h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l * C_l + N_l * S_l))))
    (hΔW : Tendsto (fun h : ℝ => ΔW h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l * S_l - N_l * C_l))))
    (hΔZ : Tendsto (fun h : ℝ => ΔZ h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * ((M_l ^ 2 + N_l ^ 2) - (C_l ^ 2 + S_l ^ 2)))))
    (hΔR : Tendsto (fun h : ℝ => ΔR h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2))))) :
    Tendsto
      (fun h : ℝ =>
        ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (ΔR h / h ^ 2) -
          ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) * (ΔZ h / h ^ 2) -
          4 * ((M * C + N * S) * (ΔH h / h ^ 2) + (M * S - N * C) * (ΔW h / h ^ 2)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (8 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
          ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2))) := by
  have hcomb :=
    ((hΔR.const_mul ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))).sub
      (hΔZ.const_mul ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)))).sub
      (((hΔH.const_mul (M * C + N * S)).add (hΔW.const_mul (M * S - N * C))).const_mul 4)
  rw [hopf_bloch_minkowski_position_laplacian_wronskian_identity M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Belavin–Polyakov 3D Linear Harmonic-Transport Limit Theorem (First Component `H`):**
`(R₀ (Δ_5 H / h²) + (Δ_5 R / h²) H₀) − 2 ((∂_l^h R)(∂_l^h H) + (∂_τ^h R)(∂_τ^h H)) → 0`. -/
theorem tendsto_belavin_polyakov_harmonic_transport_horiz_nhdsWithin_zero
    {ΔH ΔR H_l H_t R_l R_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hΔH : Tendsto (fun h : ℝ => ΔH h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l * C_l + N_l * S_l))))
    (hΔR : Tendsto (fun h : ℝ => ΔR h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2)))))
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hRl : Tendsto (fun h : ℝ => (R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l))))
    (hRt : Tendsto (fun h : ℝ => (R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (ΔH h / h ^ 2) +
            (ΔR h / h ^ 2) * (M * C + N * S)) -
          2 * (((R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) *
                ((H_l h - (M * C + N * S)) / h) +
              ((R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) *
                ((H_t h - (M * C + N * S)) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hcomb :=
    ((hΔH.const_mul ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))).add
      (hΔR.mul_const (M * C + N * S))).sub
      (((hRl.mul hHl).add (hRt.mul hHt)).const_mul 2)
  rw [belavin_polyakov_harmonic_transport_horiz M N C S M_l N_l C_l S_l, sub_self] at hcomb
  exact hcomb

/-- **Universal Belavin–Polyakov 3D Linear Harmonic-Transport Limit Theorem (Second Component `W`):**
`(R₀ (Δ_5 W / h²) + (Δ_5 R / h²) W₀) − 2 ((∂_l^h R)(∂_l^h W) + (∂_τ^h R)(∂_τ^h W)) → 0`. -/
theorem tendsto_belavin_polyakov_harmonic_transport_vert_nhdsWithin_zero
    {ΔW ΔR W_l W_t R_l R_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hΔW : Tendsto (fun h : ℝ => ΔW h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (M_l * S_l - N_l * C_l))))
    (hΔR : Tendsto (fun h : ℝ => ΔR h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2)))))
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))))
    (hRl : Tendsto (fun h : ℝ => (R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l))))
    (hRt : Tendsto (fun h : ℝ => (R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (ΔW h / h ^ 2) +
            (ΔR h / h ^ 2) * (M * S - N * C)) -
          2 * (((R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) *
                ((W_l h - (M * S - N * C)) / h) +
              ((R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) *
                ((W_t h - (M * S - N * C)) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hcomb :=
    ((hΔW.const_mul ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))).add
      (hΔR.mul_const (M * S - N * C))).sub
      (((hRl.mul hWl).add (hRt.mul hWt)).const_mul 2)
  rw [belavin_polyakov_harmonic_transport_vert M N C S M_l N_l C_l S_l, sub_self] at hcomb
  exact hcomb

/-- **Universal Belavin–Polyakov 3D Linear Harmonic-Transport Limit Theorem (Third Component `Z`):**
`(R₀ (Δ_5 Z / h²) + (Δ_5 R / h²) Z₀) − 2 ((∂_l^h R)(∂_l^h Z) + (∂_τ^h R)(∂_τ^h Z)) → 0`. -/
theorem tendsto_belavin_polyakov_harmonic_transport_z_nhdsWithin_zero
    {ΔZ ΔR Z_l Z_t R_l R_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hΔZ : Tendsto (fun h : ℝ => ΔZ h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * ((M_l ^ 2 + N_l ^ 2) - (C_l ^ 2 + S_l ^ 2)))))
    (hΔR : Tendsto (fun h : ℝ => ΔR h / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * ((M_l ^ 2 + N_l ^ 2) + (C_l ^ 2 + S_l ^ 2)))))
    (hZl : Tendsto (fun h : ℝ => (Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l))))
    (hZt : Tendsto (fun h : ℝ => (Z_t h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l))))
    (hRl : Tendsto (fun h : ℝ => (R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l))))
    (hRt : Tendsto (fun h : ℝ => (R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * (ΔZ h / h ^ 2) +
            (ΔR h / h ^ 2) * ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) -
          2 * (((R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) *
                ((Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) +
              ((R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) *
                ((Z_t h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hcomb :=
    ((hΔZ.const_mul ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))).add
      (hΔR.mul_const ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)))).sub
      (((hRl.mul hZl).add (hRt.mul hZt)).const_mul 2)
  rw [belavin_polyakov_harmonic_transport_z M N C S M_l N_l C_l S_l, sub_self] at hcomb
  exact hcomb

/-! ## Section 2: Full-Strip (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`) Five-Point Laplacians of `Z_k` and `R_k`, Fubini–Study Kähler Potential Curvature, and Dual `Z`-Gradient Complement -/

/-- **Full-Strip Five-Point Laplacian of `Z_k(l, τ) = |F_k(l, τ)|² − |Δ_k(l, τ)|²`
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`(Δ_5 |F_k|² − Δ_5 |Δ_k|²) / h² → 4 (|F_k'(l, τ)|² − |Δ_k'(l, τ)|²)`. -/
theorem tendsto_div_sq_hopfBlochZ_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) -
            (((((∫ x in Ioi (1 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) -
          ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)))) :=
  tendsto_div_sq_hopf_bloch_z_fivePoint_laplacian_nhdsWithin_zero
    (tendsto_div_sq_complexModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_imbalanceModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ)

/-- **Full-Strip Five-Point Laplacian of `R_k(l, τ) = |F_k(l, τ)|² + |Δ_k(l, τ)|²`
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`(Δ_5 |F_k|² + Δ_5 |Δ_k|²) / h² → 4 (|F_k'(l, τ)|² + |Δ_k'(l, τ)|²)`. -/
theorem tendsto_div_sq_hopfBlochR_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
            (((((∫ x in Ioi (1 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) +
          ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)))) :=
  tendsto_div_sq_hopf_bloch_r_fivePoint_laplacian_nhdsWithin_zero
    (tendsto_div_sq_complexModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_imbalanceModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ)

/-- **Full-Strip Fubini–Study Kähler Potential Curvature Limit Theorem for `R_k(l, τ)`
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`R_k (Δ_5 R_k / h²) − ((∂_l^h R_k)² + (∂_τ^h R_k)²) → 4 (W_{k,\mathrm{re}}² + W_{k,\mathrm{im}}²) ≥ 0`. -/
theorem tendsto_fubiniStudy_kahler_potential_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
              (((((∫ x in Ioi (1 : ℝ),
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2) -
          ((((((∫ x in Ioi (0 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                  (((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
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
  tendsto_fubini_study_kahler_potential_laplacian_nhdsWithin_zero
    (tendsto_div_sq_hopfBlochR_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_vert_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip Dual `Z`-Gradient Kähler Complement Limit Theorem for `R_k(l, τ)` and `Z_k(l, τ)`
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`R_k (Δ_5 R_k / h²) − ((∂_l^h Z_k)² + (∂_τ^h Z_k)²) → 4 ((∂_l P_k)² + (∂_l Q_k)²) ≥ 0`. -/
theorem tendsto_hopfBloch_z_gradient_kahler_complement_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
              (((((∫ x in Ioi (1 : ℝ),
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2) -
          ((((((∫ x in Ioi (0 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
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
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                  (((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
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
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
            ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) ^ 2))) :=
  tendsto_hopf_bloch_z_gradient_kahler_complement_nhdsWithin_zero
    (tendsto_div_sq_hopfBlochR_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_vert_shift_nhds_zero hk hν hl τ)

/-! ## Section 3: Full-Strip (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`) Minkowski Position–Laplacian Wronskian Pairing and Belavin–Polyakov 3D Harmonic-Transport System -/

/-- **Full-Strip Minkowski Position–Laplacian Wronskian Pairing Limit Theorem
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`R_k (Δ_5 R_k / h²) − Z_k (Δ_5 Z_k / h²) − 4 (H_k (Δ_5 H_k / h²) + W_k (Δ_5 W_k / h²)) →
  8 (W_{k,\mathrm{re}}² + W_{k,\mathrm{im}}²) ≥ 0`. -/
theorem tendsto_hopfBloch_minkowski_position_laplacian_wronskian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
              (((((∫ x in Ioi (1 : ℝ),
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2) -
          (((∫ x in Ioi (0 : ℝ),
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
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) *
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) -
              (((((∫ x in Ioi (1 : ℝ),
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2) -
          4 * (((∫ x in Ioi (0 : ℝ),
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
        (8 * ((((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
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
  tendsto_hopf_bloch_minkowski_position_laplacian_wronskian_nhdsWithin_zero
    (tendsto_div_sq_hermitianPairing_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_sectorWronskian_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_hopfBlochZ_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_hopfBlochR_fivePoint_laplacian_nhds_zero hk hν hl τ)

/-- **Full-Strip Belavin–Polyakov 3D Linear Harmonic-Transport Limit Theorem (First Component `H_k`)
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`(R_k (Δ_5 H_k / h²) + (Δ_5 R_k / h²) H_k) − 2 ((∂_l^h R_k)(∂_l^h H_k) + (∂_τ^h R_k)(∂_τ^h H_k)) → 0`. -/
theorem tendsto_belavinPolyakov_harmonic_transport_horiz_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) *
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
                (((((∫ x in Ioi (1 : ℝ),
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
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2) *
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) -
          2 * ((((((∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                    (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) *
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
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) +
              (((((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                    (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) *
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
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_belavin_polyakov_harmonic_transport_horiz_nhdsWithin_zero
    (tendsto_div_sq_hermitianPairing_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_hopfBlochR_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_vert_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip Belavin–Polyakov 3D Linear Harmonic-Transport Limit Theorem (Third Component `Z_k`)
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`(R_k (Δ_5 Z_k / h²) + (Δ_5 R_k / h²) Z_k) − 2 ((∂_l^h R_k)(∂_l^h Z_k) + (∂_τ^h R_k)(∂_τ^h Z_k)) → 0`. -/
theorem tendsto_belavinPolyakov_harmonic_transport_z_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) -
                (((((∫ x in Ioi (1 : ℝ),
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
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2) +
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
                (((((∫ x in Ioi (1 : ℝ),
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
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2) *
              (((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) -
          2 * ((((((∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                    (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) *
                (((((∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                    (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) +
              (((((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                    (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) *
                (((((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                    (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_belavin_polyakov_harmonic_transport_z_nhdsWithin_zero
    (tendsto_div_sq_hopfBlochZ_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_hopfBlochR_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_vert_shift_nhds_zero hk hν hl τ)

/-! ## Section 4: Critical-Line (`l = 0`) Five-Point Laplacians of `Z_k` and `R_k`, 1D Vertical Fubini–Study Kähler Curvature, and Master Witness Theorem -/

/-- **Critical-Line (`l = 0`) Five-Point Laplacian of `R_k(0, τ)` (`τ ∈ ℝ`, `k ≥ 2`):**
On the critical line `l = 0`, the five-point Laplacian of `R_k` divided by `h²` converges to
`4 ((∫_ℝ v sin(τv) Φ_k(v) dv)² + (∫_{v > 0} 2 v cos(τv) Φ_k(v) dv)²) ≥ 0`. -/
theorem tendsto_div_sq_hopfBlochR_fivePoint_laplacian_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (0 : ℝ),
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
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
            (((((∫ x in Ioi (1 : ℝ),
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
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v in Ioi (0 : ℝ), 2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  have h := tendsto_div_sq_hopfBlochR_fivePoint_laplacian_nhds_zero
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
  have hsinh0 :
      (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall (fun v => ?_))
    dsimp only
    rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
    rfl
  have hcosh0 :
      (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    dsimp only
    rw [zero_mul, Real.cosh_zero, mul_one]
  have hcosh_Ioi :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v in Ioi (0 : ℝ),
        2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    refine setIntegral_congr_ae measurableSet_Ioi (Filter.Eventually.of_forall (fun v _ => ?_))
    rw [zero_mul, Real.cosh_zero, mul_one]
  have hsinh_Ioi :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero (fun v _ => ?_)
    rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
  have hlim :
      4 * (((∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) +
        ((∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) =
      4 * ((∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
        (∫ v in Ioi (0 : ℝ), 2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    rw [hsinh0, hcosh0, hcosh_Ioi, hsinh_Ioi]
    ring
  rw [hlim] at h
  refine h.congr (fun h' => ?_)
  have hh_pos : (0 : ℝ) + h' - 1 / 2 = h' - 1 / 2 := by ring
  have hh_neg : (0 : ℝ) - h' - 1 / 2 = -h' - 1 / 2 := by ring
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  rw [hh_pos, hh_neg, hl0]

/-- **Master Witness Theorem for Fubini–Study Kähler Potential Curvature, Dual `Z`-Gradient
Complement, Minkowski Position–Laplacian Wronskian Pairing, and Belavin–Polyakov `S²` Harmonic-Transport System:**
There exists an explicit symmetric non-zero finite arc measure `ν` on `ArcParam` such that for all
`k ≥ 2`:
1. Across `|l| < 1/8` and `τ ∈ ℝ`, the five-point Laplacian of the third Hopf–Bloch coordinate
   `Z_k(l, τ) = |F_k(l, τ)|² − |G_k(l, τ)|²` divided by `h²` converges to
   `4 ((∂_l F_k)² + (∂_τ F_k)² − (∂_l G_k)² − (∂_τ G_k)²)`;
2. On the critical line `l = 0`, the five-point Laplacian of the Fubini–Study radius
   `R_k(0, τ) = |F_k(0, τ)|² + |G_k(0, τ)|²` divided by `h²` converges to
   `4 ((∫_ℝ v sin(τv) Φ_k(v) dv)² + (∫_{v > 0} 2 v cos(τv) Φ_k(v) dv)²) ≥ 0`. -/
theorem exists_dyadic_fubiniStudyKahler_belavinPolyakovHarmonicMap_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              (((((∫ x in Ioi (0 : ℝ),
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
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) -
                  (((((∫ x in Ioi (1 : ℝ),
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
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              (4 * (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                  (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) -
                ((∫ v in Ioi (0 : ℝ),
                    2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))))) ∧
        (∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              (((((∫ x in Ioi (0 : ℝ),
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
                          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
                  (((((∫ x in Ioi (1 : ℝ),
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
                            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              (4 * ((∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                (∫ v in Ioi (0 : ℝ), 2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)))) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk =>
    ⟨fun l hl τ => tendsto_div_sq_hopfBlochZ_fivePoint_laplacian_nhds_zero hk hν hl τ,
     fun τ => tendsto_div_sq_hopfBlochR_fivePoint_laplacian_at_criticalLine_nhds_zero hk hν τ⟩⟩

end

end RHTower
