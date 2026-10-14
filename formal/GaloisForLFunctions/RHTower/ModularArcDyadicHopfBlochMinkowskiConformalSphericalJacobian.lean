import GaloisForLFunctions.RHTower.ModularArcDyadicHolomorphicProductDerivativeJacobianLaplacianDuality

/-!
# Hopf–Bloch Minkowski Null-Cone Lift, Division-Free Belavin–Polyakov Spherical Cauchy–Riemann System, Conformal Isometry Laws, and 3D Fubini–Study Spherical Jacobian for the Infinite-Horizon Dyadic Tower

This module establishes the **4D Minkowski–Hopf–Bloch Null-Cone Calculus, Division-Free
Belavin–Polyakov Spherical Cauchy–Riemann System, Minkowski Conformal Isometry Laws, and
Globally Non-Negative 3D Fubini–Study Spherical Jacobian** for the infinite-horizon dyadic
oscillatory Mellin transform `F_k(l, τ) = (M_k(l, τ), N_k(l, τ))` and origin–infinity complex
Mellin imbalance `Δ_k(l, τ) = (Δ_k^{\cos}(l, τ), Δ_k^{\sin}(l, τ))` across `|l| < 1/8, τ ∈ ℝ`
(`k ≥ 2`).

For any two holomorphic pairs `F = (M, N)` and `G = (C, S)`, define the four real
Minkowski–Hopf–Bloch coordinates:
* `H = M C + N S` (Hermitian sector imbalance),
* `W = M S − N C` (symplectic sector Wronskian),
* `Z = (M² + N²) − (C² + S²)` (vertical Bloch coordinate `4 Re(conj(F⁺) F⁻)`),
* `R = (M² + N²) + (C² + S²)` (total Minkowski radius `2 (|F⁺|² + |F⁻|²)`),

together with the complex Wronskian `W_re + i W_im = F' G − F G'` and holomorphic product
derivative `P_l + i Q_l = F' G + F G'`.

## Main Results

1. **Universal 4D Minkowski–Hopf–Bloch Null-Cone, Belavin–Polyakov Spherical Cauchy–Riemann,
   Conformal Isometry, and 3D Fubini–Study Spherical Jacobian Calculus (Section 1):**
   * `hopf_bloch_minkowski_null_cone_identity` &
     `hopf_bloch_minkowski_laplacian_null_cone_identity`:
     `4 (H² + W²) + Z² = R²` and `4 ((ΔH)² + (ΔW)²) + (ΔZ)² = (ΔR)²`.
   * `hopf_bloch_minkowski_radial_orthogonality_horiz` &
     `hopf_bloch_minkowski_radial_orthogonality_vert`:
     `4 (H H_l + W W_l) + Z Z_l = R R_l` and `4 (H H_t + W W_t) + Z Z_t = R R_t`.
   * `belavin_polyakov_spherical_cr_horiz_first`,
     `belavin_polyakov_spherical_cr_horiz_second`,
     `belavin_polyakov_spherical_cr_horiz_third`,
     `belavin_polyakov_spherical_cr_vert_first`,
     `belavin_polyakov_spherical_cr_vert_second`, and
     `belavin_polyakov_spherical_cr_vert_third`:
     Complete 6-equation division-free Belavin–Polyakov spherical Cauchy–Riemann system
     `X × ∂_l X = R ∂_τ X − (∂_τ R) X` and `X × ∂_τ X = −(R ∂_l X − (∂_l R) X)` for
     `X = (2 H, 2 W, Z)`:
     `W Z_l − Z W_l = R H_t − R_t H`, `Z H_l − H Z_l = R W_t − R_t W`,
     `4 (H W_l − W H_l) = R Z_t − R_t Z`, `W Z_t − Z W_t = R_l H − R H_l`,
     `Z H_t − H Z_t = R_l W − R W_l`, `4 (H W_t − W H_t) = R_l Z − R Z_l`.
   * `hopf_bloch_minkowski_conformal_horiz_eq_wronskian_norm_sq`,
     `hopf_bloch_minkowski_conformal_vert_eq_wronskian_norm_sq`, and
     `hopf_bloch_minkowski_conformal_orthogonality`:
     Exact Minkowski conformal isometry laws
     `4 (H_l² + W_l²) + Z_l² − R_l² = 4 (H_t² + W_t²) + Z_t² − R_t² = 4 (W_re² + W_im²) ≥ 0`
     and `4 (H_l H_t + W_l W_t) + Z_l Z_t − R_l R_t = 0`.
   * `hopf_bloch_minkowski_dual_dirichlet_eq_holomorphic_product_deriv_norm_sq` &
     `hopf_bloch_minkowski_laplacian_defect_eq_wronskian_norm_sq`:
     `4 (|∇H|² + |∇W|²) + |∇R|² − |∇Z|² = 8 (P_l² + Q_l²)` and
     `R ΔR − (4 (H ΔH + W ΔW) + Z ΔZ) = 8 (W_re² + W_im²)`.
   * `hopf_bloch_spherical_jacobian_det_eq_radius_mul_wronskian_norm_sq`:
     Globally non-negative 3D Fubini–Study spherical Jacobian determinant
     `H (W_l Z_t − W_t Z_l) + W (Z_l H_t − Z_t H_l) + Z (H_l W_t − H_t W_l) = R (W_re² + W_im²) ≥ 0`.
   * Universal limit theorems for `Z`, `R`, the Belavin–Polyakov spherical Cauchy–Riemann
     system, the Minkowski conformal isometry laws, and the 3D Fubini–Study spherical Jacobian.

2. **Full-Strip First-Order Partial Derivatives of `(Z_k, R_k)` and Belavin–Polyakov Spherical
   Cauchy–Riemann System Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`) (Section 2):**
   * `tendsto_div_hopfBlochZ_horiz_shift_nhds_zero`,
     `tendsto_div_hopfBlochZ_vert_shift_nhds_zero`,
     `tendsto_div_hopfBlochR_horiz_shift_nhds_zero`, and
     `tendsto_div_hopfBlochR_vert_shift_nhds_zero`:
     First-order horizontal and vertical partial derivatives of `Z_k = |F_k|² − |Δ_k|²` and
     `R_k = |F_k|² + |Δ_k|²`.
   * `tendsto_belavinPolyakov_spherical_cr_horiz_first_nhds_zero` &
     `tendsto_belavinPolyakov_spherical_cr_horiz_second_nhds_zero`:
     Full-strip division-free Belavin–Polyakov spherical Cauchy–Riemann equations for
     `(H_k, W_k, Z_k, R_k)`.

3. **Full-Strip Minkowski Conformal Isometry Laws and 3D Fubini–Study Spherical Jacobian Across
   `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`) (Section 3):**
   * `tendsto_hopfBloch_minkowski_conformal_horiz_nhds_zero`,
     `tendsto_hopfBloch_minkowski_conformal_vert_nhds_zero`,
     `tendsto_hopfBloch_minkowski_conformal_orthogonality_nhds_zero`, and
     `tendsto_hopfBloch_spherical_jacobian_det_nhds_zero`:
     Full-strip Minkowski horizontal and vertical conformal energy laws, Minkowski tangent
     orthogonality, and 3D Fubini–Study spherical Jacobian factorization.

4. **Critical-Line (`l = 0`) Even Reflection Symmetry and Horizontal Stationarity of `(Z_k, R_k)`
   (Section 4):**
   * `hopfBlochZ_neg_left` & `hopfBlochR_neg_left`:
     `Z_k(−l, τ) = Z_k(l, τ)` and `R_k(−l, τ) = R_k(l, τ)`.
   * `tendsto_div_hopfBlochZ_horiz_shift_at_criticalLine_nhds_zero` &
     `tendsto_div_hopfBlochR_horiz_shift_at_criticalLine_nhds_zero`:
     `∂_l Z_k(0, τ) = 0` and `∂_l R_k(0, τ) = 0`.
   * `exists_dyadic_hopfBloch_minkowskiConformal_sphericalJacobian_arcWitness`:
     Master witness theorem.
-/

open MeasureTheory Set Filter Topology BigOperators

namespace RHTower

noncomputable section

/-! ## Section 1: Universal 4D Minkowski–Hopf–Bloch Null-Cone Calculus, Belavin–Polyakov Spherical Cauchy–Riemann System, Conformal Isometry Laws, and 3D Fubini–Study Spherical Jacobian -/

/-- **Universal Minkowski–Hopf–Bloch Null-Cone Identity in Function Space:**
`4 (H² + W²) + Z² = R²`, where `H = M C + N S`, `W = M S − N C`,
`Z = (M² + N²) − (C² + S²)`, and `R = (M² + N²) + (C² + S²)`. -/
theorem hopf_bloch_minkowski_null_cone_identity
    (M N C S : ℝ) :
    4 * ((M * C + N * S) ^ 2 + (M * S - N * C) ^ 2) +
      ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) ^ 2 =
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) ^ 2 := by
  ring

/-- **Universal Minkowski–Hopf–Bloch Null-Cone Identity in Laplacian Space:**
`4 ((ΔH)² + (ΔW)²) + (ΔZ)² = (ΔR)²`, where `ΔH = 4 (M_l C_l + N_l S_l)`,
`ΔW = 4 (M_l S_l − N_l C_l)`, `ΔZ = 4 (M_l² + N_l²) − 4 (C_l² + S_l²)`, and
`ΔR = 4 (M_l² + N_l²) + 4 (C_l² + S_l²)`. -/
theorem hopf_bloch_minkowski_laplacian_null_cone_identity
    (M_l N_l C_l S_l : ℝ) :
    4 * ((4 * (M_l * C_l + N_l * S_l)) ^ 2 + (4 * (M_l * S_l - N_l * C_l)) ^ 2) +
      (4 * (M_l ^ 2 + N_l ^ 2) - 4 * (C_l ^ 2 + S_l ^ 2)) ^ 2 =
    (4 * (M_l ^ 2 + N_l ^ 2) + 4 * (C_l ^ 2 + S_l ^ 2)) ^ 2 := by
  ring

/-- **Universal Horizontal Minkowski Radial Orthogonality:**
`4 (H H_l + W W_l) + Z Z_l = R R_l`. -/
theorem hopf_bloch_minkowski_radial_orthogonality_horiz
    (M N C S M_l N_l C_l S_l : ℝ) :
    4 * ((M * C + N * S) * ((M * C_l + C * M_l) + (N * S_l + S * N_l)) +
        (M * S - N * C) * ((M * S_l + S * M_l) - (N * C_l + C * N_l))) +
      ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) *
        (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) =
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
      (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) := by
  ring

/-- **Universal Vertical Minkowski Radial Orthogonality (under Cauchy–Riemann):**
`4 (H H_t + W W_t) + Z Z_t = R R_t`. -/
theorem hopf_bloch_minkowski_radial_orthogonality_vert
    (M N C S M_l N_l C_l S_l : ℝ) :
    4 * ((M * C + N * S) * ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) +
        (M * S - N * C) * ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))) +
      ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) *
        (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) =
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
      (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) := by
  ring

/-- **Universal Division-Free Belavin–Polyakov Spherical Cauchy–Riemann Equation (Horizontal,
First Component):**
`W Z_l − Z W_l = R H_t − R_t H`. -/
theorem belavin_polyakov_spherical_cr_horiz_first
    (M N C S M_l N_l C_l S_l : ℝ) :
    (M * S - N * C) * (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) -
      ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) *
        ((M * S_l + S * M_l) - (N * C_l + C * N_l)) =
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) -
      (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) *
        (M * C + N * S) := by
  ring

/-- **Universal Division-Free Belavin–Polyakov Spherical Cauchy–Riemann Equation (Horizontal,
Second Component):**
`Z H_l − H Z_l = R W_t − R_t W`. -/
theorem belavin_polyakov_spherical_cr_horiz_second
    (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) *
        ((M * C_l + C * M_l) + (N * S_l + S * N_l)) -
      (M * C + N * S) * (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) =
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) -
      (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) *
        (M * S - N * C) := by
  ring

/-- **Universal Division-Free Belavin–Polyakov Spherical Cauchy–Riemann Equation (Horizontal,
Third Component):**
`4 (H W_l − W H_l) = R Z_t − R_t Z`. -/
theorem belavin_polyakov_spherical_cr_horiz_third
    (M N C S M_l N_l C_l S_l : ℝ) :
    4 * ((M * C + N * S) * ((M * S_l + S * M_l) - (N * C_l + C * N_l)) -
        (M * S - N * C) * ((M * C_l + C * M_l) + (N * S_l + S * N_l))) =
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) -
      (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) *
        ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) := by
  ring

/-- **Universal Division-Free Belavin–Polyakov Spherical Cauchy–Riemann Equation (Vertical,
First Component):**
`W Z_t − Z W_t = R_l H − R H_l`. -/
theorem belavin_polyakov_spherical_cr_vert_first
    (M N C S M_l N_l C_l S_l : ℝ) :
    (M * S - N * C) * (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) -
      ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) *
        ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) =
    (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) * (M * C + N * S) -
      ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        ((M * C_l + C * M_l) + (N * S_l + S * N_l)) := by
  ring

/-- **Universal Division-Free Belavin–Polyakov Spherical Cauchy–Riemann Equation (Vertical,
Second Component):**
`Z H_t − H Z_t = R_l W − R W_l`. -/
theorem belavin_polyakov_spherical_cr_vert_second
    (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) *
        ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) -
      (M * C + N * S) * (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) =
    (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) * (M * S - N * C) -
      ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        ((M * S_l + S * M_l) - (N * C_l + C * N_l)) := by
  ring

/-- **Universal Division-Free Belavin–Polyakov Spherical Cauchy–Riemann Equation (Vertical,
Third Component):**
`4 (H W_t − W H_t) = R_l Z − R Z_l`. -/
theorem belavin_polyakov_spherical_cr_vert_third
    (M N C S M_l N_l C_l S_l : ℝ) :
    4 * ((M * C + N * S) * ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) -
        (M * S - N * C) * ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))) =
    (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) *
        ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) -
      ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) := by
  ring

/-- **Universal Minkowski Horizontal Conformal Energy Law:**
`4 (H_l² + W_l²) + Z_l² − R_l² = 4 (W_re² + W_im²)`. -/
theorem hopf_bloch_minkowski_conformal_horiz_eq_wronskian_norm_sq
    (M N C S M_l N_l C_l S_l : ℝ) :
    4 * (((M * C_l + C * M_l) + (N * S_l + S * N_l)) ^ 2 +
        ((M * S_l + S * M_l) - (N * C_l + C * N_l)) ^ 2) +
      (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) ^ 2 -
      (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) ^ 2 =
    4 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Minkowski Vertical Conformal Energy Law (under Cauchy–Riemann):**
`4 (H_t² + W_t²) + Z_t² − R_t² = 4 (W_re² + W_im²)`. -/
theorem hopf_bloch_minkowski_conformal_vert_eq_wronskian_norm_sq
    (M N C S M_l N_l C_l S_l : ℝ) :
    4 * (((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) ^ 2 +
        ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) ^ 2) +
      (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) ^ 2 -
      (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) ^ 2 =
    4 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Minkowski Conformal Orthogonality Law:**
`4 (H_l H_t + W_l W_t) + Z_l Z_t − R_l R_t = 0`. -/
theorem hopf_bloch_minkowski_conformal_orthogonality
    (M N C S M_l N_l C_l S_l : ℝ) :
    4 * (((M * C_l + C * M_l) + (N * S_l + S * N_l)) *
          ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) +
        ((M * S_l + S * M_l) - (N * C_l + C * N_l)) *
          ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))) +
      (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) *
        (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) -
      (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) *
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) = 0 := by
  ring

/-- **Universal Dual Minkowski Dirichlet Energy for the Holomorphic Product Derivative:**
`4 (H_l² + H_t² + W_l² + W_t²) + (R_l² + R_t²) − (Z_l² + Z_t²) = 8 (P_l² + Q_l²)`. -/
theorem hopf_bloch_minkowski_dual_dirichlet_eq_holomorphic_product_deriv_norm_sq
    (M N C S M_l N_l C_l S_l : ℝ) :
    4 * (((M * C_l + C * M_l) + (N * S_l + S * N_l)) ^ 2 +
        ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) ^ 2 +
        ((M * S_l + S * M_l) - (N * C_l + C * N_l)) ^ 2 +
        ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) ^ 2) +
      ((2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)) ^ 2 +
        (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)) ^ 2) -
      ((2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) ^ 2 +
        (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) ^ 2) =
    8 * (((M_l * C - N_l * S) + (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) + (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Minkowski Laplacian Defect Identity:**
`R ΔR − (4 (H ΔH + W ΔW) + Z ΔZ) = 8 (W_re² + W_im²)`. -/
theorem hopf_bloch_minkowski_laplacian_defect_eq_wronskian_norm_sq
    (M N C S M_l N_l C_l S_l : ℝ) :
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
        (4 * (M_l ^ 2 + N_l ^ 2) + 4 * (C_l ^ 2 + S_l ^ 2)) -
      (4 * ((M * C + N * S) * (4 * (M_l * C_l + N_l * S_l)) +
          (M * S - N * C) * (4 * (M_l * S_l - N_l * C_l))) +
        ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) *
          (4 * (M_l ^ 2 + N_l ^ 2) - 4 * (C_l ^ 2 + S_l ^ 2))) =
    8 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal 3D Fubini–Study Spherical Jacobian Determinant Identity:**
`H (W_l Z_t − W_t Z_l) + W (Z_l H_t − Z_t H_l) + Z (H_l W_t − H_t W_l) = R (W_re² + W_im²)`. -/
theorem hopf_bloch_spherical_jacobian_det_eq_radius_mul_wronskian_norm_sq
    (M N C S M_l N_l C_l S_l : ℝ) :
    (M * C + N * S) *
        (((M * S_l + S * M_l) - (N * C_l + C * N_l)) *
            (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) -
          ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) *
            (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l))) +
      (M * S - N * C) *
        ((2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l)) *
            ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) -
          (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)) *
            ((M * C_l + C * M_l) + (N * S_l + S * N_l))) +
      ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) *
        (((M * C_l + C * M_l) + (N * S_l + S * N_l)) *
            ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l)) -
          ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l)) *
            ((M * S_l + S * M_l) - (N * C_l + C * N_l))) =
    ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
      (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
        ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2) := by
  ring

/-- **Universal Difference-Quotient Limit for `Z = F − G`:** -/
theorem tendsto_div_hopf_bloch_z_nhdsWithin_zero
    {F_f G_f : ℝ → ℝ} {F₀ G₀ F_d G_d : ℝ}
    (hF : Tendsto (fun h : ℝ => (F_f h - F₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds F_d))
    (hG : Tendsto (fun h : ℝ => (G_f h - G₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds G_d)) :
    Tendsto
      (fun h : ℝ => ((F_f h - G_f h) - (F₀ - G₀)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (F_d - G_d)) :=
  (hF.sub hG).congr (fun _ => by ring)

/-- **Universal Difference-Quotient Limit for `R = F + G`:** -/
theorem tendsto_div_hopf_bloch_r_nhdsWithin_zero
    {F_f G_f : ℝ → ℝ} {F₀ G₀ F_d G_d : ℝ}
    (hF : Tendsto (fun h : ℝ => (F_f h - F₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds F_d))
    (hG : Tendsto (fun h : ℝ => (G_f h - G₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds G_d)) :
    Tendsto
      (fun h : ℝ => ((F_f h + G_f h) - (F₀ + G₀)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (F_d + G_d)) :=
  (hF.add hG).congr (fun _ => by ring)

/-- **Universal Limit Theorem for the First Belavin–Polyakov Spherical Cauchy–Riemann Equation:**
`W₀ (∂_l^h Z) − Z₀ (∂_l^h W) − (R₀ (∂_τ^h H) − (∂_τ^h R) H₀) → 0`. -/
theorem tendsto_belavin_polyakov_spherical_cr_horiz_first_nhdsWithin_zero
    {H_t W_l Z_l R_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l))))
    (hZl : Tendsto (fun h : ℝ => (Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l))))
    (hRt : Tendsto (fun h : ℝ => (R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        ((M * S - N * C) * ((Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) -
            ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) * ((W_l h - (M * S - N * C)) / h)) -
          (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * ((H_t h - (M * C + N * S)) / h) -
            ((R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) * (M * C + N * S)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h1 :=
    (hZl.const_mul (M * S - N * C)).sub (hWl.const_mul ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)))
  have h2 :=
    (hHt.const_mul ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))).sub (hRt.mul_const (M * C + N * S))
  have hcomb := h1.sub h2
  rw [belavin_polyakov_spherical_cr_horiz_first M N C S M_l N_l C_l S_l, sub_self] at hcomb
  exact hcomb

/-- **Universal Limit Theorem for the Second Belavin–Polyakov Spherical Cauchy–Riemann Equation:**
`Z₀ (∂_l^h H) − H₀ (∂_l^h Z) − (R₀ (∂_τ^h W) − (∂_τ^h R) W₀) → 0`. -/
theorem tendsto_belavin_polyakov_spherical_cr_horiz_second_nhdsWithin_zero
    {H_l W_t Z_l R_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))))
    (hZl : Tendsto (fun h : ℝ => (Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l))))
    (hRt : Tendsto (fun h : ℝ => (R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        (((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) * ((H_l h - (M * C + N * S)) / h) -
            (M * C + N * S) * ((Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)) -
          (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) * ((W_t h - (M * S - N * C)) / h) -
            ((R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) * (M * S - N * C)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have h1 :=
    (hHl.const_mul ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))).sub (hZl.const_mul (M * C + N * S))
  have h2 :=
    (hWt.const_mul ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))).sub (hRt.mul_const (M * S - N * C))
  have hcomb := h1.sub h2
  rw [belavin_polyakov_spherical_cr_horiz_second M N C S M_l N_l C_l S_l, sub_self] at hcomb
  exact hcomb

/-- **Universal Minkowski Horizontal Conformal Energy Limit Theorem:**
`4 ((∂_l^h H)² + (∂_l^h W)²) + (∂_l^h Z)² − (∂_l^h R)² → 4 (W_re² + W_im²)`. -/
theorem tendsto_hopf_bloch_minkowski_conformal_horiz_nhdsWithin_zero
    {H_l W_l Z_l R_l : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l))))
    (hZl : Tendsto (fun h : ℝ => (Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l))))
    (hRl : Tendsto (fun h : ℝ => (R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) + 2 * (C * C_l + S * S_l)))) :
    Tendsto
      (fun h : ℝ =>
        4 * (((H_l h - (M * C + N * S)) / h) ^ 2 + ((W_l h - (M * S - N * C)) / h) ^ 2) +
          ((Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) ^ 2 -
          ((R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
            ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2))) := by
  have hcomb :=
    (((hHl.pow 2).add (hWl.pow 2)).const_mul 4).add (hZl.pow 2) |>.sub (hRl.pow 2)
  rw [hopf_bloch_minkowski_conformal_horiz_eq_wronskian_norm_sq M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Minkowski Vertical Conformal Energy Limit Theorem:**
`4 ((∂_τ^h H)² + (∂_τ^h W)²) + (∂_τ^h Z)² − (∂_τ^h R)² → 4 (W_re² + W_im²)`. -/
theorem tendsto_hopf_bloch_minkowski_conformal_vert_nhdsWithin_zero
    {H_t W_t Z_t R_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))))
    (hZt : Tendsto (fun h : ℝ => (Z_t h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l))))
    (hRt : Tendsto (fun h : ℝ => (R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) + 2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        4 * (((H_t h - (M * C + N * S)) / h) ^ 2 + ((W_t h - (M * S - N * C)) / h) ^ 2) +
          ((Z_t h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) ^ 2 -
          ((R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
            ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2))) := by
  have hcomb :=
    (((hHt.pow 2).add (hWt.pow 2)).const_mul 4).add (hZt.pow 2) |>.sub (hRt.pow 2)
  rw [hopf_bloch_minkowski_conformal_vert_eq_wronskian_norm_sq M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal Minkowski Conformal Orthogonality Limit Theorem:**
`4 ((∂_l^h H)(∂_τ^h H) + (∂_l^h W)(∂_τ^h W)) + (∂_l^h Z)(∂_τ^h Z) − (∂_l^h R)(∂_τ^h R) → 0`. -/
theorem tendsto_hopf_bloch_minkowski_conformal_orthogonality_nhdsWithin_zero
    {H_l H_t W_l W_t Z_l Z_t R_l R_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))))
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
        4 * (((H_l h - (M * C + N * S)) / h) * ((H_t h - (M * C + N * S)) / h) +
            ((W_l h - (M * S - N * C)) / h) * ((W_t h - (M * S - N * C)) / h)) +
          ((Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) *
            ((Z_t h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) -
          ((R_l h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h) *
            ((R_t h - ((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2))) / h))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hcomb :=
    (((hHl.mul hHt).add (hWl.mul hWt)).const_mul 4).add (hZl.mul hZt) |>.sub (hRl.mul hRt)
  rw [hopf_bloch_minkowski_conformal_orthogonality M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-- **Universal 3D Fubini–Study Spherical Jacobian Determinant Limit Theorem:**
`H₀ ((∂_l^h W)(∂_τ^h Z) − (∂_τ^h W)(∂_l^h Z)) + W₀ ((∂_l^h Z)(∂_τ^h H) − (∂_τ^h Z)(∂_l^h H)) +
  Z₀ ((∂_l^h H)(∂_τ^h W) − (∂_τ^h H)(∂_l^h W)) → R₀ (W_re² + W_im²)`. -/
theorem tendsto_hopf_bloch_spherical_jacobian_det_nhdsWithin_zero
    {H_l H_t W_l W_t Z_l Z_t : ℝ → ℝ} {M N C S M_l N_l C_l S_l : ℝ}
    (hHl : Tendsto (fun h : ℝ => (H_l h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + C * M_l) + (N * S_l + S * N_l))))
    (hHt : Tendsto (fun h : ℝ => (H_t h - (M * C + N * S)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * (-S_l) + C * (-N_l)) + (N * C_l + S * M_l))))
    (hWl : Tendsto (fun h : ℝ => (W_l h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * S_l + S * M_l) - (N * C_l + C * N_l))))
    (hWt : Tendsto (fun h : ℝ => (W_t h - (M * S - N * C)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((M * C_l + S * (-N_l)) - (N * (-S_l) + C * M_l))))
    (hZl : Tendsto (fun h : ℝ => (Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * M_l + N * N_l) - 2 * (C * C_l + S * S_l))))
    (hZt : Tendsto (fun h : ℝ => (Z_t h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (M * (-N_l) + N * M_l) - 2 * (C * (-S_l) + S * C_l)))) :
    Tendsto
      (fun h : ℝ =>
        (M * C + N * S) *
            (((W_l h - (M * S - N * C)) / h) *
                ((Z_t h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) -
              ((W_t h - (M * S - N * C)) / h) *
                ((Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h)) +
          (M * S - N * C) *
            (((Z_l h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) *
                ((H_t h - (M * C + N * S)) / h) -
              ((Z_t h - ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))) / h) *
                ((H_l h - (M * C + N * S)) / h)) +
          ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2)) *
            (((H_l h - (M * C + N * S)) / h) * ((W_t h - (M * S - N * C)) / h) -
              ((H_t h - (M * C + N * S)) / h) * ((W_l h - (M * S - N * C)) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((M ^ 2 + N ^ 2) + (C ^ 2 + S ^ 2)) *
          (((M_l * C - N_l * S) - (M * C_l - N * S_l)) ^ 2 +
            ((M_l * S + N_l * C) - (M * S_l + N * C_l)) ^ 2))) := by
  have hc1 := ((hWl.mul hZt).sub (hWt.mul hZl)).const_mul (M * C + N * S)
  have hc2 := ((hZl.mul hHt).sub (hZt.mul hHl)).const_mul (M * S - N * C)
  have hc3 := ((hHl.mul hWt).sub (hHt.mul hWl)).const_mul ((M ^ 2 + N ^ 2) - (C ^ 2 + S ^ 2))
  have hcomb := (hc1.add hc2).add hc3
  rw [hopf_bloch_spherical_jacobian_det_eq_radius_mul_wronskian_norm_sq
    M N C S M_l N_l C_l S_l] at hcomb
  exact hcomb

/-! ## Section 2: Full-Strip First-Order Partial Derivatives of `(Z_k, R_k)` and Belavin–Polyakov Spherical Cauchy–Riemann System Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`) -/

/-- **Full-Strip Horizontal Partial Derivative `∂_l Z_k(l, τ)` of the Vertical Bloch Coordinate
`Z_k = |F_k|² − |Δ_k|²` (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`).** -/
theorem tendsto_div_hopfBlochZ_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
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
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
          2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) :=
  tendsto_div_hopf_bloch_z_nhdsWithin_zero
    (tendsto_div_complexModulusSq_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_horiz_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip Vertical Partial Derivative `∂_τ Z_k(l, τ)` of the Vertical Bloch Coordinate
`Z_k = |F_k|² − |Δ_k|²` (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`).** -/
theorem tendsto_div_hopfBlochZ_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
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
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
          2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (-(∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
              ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) :=
  tendsto_div_hopf_bloch_z_nhdsWithin_zero
    (tendsto_div_complexModulusSq_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_vert_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip Horizontal Partial Derivative `∂_l R_k(l, τ)` of the Minkowski Radius
`R_k = |F_k|² + |Δ_k|²` (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`).** -/
theorem tendsto_div_hopfBlochR_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
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
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) :=
  tendsto_div_hopf_bloch_r_nhdsWithin_zero
    (tendsto_div_complexModulusSq_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_horiz_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip Vertical Partial Derivative `∂_τ R_k(l, τ)` of the Minkowski Radius
`R_k = |F_k|² + |Δ_k|²` (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`).** -/
theorem tendsto_div_hopfBlochR_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
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
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (-(∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
              ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) :=
  tendsto_div_hopf_bloch_r_nhdsWithin_zero
    (tendsto_div_complexModulusSq_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_vert_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip First Belavin–Polyakov Spherical Cauchy–Riemann Equation for `(H_k, W_k, Z_k, R_k)`
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`W_k (∂_l^h Z_k) − Z_k (∂_l^h W_k) − (R_k (∂_τ^h H_k) − (∂_τ^h R_k) H_k) → 0`. -/
theorem tendsto_belavinPolyakov_spherical_cr_horiz_first_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) -
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
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) -
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) -
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_belavin_polyakov_spherical_cr_horiz_first_nhdsWithin_zero
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_vert_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip Second Belavin–Polyakov Spherical Cauchy–Riemann Equation for `(H_k, W_k, Z_k, R_k)`
(`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`Z_k (∂_l^h H_k) − H_k (∂_l^h Z_k) − (R_k (∂_τ^h W_k) − (∂_τ^h R_k) W_k) → 0`. -/
theorem tendsto_belavinPolyakov_spherical_cr_horiz_second_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) -
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)) -
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
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_belavin_polyakov_spherical_cr_horiz_second_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_vert_shift_nhds_zero hk hν hl τ)

/-! ## Section 3: Full-Strip Minkowski Conformal Isometry Laws and 3D Fubini–Study Spherical Jacobian Across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`) -/

/-- **Full-Strip Minkowski Horizontal Conformal Energy Law (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`4 ((∂_l^h H_k)² + (∂_l^h W_k)²) + (∂_l^h Z_k)² − (∂_l^h R_k)² → 4 (W_{k,\mathrm{re}}² + W_{k,\mathrm{im}}²)`. -/
theorem tendsto_hopfBloch_minkowski_conformal_horiz_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        4 * (((((∫ x in Ioi (0 : ℝ),
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
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) ^ 2) +
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2 -
          (((((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2)
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
  tendsto_hopf_bloch_minkowski_conformal_horiz_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_horiz_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip Minkowski Vertical Conformal Energy Law (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`4 ((∂_τ^h H_k)² + (∂_τ^h W_k)²) + (∂_τ^h Z_k)² − (∂_τ^h R_k)² → 4 (W_{k,\mathrm{re}}² + W_{k,\mathrm{im}}²)`. -/
theorem tendsto_hopfBloch_minkowski_conformal_vert_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        4 * (((((∫ x in Ioi (0 : ℝ),
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) ^ 2 +
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
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) ^ 2) +
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2 -
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) ^ 2)
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
  tendsto_hopf_bloch_minkowski_conformal_vert_nhdsWithin_zero
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_vert_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip Minkowski Conformal Orthogonality Law (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`4 ((∂_l^h H_k)(∂_τ^h H_k) + (∂_l^h W_k)(∂_τ^h W_k)) + (∂_l^h Z_k)(∂_τ^h Z_k) − (∂_l^h R_k)(∂_τ^h R_k) → 0`. -/
theorem tendsto_hopfBloch_minkowski_conformal_orthogonality_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        4 * (((((∫ x in Ioi (0 : ℝ),
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) +
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
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
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
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) +
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) -
          (((((∫ x in Ioi (0 : ℝ),
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_hopf_bloch_minkowski_conformal_orthogonality_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochR_vert_shift_nhds_zero hk hν hl τ)

/-- **Full-Strip 3D Fubini–Study Spherical Jacobian Determinant Law (`|l| < 1/8`, `τ ∈ ℝ`, `k ≥ 2`):**
`H_k ((∂_l^h W_k)(∂_τ^h Z_k) − (∂_τ^h W_k)(∂_l^h Z_k)) +
  W_k ((∂_l^h Z_k)(∂_τ^h H_k) − (∂_τ^h Z_k)(∂_l^h H_k)) +
  Z_k ((∂_l^h H_k)(∂_τ^h W_k) − (∂_τ^h H_k)(∂_l^h W_k)) → R_k (W_{k,\mathrm{re}}² + W_{k,\mathrm{im}}²) ≥ 0`. -/
theorem tendsto_hopfBloch_spherical_jacobian_det_nhds_zero
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
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) -
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
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
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
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)) +
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) -
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) +
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
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
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
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
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
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
  tendsto_hopf_bloch_spherical_jacobian_det_nhdsWithin_zero
    (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_hopfBlochZ_vert_shift_nhds_zero hk hν hl τ)

/-! ## Section 4: Critical-Line (`l = 0`) Even Reflection Symmetry and Horizontal Stationarity of `(Z_k, R_k)` (`k ≥ 1` / `k ≥ 2`) -/

/-- **Even Horizontal Reflection Symmetry `Z_k(−l, τ) = Z_k(l, τ)` (`k ≥ 1`, `l, τ ∈ ℝ`):** -/
theorem hopfBlochZ_neg_left
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (((∫ x in Ioi (0 : ℝ),
          x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (0 : ℝ),
          x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
      (((∫ x in Ioi (1 : ℝ),
            x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        ((∫ x in Ioi (1 : ℝ),
            x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) =
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
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  rw [setIntegral_Ioi_rpow_neg_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector hk ν l τ,
    setIntegral_Ioi_rpow_neg_mul_sin_log_eq_neg hk ν l τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_cos_log hk ν l τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_sin_log hk ν l τ]
  ring

/-- **Even Horizontal Reflection Symmetry `R_k(−l, τ) = R_k(l, τ)` (`k ≥ 1`, `l, τ ∈ ℝ`):** -/
theorem hopfBlochR_neg_left
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (((∫ x in Ioi (0 : ℝ),
          x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (0 : ℝ),
          x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
      (((∫ x in Ioi (1 : ℝ),
            x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        ((∫ x in Ioi (1 : ℝ),
            x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) =
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
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  rw [setIntegral_Ioi_rpow_neg_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector hk ν l τ,
    setIntegral_Ioi_rpow_neg_mul_sin_log_eq_neg hk ν l τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_cos_log hk ν l τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_sin_log hk ν l τ]
  ring

/-- **Critical-Line Horizontal Stationarity `∂_l Z_k(0, τ) = 0` (`τ ∈ ℝ`, `k ≥ 2`):** -/
theorem tendsto_div_hopfBlochZ_horiz_shift_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
          (((∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hk1 : 1 ≤ k := by omega
  have h := tendsto_div_hopfBlochZ_horiz_shift_nhds_zero
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
  have hsinh0 :
      (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall (fun v => ?_))
    dsimp only
    rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
    rfl
  have hsinh_Ioi :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero (fun v _ => ?_)
    rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  have hΔc0 := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_cos_log hk1 ν τ
  rw [hl0] at hΔc0
  rw [hl0] at h
  have hlim :
      (2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
          2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) = 0 := by
    rw [hsinh0, hsinh_Ioi,
      setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk1 ν τ,
      hΔc0]
    ring
  rw [hlim] at h
  refine h.congr (fun h' => ?_)
  have hh_pos : (0 : ℝ) + h' - 1 / 2 = h' - 1 / 2 := by ring
  rw [hh_pos]

/-- **Critical-Line Horizontal Stationarity `∂_l R_k(0, τ) = 0` (`τ ∈ ℝ`, `k ≥ 2`):** -/
theorem tendsto_div_hopfBlochR_horiz_shift_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (0 : ℝ),
                x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
          (((∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hk1 : 1 ≤ k := by omega
  have h := tendsto_div_hopfBlochR_horiz_shift_nhds_zero
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
  have hsinh0 :
      (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall (fun v => ?_))
    dsimp only
    rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
    rfl
  have hsinh_Ioi :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero (fun v _ => ?_)
    rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  have hΔc0 := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_cos_log hk1 ν τ
  rw [hl0] at hΔc0
  rw [hl0] at h
  have hlim :
      (2 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          2 * (((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) = 0 := by
    rw [hsinh0, hsinh_Ioi,
      setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk1 ν τ,
      hΔc0]
    ring
  rw [hlim] at h
  refine h.congr (fun h' => ?_)
  have hh_pos : (0 : ℝ) + h' - 1 / 2 = h' - 1 / 2 := by ring
  rw [hh_pos]

/-- **Master Witness Theorem for the Hopf–Bloch Minkowski Null-Cone Lift, Belavin–Polyakov Spherical
Cauchy–Riemann System, Conformal Isometry Laws, and 3D Fubini–Study Spherical Jacobian:**
There exists an explicit symmetric non-zero finite arc measure `ν` on `ArcParam` such that for all
`k ≥ 2`:
1. Across `|l| < 1/8` and `τ ∈ ℝ`, the 4D Minkowski–Hopf–Bloch vector `(2 H_k, 2 W_k, Z_k, R_k)`
   satisfies the Minkowski conformal orthogonality law
   `4 ((∂_l^h H_k)(∂_τ^h H_k) + (∂_l^h W_k)(∂_τ^h W_k)) + (∂_l^h Z_k)(∂_τ^h Z_k) − (∂_l^h R_k)(∂_τ^h R_k) → 0`;
2. On the critical line `l = 0`, both `Z_k` and `R_k` are horizontally stationary:
   `∂_l Z_k(0, τ) = 0` and `∂_l R_k(0, τ) = 0` for all `τ ∈ ℝ`. -/
theorem exists_dyadic_hopfBloch_minkowskiConformal_sphericalJacobian_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              4 * (((((∫ x in Ioi (0 : ℝ),
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
                              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
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
                              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) +
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
                              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
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
                              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) +
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
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h) -
                (((((∫ x in Ioi (0 : ℝ),
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
                            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) ∧
        (∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              ((((∫ x in Ioi (0 : ℝ),
                      x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                  (((∫ x in Ioi (1 : ℝ),
                        x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
                (((∫ x in Ioi (0 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    (∫ x in Ioi (0 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                  (((∫ x in Ioi (1 : ℝ),
                        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk =>
    ⟨fun l hl τ => tendsto_hopfBloch_minkowski_conformal_orthogonality_nhds_zero hk hν hl τ,
     fun τ => tendsto_div_hopfBlochZ_horiz_shift_at_criticalLine_nhds_zero hk hν τ⟩⟩

end

end RHTower
