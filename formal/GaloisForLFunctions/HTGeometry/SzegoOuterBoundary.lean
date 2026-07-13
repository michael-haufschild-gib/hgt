import GaloisForLFunctions.HTGeometry.PoissonFatou
import GaloisForLFunctions.HTGeometry.SzegoOuterFunction

/-!
# Boundary modulus of the Szegő outer function

The squared modulus of the Szegő outer function on the disk is the Poisson integral of the log
weight: `‖D(r e^{iφ})‖² = exp((2π)⁻¹∫₀²π P_r(θ-φ) log w(θ) dθ)`.  Combined with Fatou's theorem
(`tendsto_poissonConv_ae`) this gives the boundary identity `|D|² = w` a.e. — the analytic input to
the `≤` half of the first Szegő limit theorem.

The bridge is that the real part of the (negated) Herglotz–Riesz kernel evaluated at an interior
point `r e^{iφ}` and a boundary point `e^{iθ}` is exactly the angular Poisson kernel `P_r(θ-φ)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Real MeasureTheory Complex intervalIntegral
open scoped Real

/-- Squared distance between an interior point `r e^{iφ}` and a boundary point `e^{iθ}` of the unit
circle: `‖r e^{iφ} - e^{iθ}‖² = r² - 2r cos(θ-φ) + 1`. -/
theorem norm_sub_circleMap_sq (r φ θ : ℝ) :
    ‖circleMap 0 r φ - circleMap 0 1 θ‖ ^ 2 = r ^ 2 - 2 * r * Real.cos (θ - φ) + 1 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, circleMap, Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_add, one_mul, zero_mul, sub_zero]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq φ, Real.sin_sq_add_cos_sq θ]

/-- The negated real part of the Herglotz–Riesz kernel at interior point `r e^{iφ}` and boundary
point `e^{iθ}` is the angular Poisson kernel: `-Re(herglotz 0 e^{iθ} (r e^{iφ})) = P_r(θ-φ)`. -/
theorem neg_re_herglotz_eq_poissonKer {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (φ θ : ℝ) :
    -(herglotzRieszKernel 0 (circleMap 0 1 θ) (circleMap 0 r φ)).re = poissonKer r (θ - φ) := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hre : (herglotzRieszKernel 0 (circleMap 0 1 θ) (circleMap 0 r φ)).re
      = poissonKernel 0 (circleMap 0 1 θ) (circleMap 0 r φ) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]; rfl
  rw [hre, poissonKernel_def]
  simp only [sub_zero]
  rw [norm_circleMap_zero, norm_circleMap_zero, abs_of_nonneg hr0,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1), norm_sub_circleMap_sq, poissonKer]
  have hden : 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 ≠ 0 := (poissonKer_denom_pos habs (θ - φ)).ne'
  rw [← neg_div]
  congr 1 <;> ring

end GaloisForLFunctions.HTGeometry
