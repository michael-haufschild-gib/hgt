/-
The seam sign bit at the real anchor, read off the coefficient side.

On the real segment of the critical strip `σ ∈ (0,1)` the completed `ξ` is a
strictly positive real number: `(xi σ).im = 0` and `0 < (xi σ).re`.  The
mechanism is entirely arithmetic, not symmetry:

* The zeta value is a *negative* real there.  This is the coefficient-side input
  `riemannZeta_real_strip_neg`, supplied by the dedicated real-strip module: the
  paired Dirichlet-eta series is positive on `(0,1)` and the eta factor
  `1 − 2^{1−σ}` is negative, so `ζ(σ) = E(σ)/(1 − 2^{1−σ})` is negative.

* The archimedean factor `archFactor σ = σ(σ−1)/2 · Γ_ℝ(σ)` is a negative
  real on `(0,1)` (the polynomial part is negative, `Γ_ℝ` positive).

The product `ξ(σ) = archFactor(σ)·ζ(σ) = (negative)·(negative)` is a positive
real.  The base point of all seam-sign bookkeeping is `+`, forced by the
coefficients themselves.

This file keeps only the archimedean-factor bookkeeping and the `ξ` assembly;
the zeta-negativity input comes from `GaloisForLFunctions.RHTower.ZetaRealStrip`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.ZetaRealStrip

namespace RHTower

open Complex

/-! ### `ζ` is a negative real on `(0,1)`, hence `ξ` is a positive real -/

/-- On the open real segment `(0,1)` the Riemann zeta function takes a strictly
negative real value.  This is the coefficient-side statement
`riemannZeta_real_strip_neg` from the dedicated real-strip module. -/
private theorem zeta_neg_real_on_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ Z : ℝ, Z < 0 ∧ riemannZeta (σ:ℂ) = (Z:ℂ) :=
  riemannZeta_real_strip_neg h0 h1

/-- On `(0,1)` the archimedean factor `σ(σ−1)/2 · Γ_ℝ(σ)` is a negative real. -/
private theorem archFactor_neg_real {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ Wa : ℝ, Wa < 0 ∧ archFactor (σ:ℂ) = (Wa:ℂ) := by
  refine ⟨σ*(σ-1)/2 * (Real.pi^(-σ/2) * Real.Gamma (σ/2)), ?_, ?_⟩
  · apply mul_neg_of_neg_of_pos
    · apply div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h0 (by linarith)) (by norm_num)
    · exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
  · rw [archFactor, Complex.Gammaℝ_def, show ((σ:ℂ)/2) = (((σ/2):ℝ):ℂ) by push_cast; ring,
        Complex.Gamma_ofReal, show (-(σ:ℂ)/2) = (((-σ/2):ℝ):ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow Real.pi_pos.le]
    push_cast; ring

/-- On `(0,1)` the completed `ξ` is a strictly positive real number. -/
private theorem xi_real_anchor_eq {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ r : ℝ, 0 < r ∧ xi (σ:ℂ) = (r:ℂ) := by
  obtain ⟨Z, hZ, hζ⟩ := zeta_neg_real_on_Ioo h0 h1
  obtain ⟨Wa, hWa, harch⟩ := archFactor_neg_real h0 h1
  have hσ0 : (σ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h0)
  have hσ1 : (σ:ℂ) ≠ 1 := by rw [Ne, Complex.ofReal_eq_one]; exact ne_of_lt h1
  have hG : Gammaℝ (σ:ℂ) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using h0)
  refine ⟨Wa * Z, mul_pos_of_neg_of_neg hWa hZ, ?_⟩
  rw [xi_eq_archFactor_mul_zeta hσ0 hσ1 hG, harch, hζ, ← Complex.ofReal_mul]

/-! ### The seam sign bit at the real anchor -/

/-- `ξ` is real on the real segment of the critical strip: for `σ ∈ (0,1)`,
`ξ(σ)` has vanishing imaginary part. -/
theorem xi_real_on_real_anchor {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (xi (σ:ℂ)).im = 0 := by
  obtain ⟨r, _, hr⟩ := xi_real_anchor_eq h0 h1
  rw [hr, Complex.ofReal_im]

/-- `ξ` is strictly positive on the real segment of the critical strip: for
`σ ∈ (0,1)`, `0 < ξ(σ).re`.  The seam sign at the real anchor is `+`, forced by
the coefficients (positive paired eta series, negative eta factor, negative
archimedean factor). -/
theorem xi_pos_on_real_anchor {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    0 < (xi (σ:ℂ)).re := by
  obtain ⟨r, hr, hval⟩ := xi_real_anchor_eq h0 h1
  rw [hval, Complex.ofReal_re]; exact hr

end RHTower
