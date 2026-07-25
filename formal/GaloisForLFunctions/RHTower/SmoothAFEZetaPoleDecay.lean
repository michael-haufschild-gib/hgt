import GaloisForLFunctions.RHTower.SmoothAFEDualFactorization

/-!
# Gaussian decay of the shifted zeta-pole residue

On the critical line, the secondary contour residue lies at `w = 1/2-iτ`.  Its Gaussian factor has
exact modulus `exp(1/4-τ²)`, while the denominator has modulus at least `|τ|`.  For `|τ| ≥ 1` this
gives a direct exponentially decaying bound.
-/

noncomputable section

namespace RHTower

open Complex

theorem norm_one_sub_linePt_sq_exp (τ : ℝ) :
    ‖Complex.exp ((1 - linePt τ) ^ 2)‖ =
      Real.exp (1 / 4 - τ ^ 2) := by
  rw [Complex.norm_exp]
  have hcoord :
      (1 : ℂ) - linePt τ =
        ((1 / 2 : ℝ) : ℂ) - (τ : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  rw [hcoord]
  simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    mul_one, sub_self]
  ring_nf

theorem norm_one_sub_linePt_ge_abs (τ : ℝ) :
    |τ| ≤ ‖1 - linePt τ‖ := by
  calc
    |τ| = |(1 - linePt τ).im| := by
      unfold linePt
      simp
    _ ≤ ‖1 - linePt τ‖ := Complex.abs_im_le_norm _

theorem norm_smoothAFEZetaShiftedPoleResidue_line_le
    {x τ : ℝ} (hx : 0 < x) (hτ : 1 ≤ |τ|) :
    ‖smoothAFEZetaShiftedPoleResidue (linePt τ) x‖ ≤
      Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(τ ^ 2)) := by
  have hden : 1 ≤ ‖1 - linePt τ‖ :=
    hτ.trans (norm_one_sub_linePt_ge_abs τ)
  rw [smoothAFEZetaShiftedPoleResidue, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx,
    norm_one_sub_linePt_sq_exp]
  have hre : (1 - linePt τ).re = 1 / 2 := by
    rw [Complex.sub_re, Complex.one_re, linePt_re]
    norm_num
  rw [hre, ← Real.sqrt_eq_rpow]
  calc
    Real.sqrt x * Real.exp (1 / 4 - τ ^ 2) / ‖1 - linePt τ‖
        ≤ Real.sqrt x * Real.exp (1 / 4 - τ ^ 2) := by
      apply (div_le_iff₀ (zero_lt_one.trans_le hden)).2
      exact le_mul_of_one_le_right (by positivity) hden
    _ = Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(τ ^ 2)) := by
      rw [show (1 / 4 : ℝ) - τ ^ 2 = 1 / 4 + (-(τ ^ 2)) by ring,
        Real.exp_add]
      ring

end RHTower
