import GaloisForLFunctions.RHTower.SmoothAFEZetaContour
import GaloisForLFunctions.RHTower.ZetaCarrier

/-!
# Exact reflected Dirichlet expansion on the left AFE flank

Whenever `Re(1-s-w) > 1`, the zeta functional equation and the absolutely convergent Dirichlet
series give the pointwise identity

`ζ(s+w) x^w G(w)/w
  = Σₙ χ(s+w) (n+1)^(s+w-1) x^w G(w)/w`.

In particular this holds on `Re w = -1` for `Re s = 1/2`.  This module performs no Gamma-ratio
approximation; the exact varying factor `χ(s+w)` is retained.
-/

noncomputable section

namespace RHTower

open Complex

def smoothAFEZetaReflectedTerm
    (s : ℂ) (x : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  zetaChi (s + w) *
    (1 / (n + 1 : ℂ) ^ (1 - (s + w))) *
      (x : ℂ) ^ w * smoothAFEGaussianKernel w

theorem smoothAFEZetaMellinIntegrand_eq_reflected_tsum
    {s w : ℂ} {x : ℝ} (hreflect : 1 < (1 - (s + w)).re) :
    smoothAFEZetaMellinIntegrand s x w =
      ∑' n : ℕ, smoothAFEZetaReflectedTerm s x n w := by
  have hz0 : s + w ≠ 0 := by
    intro h
    rw [h] at hreflect
    norm_num at hreflect
  have hz1 : s + w ≠ 1 := by
    intro h
    rw [h] at hreflect
    norm_num at hreflect
  have hGamma : Gammaℝ (1 - (s + w)) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hreflect)
  have hzeta :
      riemannZeta (1 - (s + w)) =
        ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (1 - (s + w)) :=
    zeta_eq_tsum_one_div_nat_add_one_cpow hreflect
  rw [smoothAFEZetaMellinIntegrand,
    zeta_eq_zetaChi_mul hz0 hz1 hGamma, hzeta]
  simp only [smoothAFEZetaReflectedTerm, ← tsum_mul_left, ← tsum_mul_right]

theorem smoothAFEZetaMellinIntegrand_eq_reflected_tsum_left_one
    {s : ℂ} {x t : ℝ} (hsre : s.re = 1 / 2) :
    smoothAFEZetaMellinIntegrand s x
        ((-1 : ℂ) + (t : ℂ) * I) =
      ∑' n : ℕ, smoothAFEZetaReflectedTerm s x n
        ((-1 : ℂ) + (t : ℂ) * I) := by
  apply smoothAFEZetaMellinIntegrand_eq_reflected_tsum
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re,
    Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero]
  rw [hsre]
  norm_num

theorem smoothAFEZetaReflectedTerm_eq_cpow
    (s : ℂ) (x : ℝ) (n : ℕ) (w : ℂ) :
    smoothAFEZetaReflectedTerm s x n w =
      zetaChi (s + w) * (n + 1 : ℂ) ^ (s + w - 1) *
        (x : ℂ) ^ w * smoothAFEGaussianKernel w := by
  rw [smoothAFEZetaReflectedTerm, one_div, ← Complex.cpow_neg]
  congr 2
  ring_nf

end RHTower
