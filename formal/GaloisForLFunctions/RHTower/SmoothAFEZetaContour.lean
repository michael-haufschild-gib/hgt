import GaloisForLFunctions.RHTower.SmoothAFEZetaResidueDecomposition
import GaloisForLFunctions.RHTower.RectangleTwoPoleResidue
import GaloisForLFunctions.RHTower.HardyCarrier

/-!
# Finite rectangular contour shift for the smooth zeta Mellin integrand

The pole decomposition now feeds directly into the rectangle residue theorem.  Any rectangle
strictly enclosing both `w = 0` and `w = 1-s` has boundary integral

`2πi (ζ(s) + x^(1-s) exp((1-s)²)/(1-s))`.

This is the exact finite-contour identity underlying the smooth approximate functional equation.
-/

noncomputable section

namespace RHTower

open Complex

theorem rectIntegral_smoothAFEZetaMellinIntegrand_eq
    {s : ℂ} {x : ℝ} {z₁ z₂ : ℂ}
    (hx : 0 < x) (hs : s ≠ 1)
    (h01 : z₁.re < 0) (h02 : 0 < z₂.re)
    (h03 : z₁.im < 0) (h04 : 0 < z₂.im)
    (hρ1 : z₁.re < (1 - s).re) (hρ2 : (1 - s).re < z₂.re)
    (hρ3 : z₁.im < (1 - s).im) (hρ4 : (1 - s).im < z₂.im) :
    rectIntegral (smoothAFEZetaMellinIntegrand s x) z₁ z₂ =
      2 * Real.pi * I *
        (riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) := by
  apply rectIntegral_eq_two_pole_residues
    (p := 0) (q := 1 - s)
    (R := smoothAFEZetaPoleRemainder s x)
    h01 h02 h03 h04 hρ1 hρ2 hρ3 hρ4
    (differentiable_smoothAFEZetaPoleRemainder hx s)
  intro z hz0 hzρ
  simpa only [sub_zero, add_assoc] using
    smoothAFEZetaMellinIntegrand_eq_two_poles_add_remainder
      (x := x) hs hz0 hzρ

theorem rectIntegral_smoothAFEZetaMellinIntegrand_horizontal_box
    {s : ℂ} {x a b T : ℝ}
    (hx : 0 < x) (hs : s ≠ 1)
    (ha0 : a < 0) (h0b : 0 < b) (hT : 0 < T)
    (hρa : a < (1 - s).re) (hρb : (1 - s).re < b)
    (hρlow : -T < (1 - s).im) (hρhigh : (1 - s).im < T) :
    rectIntegral (smoothAFEZetaMellinIntegrand s x)
        ((a : ℂ) - (T : ℂ) * I) ((b : ℂ) + (T : ℂ) * I) =
      2 * Real.pi * I *
        (riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) := by
  apply rectIntegral_smoothAFEZetaMellinIntegrand_eq hx hs
  · simpa using ha0
  · simpa using h0b
  · simpa using hT
  · simpa using hT
  · simpa using hρa
  · simpa using hρb
  · simpa using hρlow
  · simpa using hρhigh

theorem smoothAFEZetaMellin_finite_contour_shift_line
    {x τ T : ℝ} (hx : 0 < x) (hT : |τ| < T) :
    ((∫ u : ℝ in (-1)..1,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            ((u : ℂ) - (T : ℂ) * I)) -
        (∫ u : ℝ in (-1)..1,
          smoothAFEZetaMellinIntegrand (linePt τ) x
            ((u : ℂ) + (T : ℂ) * I)) +
      I • (∫ v : ℝ in (-T)..T,
        smoothAFEZetaMellinIntegrand (linePt τ) x
          ((1 : ℂ) + (v : ℂ) * I))) -
      I • (∫ v : ℝ in (-T)..T,
        smoothAFEZetaMellinIntegrand (linePt τ) x
          ((-1 : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I *
        (riemannZeta (linePt τ) +
          smoothAFEZetaShiftedPoleResidue (linePt τ) x) := by
  have hs : linePt τ ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [linePt_re, Complex.one_re] at hre
    norm_num at hre
  have hTpos : 0 < T := (abs_nonneg τ).trans_lt hT
  have hρre : (1 - linePt τ).re = 1 / 2 := by
    rw [Complex.sub_re, Complex.one_re, linePt_re]
    norm_num
  have hρim : (1 - linePt τ).im = -τ := by
    unfold linePt
    simp
  have habs := abs_lt.mp hT
  have hbox := rectIntegral_smoothAFEZetaMellinIntegrand_horizontal_box
    (s := linePt τ) (x := x) (a := -1) (b := 1) (T := T)
    hx hs (by norm_num) (by norm_num) hTpos
    (by rw [hρre]; norm_num) (by rw [hρre]; norm_num)
    (by rw [hρim]; linarith) (by rw [hρim]; linarith)
  simpa [rectIntegral] using hbox

end RHTower
