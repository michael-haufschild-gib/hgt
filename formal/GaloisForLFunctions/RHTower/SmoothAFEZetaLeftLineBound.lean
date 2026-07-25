import GaloisForLFunctions.RHTower.SmoothAFEDualFactorization
import GaloisForLFunctions.RHTower.ZetaVerticalSqrtBound
import GaloisForLFunctions.RHTower.Reflection

/-!
# Exact archimedean and zeta bounds on the smooth-AFE left line

The contour used by the Gaussian smooth approximate functional equation has left edge
`w = -1+iv`.  On the critical line this puts the zeta argument at
`-1/2+i(τ+v)`.  Deligne's exact two-step Gamma recurrence makes the modulus of the
functional-equation factor elementary on this line:

`‖χ(-1/2+it)‖ = ‖-1/2+it‖ / (2π)`.

Combining this identity with the already formalized square-root bound for zeta on
`Re s ≥ 1/2` gives an unconditional polynomial bound for zeta on the full left edge.
-/

noncomputable section

namespace RHTower

open Complex

/-- The zeta argument on the left edge of the critical-line smooth-AFE contour. -/
def smoothAFEZetaLeftLinePt (t : ℝ) : ℂ :=
  ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I

@[simp]
theorem smoothAFEZetaLeftLinePt_re (t : ℝ) :
    (smoothAFEZetaLeftLinePt t).re = -1 / 2 := by
  simp [smoothAFEZetaLeftLinePt]

@[simp]
theorem smoothAFEZetaLeftLinePt_im (t : ℝ) :
    (smoothAFEZetaLeftLinePt t).im = t := by
  simp [smoothAFEZetaLeftLinePt]

theorem smoothAFEZetaLeftLinePt_ne_zero (t : ℝ) :
    smoothAFEZetaLeftLinePt t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

theorem one_sub_smoothAFEZetaLeftLinePt_eq_conj_add_two (t : ℝ) :
    1 - smoothAFEZetaLeftLinePt t =
      (starRingEnd ℂ) (smoothAFEZetaLeftLinePt t + 2) := by
  apply Complex.ext <;>
    norm_num [smoothAFEZetaLeftLinePt, map_add, map_mul, map_div₀, map_neg]

/-- Exact modulus of the zeta functional-equation factor on `Re s = -1/2`. -/
theorem norm_zetaChi_smoothAFEZetaLeftLinePt (t : ℝ) :
    ‖zetaChi (smoothAFEZetaLeftLinePt t)‖ =
      ‖smoothAFEZetaLeftLinePt t‖ / (2 * Real.pi) := by
  let z := smoothAFEZetaLeftLinePt t
  change ‖zetaChi z‖ = ‖z‖ / (2 * Real.pi)
  have hz0 : z ≠ 0 := smoothAFEZetaLeftLinePt_ne_zero t
  have hshift : Complex.Gammaℝ (z + 2) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    dsimp only [z]
    rw [Complex.add_re, smoothAFEZetaLeftLinePt_re]
    norm_num
  have hrec := Complex.Gammaℝ_add_two hz0
  have hzetaGamma : Complex.Gammaℝ z ≠ 0 := by
    intro hzero
    rw [hzero] at hrec
    simp at hrec
    exact hshift hrec
  have hconj :
      Complex.Gammaℝ (1 - z) =
        (starRingEnd ℂ) (Complex.Gammaℝ (z + 2)) := by
    rw [show 1 - z = (starRingEnd ℂ) (z + 2) by
      simpa only [z] using one_sub_smoothAFEZetaLeftLinePt_eq_conj_add_two t,
      Gammaℝ_conj]
  have hnormGamma : ‖Complex.Gammaℝ z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hzetaGamma
  rw [zetaChi, hconj, norm_div]
  simp only [Complex.norm_conj]
  rw [hrec, norm_div, norm_div, norm_mul]
  norm_num only [norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  field_simp

/-- The reflected zeta argument lies on `Re s = 3/2` and stays at least `1/2`
away from the pole. -/
theorem one_sub_smoothAFEZetaLeftLinePt_re (t : ℝ) :
    (1 - smoothAFEZetaLeftLinePt t).re = 3 / 2 := by
  rw [Complex.sub_re, Complex.one_re, smoothAFEZetaLeftLinePt_re]
  norm_num

theorem half_le_norm_one_sub_smoothAFEZetaLeftLinePt_sub_one (t : ℝ) :
    (1 / 2 : ℝ) ≤ ‖(1 - smoothAFEZetaLeftLinePt t) - 1‖ := by
  have hre :
      ((1 - smoothAFEZetaLeftLinePt t) - 1).re = 1 / 2 := by
    rw [Complex.sub_re, one_sub_smoothAFEZetaLeftLinePt_re, Complex.one_re]
    norm_num
  calc
    (1 / 2 : ℝ) = |((1 - smoothAFEZetaLeftLinePt t) - 1).re| := by
      rw [hre]
      norm_num
    _ ≤ ‖(1 - smoothAFEZetaLeftLinePt t) - 1‖ :=
      Complex.abs_re_le_norm _

/-- Unconditional polynomial-growth certificate for zeta on the complete left
edge `Re s = -1/2`.  No asymptotic hypothesis is used. -/
theorem norm_riemannZeta_smoothAFEZetaLeftLinePt_le (t : ℝ) :
    ‖riemannZeta (smoothAFEZetaLeftLinePt t)‖ ≤
      (‖smoothAFEZetaLeftLinePt t‖ / (2 * Real.pi)) *
        (6 * Real.sqrt (‖1 - smoothAFEZetaLeftLinePt t‖ + 2)) := by
  let z := smoothAFEZetaLeftLinePt t
  have hz0 : z ≠ 0 := smoothAFEZetaLeftLinePt_ne_zero t
  have hz1 : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [z] at hre
    rw [smoothAFEZetaLeftLinePt_re, Complex.one_re] at hre
    norm_num at hre
  have hGamma : Complex.Gammaℝ (1 - z) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    dsimp only [z]
    rw [one_sub_smoothAFEZetaLeftLinePt_re]
    norm_num
  have hreflect := zeta_eq_zetaChi_mul hz0 hz1 hGamma
  have hzetaRight :
      ‖riemannZeta (1 - z)‖ ≤
        6 * Real.sqrt (‖1 - z‖ + 2) := by
    have hraw := norm_riemannZeta_le_sqrt_norm_add_two_half
      (s := 1 - z)
      (by
        dsimp only [z]
        rw [one_sub_smoothAFEZetaLeftLinePt_re]
        norm_num)
      (d := 1 / 2) (by norm_num)
      (by
        dsimp only [z]
        exact half_le_norm_one_sub_smoothAFEZetaLeftLinePt_sub_one t)
    norm_num at hraw ⊢
    exact hraw
  rw [hreflect, norm_mul,
    show ‖zetaChi z‖ = ‖z‖ / (2 * Real.pi) by
      dsimp only [z]
      exact norm_zetaChi_smoothAFEZetaLeftLinePt t]
  gcongr

end RHTower
