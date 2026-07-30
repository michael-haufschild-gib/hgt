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

/-- A simpler quadratic envelope for the preceding exact reflected bound. -/
theorem norm_riemannZeta_smoothAFEZetaLeftLinePt_le_quadratic (t : ℝ) :
    ‖riemannZeta (smoothAFEZetaLeftLinePt t)‖ ≤
      6 * (1 + |t|) * (4 + |t|) := by
  have hzNorm :
      ‖smoothAFEZetaLeftLinePt t‖ ≤ 1 + |t| := by
    rw [smoothAFEZetaLeftLinePt]
    calc
      ‖(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
          ‖(((-1 / 2 : ℝ) : ℂ))‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 / 2 + |t| := by
        rw [norm_mul, norm_I]
        norm_num
      _ ≤ 1 + |t| := by linarith
  have honePi : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hchi :
      ‖smoothAFEZetaLeftLinePt t‖ / (2 * Real.pi) ≤ 1 + |t| := by
    calc
      ‖smoothAFEZetaLeftLinePt t‖ / (2 * Real.pi)
          ≤ ‖smoothAFEZetaLeftLinePt t‖ := by
            exact div_le_self (norm_nonneg _) honePi
      _ ≤ 1 + |t| := hzNorm
  have hreflectedNorm :
      ‖1 - smoothAFEZetaLeftLinePt t‖ ≤ 3 / 2 + |t| := by
    have hcoord :
        1 - smoothAFEZetaLeftLinePt t =
          (((3 / 2 : ℝ) : ℂ) - (t : ℂ) * I) := by
      unfold smoothAFEZetaLeftLinePt
      push_cast
      ring
    rw [hcoord]
    calc
      ‖(((3 / 2 : ℝ) : ℂ) - (t : ℂ) * I)‖ ≤
          ‖(((3 / 2 : ℝ) : ℂ))‖ + ‖(t : ℂ) * I‖ := norm_sub_le _ _
      _ = 3 / 2 + |t| := by
        rw [norm_mul, norm_I]
        norm_num
  have hsqrt :
      Real.sqrt (‖1 - smoothAFEZetaLeftLinePt t‖ + 2) ≤ 4 + |t| := by
    have hnonneg : 0 ≤ ‖1 - smoothAFEZetaLeftLinePt t‖ + 2 := by positivity
    have hone : 1 ≤ ‖1 - smoothAFEZetaLeftLinePt t‖ + 2 := by
      linarith [norm_nonneg (1 - smoothAFEZetaLeftLinePt t)]
    have hself :
        Real.sqrt (‖1 - smoothAFEZetaLeftLinePt t‖ + 2) ≤
          ‖1 - smoothAFEZetaLeftLinePt t‖ + 2 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith
    exact hself.trans <| by linarith [hreflectedNorm]
  calc
    ‖riemannZeta (smoothAFEZetaLeftLinePt t)‖ ≤
        (‖smoothAFEZetaLeftLinePt t‖ / (2 * Real.pi)) *
          (6 * Real.sqrt (‖1 - smoothAFEZetaLeftLinePt t‖ + 2)) :=
      norm_riemannZeta_smoothAFEZetaLeftLinePt_le t
    _ ≤ (1 + |t|) * (6 * (4 + |t|)) := by gcongr
    _ = 6 * (1 + |t|) * (4 + |t|) := by ring

theorem linePt_add_left_one_eq_smoothAFEZetaLeftLinePt
    (τ v : ℝ) :
    linePt τ + ((-1 : ℂ) + (v : ℂ) * I) =
      smoothAFEZetaLeftLinePt (τ + v) := by
  unfold linePt smoothAFEZetaLeftLinePt
  push_cast
  ring

/-- Pointwise Gaussian-polynomial majorant for the zeta-weighted left edge. -/
theorem norm_smoothAFEZetaMellinIntegrand_left_one_le
    {x : ℝ} (hx : 0 < x) (τ v : ℝ) :
    ‖smoothAFEZetaMellinIntegrand (linePt τ) x
        ((-1 : ℂ) + (v : ℂ) * I)‖ ≤
      (x⁻¹ * Real.exp 1 * (6 * (1 + |τ|) * (4 + |τ|))) *
        ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
  have hzeta :
      ‖riemannZeta
          (linePt τ + ((-1 : ℂ) + (v : ℂ) * I))‖ ≤
        6 * (1 + |τ| + |v|) * (4 + |τ| + |v|) := by
    rw [linePt_add_left_one_eq_smoothAFEZetaLeftLinePt]
    refine (norm_riemannZeta_smoothAFEZetaLeftLinePt_le_quadratic
      (τ + v)).trans ?_
    have habs : |τ + v| ≤ |τ| + |v| := abs_add_le τ v
    have hfirst : 1 + |τ + v| ≤ 1 + |τ| + |v| := by linarith
    have hsecond : 4 + |τ + v| ≤ 4 + |τ| + |v| := by linarith
    calc
      6 * (1 + |τ + v|) * (4 + |τ + v|)
          ≤ 6 * (1 + |τ| + |v|) * (4 + |τ + v|) := by gcongr
      _ ≤ 6 * (1 + |τ| + |v|) * (4 + |τ| + |v|) := by gcongr
  have hzetaSeparated :
      ‖riemannZeta
          (linePt τ + ((-1 : ℂ) + (v : ℂ) * I))‖ ≤
        (6 * (1 + |τ|) * (4 + |τ|)) * (1 + |v|) ^ 2 := by
    refine hzeta.trans ?_
    have hτ : 0 ≤ |τ| := abs_nonneg τ
    have hv : 0 ≤ |v| := abs_nonneg v
    have hfirst : 1 + |τ| + |v| ≤ (1 + |τ|) * (1 + |v|) := by
      nlinarith
    have hsecond : 4 + |τ| + |v| ≤ (4 + |τ|) * (1 + |v|) := by
      nlinarith
    calc
      6 * (1 + |τ| + |v|) * (4 + |τ| + |v|)
          ≤ 6 * ((1 + |τ|) * (1 + |v|)) *
              ((4 + |τ|) * (1 + |v|)) := by gcongr
      _ = (6 * (1 + |τ|) * (4 + |τ|)) * (1 + |v|) ^ 2 := by ring
  have hkernel :=
    norm_smoothAFEGaussianKernel_vertical_le_of_ne
      (σ := -1) (by norm_num) v
  have hkernel' :
      ‖smoothAFEGaussianKernel ((-1 : ℂ) + (v : ℂ) * I)‖ ≤
        Real.exp 1 * Real.exp (-(v ^ 2)) := by
    convert hkernel using 1 <;> norm_num
  rw [smoothAFEZetaMellinIntegrand, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  rw [show (((-1 : ℂ) + (v : ℂ) * I).re) = -1 by simp,
    Real.rpow_neg_one]
  calc
    ‖riemannZeta (linePt τ + (-1 + ↑v * I))‖ * x⁻¹ *
          ‖smoothAFEGaussianKernel (-1 + ↑v * I)‖
        ≤ ((6 * (1 + |τ|) * (4 + |τ|)) * (1 + |v|) ^ 2) *
          x⁻¹ * (Real.exp 1 * Real.exp (-(v ^ 2))) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right hzetaSeparated (by positivity))
            hkernel' (norm_nonneg _) (by positivity)
    _ = (x⁻¹ * Real.exp 1 * (6 * (1 + |τ|) * (4 + |τ|))) *
          ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by ring

/-- A quadratic polynomial times the standard Gaussian is integrable on the
whole real line. -/
theorem integrable_one_add_abs_sq_mul_exp_neg_sq :
    MeasureTheory.Integrable
      (fun v : ℝ => (1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
  have h0 : MeasureTheory.Integrable
      (fun v : ℝ => Real.exp (-1 * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have h1raw : MeasureTheory.Integrable
      (fun v : ℝ => v * Real.exp (-1 * v ^ 2)) :=
    integrable_mul_exp_neg_mul_sq (by norm_num)
  have h1 : MeasureTheory.Integrable
      (fun v : ℝ => |v| * Real.exp (-1 * v ^ 2)) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using h1raw.norm
  have h2 : MeasureTheory.Integrable
      (fun v : ℝ => v ^ 2 * Real.exp (-1 * v ^ 2)) := by
    simpa [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 2))
  have hsum := (h0.add (h1.const_mul 2)).add h2
  apply hsum.congr
  exact Filter.Eventually.of_forall fun v => by
    simp only [Pi.add_apply]
    rw [show -(v ^ 2) = -1 * v ^ 2 by ring]
    have hexpand : (1 + |v|) ^ 2 = 1 + 2 * |v| + v ^ 2 := by
      nlinarith [sq_abs v]
    rw [hexpand]
    ring

/-- The zeta-weighted Gaussian integrand is absolutely integrable on the full
left edge of the critical-line contour. -/
theorem smoothAFEZetaMellinIntegrand_left_one_verticalIntegrable
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    Complex.VerticalIntegrable
      (smoothAFEZetaMellinIntegrand (linePt τ) x) (-1) := by
  rw [Complex.VerticalIntegrable]
  apply MeasureTheory.Integrable.mono'
    (integrable_one_add_abs_sq_mul_exp_neg_sq.const_mul
      (x⁻¹ * Real.exp 1 * (6 * (1 + |τ|) * (4 + |τ|))))
  · haveI : NeZero (x : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hzetaContinuous : Continuous (fun v : ℝ =>
        riemannZeta
          (linePt τ + (((-1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro v
      apply (differentiableAt_riemannZeta ?_).continuousAt.comp
      · fun_prop
      · intro hpole
        have hre := congrArg Complex.re hpole
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
          sub_zero, add_zero, linePt_re, Complex.one_re] at hre
        norm_num at hre
    let w : ℝ → ℂ := fun v => ((-1 : ℝ) : ℂ) + (v : ℂ) * I
    have hw : Continuous w := by
      dsimp only [w]
      fun_prop
    have hwne : ∀ v : ℝ, w v ≠ 0 := by
      intro v hzero
      have hre := congrArg Complex.re hzero
      dsimp only [w] at hre
      simp at hre
    have hpow : Continuous (fun v : ℝ => (x : ℂ) ^ (w v)) :=
      (continuous_const_cpow (x : ℂ)).comp hw
    have hkernel : Continuous (fun v : ℝ => smoothAFEGaussianKernel (w v)) := by
      unfold smoothAFEGaussianKernel
      exact (Complex.continuous_exp.comp (hw.pow 2)).div hw hwne
    unfold smoothAFEZetaMellinIntegrand
    simpa only [w, Pi.mul_apply] using!
      ((hzetaContinuous.mul hpow).mul hkernel).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      simpa using norm_smoothAFEZetaMellinIntegrand_left_one_le hx τ v

end RHTower
