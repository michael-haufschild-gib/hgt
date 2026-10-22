import GaloisForLFunctions.RHTower.HardyThetaFourier
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCharacteristicMeromorphicLimit

/-!
# Hardy's theorem: infinitely many real zeros of the centered completed function

The theta source `hardySource` of the completed zeta transform is holomorphic on the strip
`|Im u| < π/2` and decays exponentially along every horizontal line of that strip, so its Fourier
transform is the completed zeta function on the critical line.  Inversion on each horizontal line
of the strip expresses the source as the transform of a real density built from `Ξ`.

If `Ξ` had only finitely many real zeros it would keep one sign on a half-line; the density would
then keep one sign on the tail, and the vertical growth of the inversion integral would be
controlled by a single value on the vertical axis.  Fatou's lemma converts that into an
exponential moment of the density, which bounds the source on the whole strip.  The Jacobi theta
transformation makes the source blow up as `log 2 + i y` approaches the boundary `y ↑ π/2`, a
contradiction.  Hence `Ξ` has real zeros above every height.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ## The real density of the critical-line transform -/

/-- The completed zeta function on the critical line is the elementary real multiple
`-2Ξ(t)/(t²+1/4)` of the detector. -/
theorem completedRiemannZeta_critical_eq_Xi (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I) = ((-2 * Xi t / (t ^ 2 + 1 / 4) : ℝ) : ℂ) := by
  have hne : ((t : ℂ) ^ 2 + 1 / 4) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, pow_two, Complex.mul_re] at hre
    nlinarith [sq_nonneg t]
  have hden1 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at hre
  have hden2 : (1 - (1 / 2 + (t : ℂ) * I)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re] at hre
    norm_num at hre
  have hpole : 1 / (1 / 2 + (t : ℂ) * I) + 1 / (1 - (1 / 2 + (t : ℂ) * I))
      = 1 / ((t : ℂ) ^ 2 + 1 / 4) := by
    rw [div_add_div _ _ hden1 hden2, div_eq_div_iff (mul_ne_zero hden1 hden2) hne]
    linear_combination ((t : ℂ) ^ 2) * Complex.I_sq
  have h0 := XiC_ofReal_eq_completedRiemannZeta₀ t
  rw [XiC_ofReal] at h0
  have hz := completedRiemannZeta_eq (1 / 2 + (t : ℂ) * I)
  rw [hz, show ∀ a b c : ℂ, a - b - c = a - (b + c) from fun a b c => by ring, hpole]
  set L := completedRiemannZeta₀ (1 / 2 + (t : ℂ) * I) with hL
  push_cast
  rw [eq_div_iff hne]
  linear_combination (2 : ℂ) * h0 - mul_inv_cancel₀ hne

/-- The real density whose Fourier transform is the theta source. -/
def hardyXiDensity (w : ℝ) : ℝ := -2 * Xi (4 * π * w) / ((4 * π * w) ^ 2 + 1 / 4)

theorem completedZetaFourier_eq_ofReal (w : ℝ) :
    completedZetaFourier w = ((hardyXiDensity w : ℝ) : ℂ) := by
  show completedRiemannZeta (1 / 2 + ((4 * π * w : ℝ) : ℂ) * I) = _
  rw [completedRiemannZeta_critical_eq_Xi (4 * π * w), hardyXiDensity]

theorem Xi_neg (t : ℝ) : Xi (-t) = Xi t := by
  have h := XiC_even (t : ℂ)
  rw [show (-(t : ℂ)) = ((-t : ℝ) : ℂ) by push_cast; ring, XiC_ofReal, XiC_ofReal] at h
  exact_mod_cast h

theorem hardyXiDensity_neg (w : ℝ) : hardyXiDensity (-w) = hardyXiDensity w := by
  rw [hardyXiDensity, hardyXiDensity, show 4 * π * -w = -(4 * π * w) by ring, Xi_neg]
  ring_nf

theorem continuous_hardyXiDensity : Continuous hardyXiDensity := by
  have hden : ∀ w : ℝ, ((4 * π * w) ^ 2 + 1 / 4) ≠ 0 := by
    intro w
    positivity
  refine Continuous.div ?_ (by fun_prop) hden
  exact (continuous_const.mul (continuous_Xi.comp (by fun_prop)))

theorem norm_completedZetaFourier_eq (w : ℝ) :
    ‖completedZetaFourier w‖ = |hardyXiDensity w| := by
  rw [completedZetaFourier_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]



/-! ## Numeric constants of the theta tail -/

theorem exp_one_gt_two : (2 : ℝ) < Real.exp 1 := by
  nlinarith [Real.exp_one_gt_d9]

theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, Real.exp_neg, ← one_div]
  have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) exp_one_gt_two.le
  linarith

theorem exp_neg_three_le_eighth : Real.exp (-3) ≤ 1 / 8 := by
  have h3 : Real.exp 3 = Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    rw [h3]
    nlinarith [exp_one_gt_two, Real.exp_pos (1 : ℝ)]
  rw [show (-3 : ℝ) = -(3 : ℝ) from rfl, Real.exp_neg, ← one_div]
  have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8) h8
  linarith

theorem jacobiThetaTailConstant_le_four : jacobiThetaTailConstant ≤ 4 := by
  have h1 : Real.exp (-π) ≤ Real.exp (-1) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-π) ≤ 1 / 2 := h1.trans exp_neg_one_le_half
  have h3 : (0 : ℝ) < 1 - Real.exp (-π) := by
    have := Real.exp_pos (-π)
    linarith
  rw [jacobiThetaTailConstant, div_le_iff₀ h3]
  linarith

/-- At height at least one the theta value is within `1/2` of its constant term. -/
theorem norm_jacobiTheta_sub_one_le_half {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ - 1‖ ≤ 1 / 2 := by
  refine (norm_jacobiTheta_sub_one_le' hτ).trans ?_
  have he : Real.exp (-π * τ.im) ≤ Real.exp (-3) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_gt_three, hτ]
  have hK := jacobiThetaTailConstant_le_four
  have hKpos := jacobiThetaTailConstant_pos
  calc jacobiThetaTailConstant * Real.exp (-π * τ.im)
      ≤ 4 * Real.exp (-3) :=
        mul_le_mul hK he (Real.exp_pos _).le (by norm_num)
    _ ≤ 1 / 2 := by
        have := exp_neg_three_le_eighth
        linarith

/-! ## The source stays bounded on the vertical axis -/

section AxisBound

/-- The theta argument attached to the vertical point `i y`, translated by the period. -/
def hardyAxisPoint (y : ℝ) : ℂ :=
  ((1 - Real.sin y : ℝ) : ℂ) + ((Real.cos y : ℝ) : ℂ) * I

theorem hardyAxisPoint_im (y : ℝ) : (hardyAxisPoint y).im = Real.cos y := by
  rw [hardyAxisPoint]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

theorem hardyAxisPoint_re (y : ℝ) : (hardyAxisPoint y).re = 1 - Real.sin y := by
  rw [hardyAxisPoint]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

theorem normSq_hardyAxisPoint (y : ℝ) :
    Complex.normSq (hardyAxisPoint y) = 2 * (1 - Real.sin y) := by
  rw [Complex.normSq_apply, hardyAxisPoint_re, hardyAxisPoint_im]
  nlinarith [Real.sin_sq_add_cos_sq y]

theorem I_mul_exp_axis (y : ℝ) :
    I * cexp ((y : ℂ) * I) = hardyAxisPoint y - 1 := by
  rw [Complex.exp_mul_I, hardyAxisPoint]
  push_cast
  linear_combination Complex.sin (y : ℂ) * Complex.I_sq

theorem jacobiTheta_hardyAxisPoint (y : ℝ) :
    jacobiTheta (I * cexp ((y : ℂ) * I)) = jacobiTheta (1 + hardyAxisPoint y) := by
  rw [I_mul_exp_axis]
  have h := jacobiTheta_two_add (hardyAxisPoint y - 1)
  rw [show (2 : ℂ) + (hardyAxisPoint y - 1) = 1 + hardyAxisPoint y by ring] at h
  exact h.symm

/-- Close to the boundary the translated axis argument has a very large imaginary height. -/
theorem four_le_im_div_normSq_hardyAxisPoint {y : ℝ} (hy2 : 63 / 65 ≤ Real.sin y)
    (hcos : 0 < Real.cos y) :
    4 ≤ (hardyAxisPoint y).im / Complex.normSq (hardyAxisPoint y) := by
  rw [hardyAxisPoint_im, normSq_hardyAxisPoint]
  have hs : Real.sin y < 1 := by
    rcases lt_or_ge (Real.sin y) 1 with h | h
    · exact h
    · exfalso
      have hsin1 : Real.sin y = 1 := le_antisymm (Real.sin_le_one y) h
      nlinarith [Real.sin_sq_add_cos_sq y, hcos]
  have hden : (0 : ℝ) < 2 * (1 - Real.sin y) := by linarith
  rw [le_div_iff₀ hden]
  have hpy : Real.cos y ^ 2 = 1 - Real.sin y ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq y]
  nlinarith [hpy, hcos, hy2, hs]

/-- The crude arithmetic behind the boundary bound: the reciprocal exponential of the height
beats the half-power divergence of the radius. -/
theorem theta_axis_bound_arith {r c K M : ℝ} (hr : 0 < r) (hrle : r ≤ 1 / 2) (hc : 0 < c)
    (hK : 0 < K) (hK4 : K ≤ 4) (hMval : M = c / r ^ 2) (hcr : 2 * r ≤ π * c) :
    r ^ (-(1 / 2) : ℝ) * (2 * K * Real.exp (-π * M / 4)) ≤ 32 := by
  have hpi := Real.pi_gt_three
  have hMpos : 0 < M := by rw [hMval]; positivity
  have hexp : Real.exp (-π * M / 4) ≤ 4 / (π * M) := by
    have hpos : 0 < π * M / 4 := by positivity
    have hle : π * M / 4 ≤ Real.exp (π * M / 4) := by
      have := Real.add_one_le_exp (π * M / 4)
      linarith
    have hexppos : 0 < Real.exp (π * M / 4) := Real.exp_pos _
    rw [show -π * M / 4 = -(π * M / 4) by ring, Real.exp_neg]
    rw [inv_le_iff_one_le_mul₀ hexppos, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity : (0:ℝ) < π * M)]
    nlinarith [hle, hpos]
  have h2 : 4 / (π * M) ≤ 2 * r := by
    rw [hMval]
    have hpos : (0:ℝ) < π * (c / r ^ 2) := by positivity
    rw [div_le_iff₀ hpos]
    have hexpand : 2 * r * (π * (c / r ^ 2)) = 2 * π * c / r := by
      field_simp
    rw [hexpand, le_div_iff₀ hr]
    nlinarith [hcr]
  have hstep : r ^ (-(1 / 2) : ℝ) * (2 * K * Real.exp (-π * M / 4))
      ≤ r ^ (-(1 / 2) : ℝ) * (2 * K * (2 * r)) := by
    have hrp : (0:ℝ) ≤ r ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hr.le _
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hexp.trans h2) (by positivity)) hrp
  refine hstep.trans ?_
  have hrp : r ^ (-(1 / 2) : ℝ) = (Real.sqrt r)⁻¹ := by
    rw [Real.rpow_neg hr.le, Real.sqrt_eq_rpow]
  rw [hrp]
  have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  have hsqpos : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hval : (Real.sqrt r)⁻¹ * (2 * K * (2 * r)) = 4 * K * Real.sqrt r := by
    field_simp
    nlinarith [hsq]
  rw [hval]
  have hsr1 : Real.sqrt r ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by linarith)
  nlinarith [hsr1, hK4, hK, hsqpos]

/-- **Boundary boundedness on the vertical axis.**  Near the boundary the theta value along the
vertical approach stays bounded. -/
theorem norm_jacobiTheta_axis_le {y : ℝ} (hy2 : 63 / 65 ≤ Real.sin y) (hcos : 0 < Real.cos y) :
    ‖jacobiTheta (I * cexp ((y : ℂ) * I))‖ ≤ 32 := by
  have him : 0 < (hardyAxisPoint y).im := by rw [hardyAxisPoint_im]; exact hcos
  have hM := four_le_im_div_normSq_hardyAxisPoint hy2 hcos
  have hb := norm_jacobiTheta_one_add_le him hM
  rw [← jacobiTheta_hardyAxisPoint] at hb
  refine hb.trans ?_
  have hrpos : 0 < ‖hardyAxisPoint y‖ := by
    rw [norm_pos_iff]
    intro h
    rw [h] at him
    simp at him
  have hr2 : ‖hardyAxisPoint y‖ ^ 2 = 2 * (1 - Real.sin y) := by
    rw [Complex.sq_norm, normSq_hardyAxisPoint]
  have hs : Real.sin y < 1 := by nlinarith [hr2, hrpos]
  have hMval : (hardyAxisPoint y).im / Complex.normSq (hardyAxisPoint y)
      = Real.cos y / ‖hardyAxisPoint y‖ ^ 2 := by
    rw [hardyAxisPoint_im, Complex.sq_norm]
  have hrle : ‖hardyAxisPoint y‖ ≤ 1 / 2 := by
    nlinarith [hr2, hy2, hrpos]
  have hc2 : Real.cos y ^ 2 = (1 - Real.sin y) * (1 + Real.sin y) := by
    nlinarith [Real.sin_sq_add_cos_sq y]
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3:ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3 / 2)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2pos : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcr0 : ‖hardyAxisPoint y‖ ≤ Real.cos y * Real.sqrt 2 := by
    have hge : ‖hardyAxisPoint y‖ ^ 2 ≤ (Real.cos y * Real.sqrt 2) ^ 2 := by
      rw [mul_pow, hsqrt2sq, hr2, hc2]
      nlinarith [Real.neg_one_le_sin y, hs]
    nlinarith [hge, hrpos, mul_pos hcos hsqrt2pos]
  have hcr : 2 * ‖hardyAxisPoint y‖ ≤ π * Real.cos y := by
    nlinarith [hcr0, hsqrt2, Real.pi_gt_three, hcos]
  exact theta_axis_bound_arith hrpos hrle hcos jacobiThetaTailConstant_pos
    jacobiThetaTailConstant_le_four hMval hcr

/-- The theta source is bounded along the vertical approach to the boundary. -/
theorem norm_hardySource_axis_le {y : ℝ} (hy2 : 63 / 65 ≤ Real.sin y) (hcos : 0 < Real.cos y) :
    ‖hardySource ((y : ℂ) * I)‖ ≤ 17 := by
  have hθ := norm_jacobiTheta_axis_le hy2 hcos
  have hnorm1 : ‖cexp ((y : ℂ) * I / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    rw [show ((y : ℂ) * I / 4).re = 0 by
      simp only [Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero,
        Complex.normSq_apply]
      norm_num]
    exact Real.exp_zero
  have hnorm2 : ‖cexp (-((y : ℂ) * I) / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    rw [show (-((y : ℂ) * I) / 4).re = 0 by
      simp only [Complex.div_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
        Complex.normSq_apply]
      norm_num]
    exact Real.exp_zero
  have hsrc : hardySource ((y : ℂ) * I)
      = (cexp ((y : ℂ) * I / 4) * (jacobiTheta (I * cexp ((y : ℂ) * I)) - 1)
          - cexp (-((y : ℂ) * I) / 4)) / 2 := by
    rw [hardySource]
  rw [hsrc, norm_div]
  have hnum : ‖cexp ((y : ℂ) * I / 4) * (jacobiTheta (I * cexp ((y : ℂ) * I)) - 1)
      - cexp (-((y : ℂ) * I) / 4)‖ ≤ 34 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, hnorm1, hnorm2, one_mul]
    have : ‖jacobiTheta (I * cexp ((y : ℂ) * I)) - 1‖ ≤ 33 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      linarith
    linarith
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  linarith [hnum]

end AxisBound


/-! ## The inversion integral in real form -/

section RealForm

theorem integrable_exp_mul_hardyXiDensity {y : ℝ} (hy : |y| < π / 2) :
    Integrable (fun w : ℝ => Real.exp (-(2 * π * y * w)) * hardyXiDensity w) := by
  have hpi := Real.pi_pos
  have hya := abs_nonneg y
  set c : ℝ := (|y| + π / 2) / 2 with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hcy : |y| < c := by rw [hc]; linarith
  have hclt : c < π / 2 := by rw [hc]; linarith
  have hbound := integrable_completedZetaFourier_mul_exp hc0 hclt hcy
  refine Integrable.mono' hbound ?_ ?_
  · exact ((by fun_prop : Continuous fun w : ℝ => Real.exp (-(2 * π * y * w))).mul
      continuous_hardyXiDensity).aestronglyMeasurable
  · filter_upwards with w
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), norm_completedZetaFourier_eq]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Real.exp_le_exp]
    have h1 : -(y * w) ≤ |y * w| := neg_le_abs _
    have h2 : |y * w| = |y| * |w| := abs_mul y w
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * π)
    nlinarith [h3, h2]

theorem hardySource_axis_eq_ofReal {y : ℝ} (hy0 : 0 ≤ y) (hy : y < π / 2) :
    hardySource ((y : ℂ) * I)
      = ((∫ w : ℝ, Real.exp (-(2 * π * y * w)) * hardyXiDensity w : ℝ) : ℂ) := by
  rw [hardySource_imaginary_eq_integral hy0 hy, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards with w
  rw [completedZetaFourier_eq_ofReal]
  push_cast
  ring

theorem integral_exp_hardyXiDensity_neg (y : ℝ) :
    (∫ w : ℝ, Real.exp (-(2 * π * y * w)) * hardyXiDensity w)
      = ∫ w : ℝ, Real.exp (2 * π * y * w) * hardyXiDensity w := by
  have h := integral_neg_eq_self
    (fun w : ℝ => Real.exp (2 * π * y * w) * hardyXiDensity w) volume
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with w
  rw [hardyXiDensity_neg]
  congr 2
  ring

theorem integral_cosh_hardyXiDensity {y : ℝ} (hy : |y| < π / 2) :
    (∫ w : ℝ, Real.exp (-(2 * π * y * w)) * hardyXiDensity w)
      = ∫ w : ℝ, Real.cosh (2 * π * y * w) * hardyXiDensity w := by
  have h1 := integrable_exp_mul_hardyXiDensity hy
  have h2 : Integrable (fun w : ℝ => Real.exp (2 * π * y * w) * hardyXiDensity w) := by
    have h := integrable_exp_mul_hardyXiDensity (y := -y) (by rwa [abs_neg])
    refine h.congr ?_
    filter_upwards with w
    congr 2
    ring
  have hsym := integral_exp_hardyXiDensity_neg y
  have hpoint : ∀ w : ℝ, Real.cosh (2 * π * y * w) * hardyXiDensity w
      = (Real.exp (-(2 * π * y * w)) * hardyXiDensity w
        + Real.exp (2 * π * y * w) * hardyXiDensity w) / 2 := by
    intro w
    rw [Real.cosh_eq]
    ring
  rw [show (∫ w : ℝ, Real.cosh (2 * π * y * w) * hardyXiDensity w)
      = ∫ w : ℝ, (Real.exp (-(2 * π * y * w)) * hardyXiDensity w
        + Real.exp (2 * π * y * w) * hardyXiDensity w) / 2 from
    integral_congr_ae (by filter_upwards with w using hpoint w)]
  rw [integral_div, integral_add h1 h2, ← hsym]
  ring

/-- The vertical values of the source are the symmetric moments of the density. -/
theorem abs_integral_cosh_hardyXiDensity_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y < π / 2)
    (hy2 : 63 / 65 ≤ Real.sin y) (hcos : 0 < Real.cos y) :
    |∫ w : ℝ, Real.cosh (2 * π * y * w) * hardyXiDensity w| ≤ 17 := by
  have habs : |y| < π / 2 := by rw [abs_of_nonneg hy0]; exact hy
  have h := norm_hardySource_axis_le hy2 hcos
  rw [hardySource_axis_eq_ofReal hy0 hy, Complex.norm_real, Real.norm_eq_abs,
    integral_cosh_hardyXiDensity habs] at h
  exact h

end RealForm


/-! ## A one-signed tail forces an exponential moment -/

section TailSign

/-- Under a one-signed tail the density has an exponential moment of rate `π²`. -/
theorem integrable_exp_pi_sq_mul_abs_hardyXiDensity
    {W σ : ℝ} (hW : 0 < W) (hσ : |σ| = 1)
    (hsign : ∀ w : ℝ, W ≤ |w| → 0 ≤ σ * hardyXiDensity w) :
    Integrable (fun w : ℝ => Real.exp (π ^ 2 * |w|) * |hardyXiDensity w|) := by
  have hpi := Real.pi_pos
  set S : Set ℝ := {w : ℝ | W ≤ |w|} with hS
  have hSmeas : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  have hmidsub : Sᶜ ⊆ Set.Icc (-W) W := by
    intro w hw
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hw
    exact ⟨by linarith [neg_abs_le w], by linarith [le_abs_self w]⟩
  have hmidint : IntegrableOn (fun w : ℝ => |hardyXiDensity w|) Sᶜ :=
    IntegrableOn.mono_set (continuous_hardyXiDensity.abs.integrableOn_Icc) hmidsub
  set B₀ : ℝ := Real.cosh (π ^ 2 * W) * ∫ w in Sᶜ, |hardyXiDensity w| with hB₀def
  have hintnn : (0 : ℝ) ≤ ∫ w in Sᶜ, |hardyXiDensity w| :=
    integral_nonneg_of_ae (by filter_upwards with w using abs_nonneg _)
  have hB₀nn : 0 ≤ B₀ := mul_nonneg (Real.cosh_pos _).le hintnn
  -- the cosh moments are globally integrable
  have hcoshint : ∀ y : ℝ, |y| < π / 2 →
      Integrable (fun w : ℝ => Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w)) := by
    intro y hy
    have h1 := integrable_exp_mul_hardyXiDensity hy
    have h2 : Integrable (fun w : ℝ => Real.exp (2 * π * y * w) * hardyXiDensity w) := by
      have h := integrable_exp_mul_hardyXiDensity (y := -y) (by rwa [abs_neg])
      refine h.congr ?_
      filter_upwards with w
      congr 2
      ring
    refine (((h1.add h2).div_const 2).const_mul σ).congr ?_
    filter_upwards with w
    simp only [Pi.add_apply]
    rw [Real.cosh_eq]
    ring
  -- the middle contribution is uniformly small
  have hmidbound : ∀ y : ℝ, 0 ≤ y → y < π / 2 →
      |∫ w in Sᶜ, Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w)| ≤ B₀ := by
    intro y hy0 hy
    have habs : |y| < π / 2 := by rwa [abs_of_nonneg hy0]
    have hint := (hcoshint y habs).restrict (s := Sᶜ)
    refine (abs_integral_le_integral_abs).trans ?_
    rw [hB₀def, ← integral_const_mul]
    refine integral_mono_ae hint.abs (hmidint.const_mul _) ?_
    filter_upwards [ae_restrict_mem hSmeas.compl] with w hw
    show |Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w)|
      ≤ Real.cosh (π ^ 2 * W) * |hardyXiDensity w|
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hw
    rw [abs_mul, abs_mul, hσ, one_mul, abs_of_pos (Real.cosh_pos _)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : (0:ℝ) ≤ π ^ 2 * W)]
    rw [show |2 * π * y * w| = 2 * π * y * |w| by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * π * y)]]
    have hyw : y * |w| ≤ π / 2 * W :=
      mul_le_mul hy.le hw.le (abs_nonneg w) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hyw (by positivity : (0:ℝ) ≤ 2 * π)]
  -- the tail bound, uniform in the height
  set B : ℝ := 17 + B₀ with hBdef
  have htail : ∀ y : ℝ, 0 ≤ y → y < π / 2 → 63 / 65 ≤ Real.sin y → 0 < Real.cos y →
      (∫ w in S, Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w)) ≤ B := by
    intro y hy0 hy hsin hcos
    have habs : |y| < π / 2 := by rwa [abs_of_nonneg hy0]
    have hint := hcoshint y habs
    have hsplit := integral_add_compl hSmeas hint
    have hglobal : |∫ w : ℝ, Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w)| ≤ 17 := by
      have hpull : (∫ w : ℝ, Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w))
          = σ * ∫ w : ℝ, Real.cosh (2 * π * y * w) * hardyXiDensity w := by
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards with w
        ring
      rw [hpull, abs_mul, hσ, one_mul]
      exact abs_integral_cosh_hardyXiDensity_le hy0 hy hsin hcos
    have hmid := hmidbound y hy0 hy
    have h1 := abs_le.1 hglobal
    have h2 := abs_le.1 hmid
    rw [hBdef]
    linarith [hsplit, h1.2, h2.1]
  -- Fatou in the height
  set G : ℝ → ℝ := fun w => Real.cosh (π ^ 2 * w) * (σ * hardyXiDensity w) with hGdef
  have hGcont : Continuous G :=
    (Real.continuous_cosh.comp (by fun_prop)).mul (continuous_const.mul continuous_hardyXiDensity)
  have hGnn : ∀ w ∈ S, 0 ≤ G w := by
    intro w hw
    simp only [hS, Set.mem_setOf_eq] at hw
    exact mul_nonneg (Real.cosh_pos _).le (hsign w hw)
  have hsintendsto : Tendsto (fun y : ℝ => Real.sin y) (𝓝[<] (π / 2)) (𝓝 1) := by
    have h : Tendsto (fun y : ℝ => Real.sin y) (𝓝 (π / 2)) (𝓝 (Real.sin (π / 2))) :=
      Real.continuous_sin.tendsto _
    rw [Real.sin_pi_div_two] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hfatou : ∫⁻ w in S, ENNReal.ofReal (G w) ≤ ENNReal.ofReal B := by
    set f : ℝ → ℝ → ENNReal := fun y w =>
      ENNReal.ofReal (Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w)) with hfdef
    have hmeas : ∀ y : ℝ, Measurable (f y) := by
      intro y
      exact ENNReal.measurable_ofReal.comp
        ((Real.continuous_cosh.comp (by fun_prop)).mul
          (continuous_const.mul continuous_hardyXiDensity)).measurable
    have hlim := lintegral_liminf_le (μ := volume.restrict S) (u := 𝓝[<] (π / 2)) hmeas
    have hpt : ∀ w : ℝ, liminf (fun y : ℝ => f y w) (𝓝[<] (π / 2)) = ENNReal.ofReal (G w) := by
      intro w
      refine Filter.Tendsto.liminf_eq ?_
      have hc : Continuous fun y : ℝ => Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w) :=
        (Real.continuous_cosh.comp (by fun_prop)).mul continuous_const
      have h : Tendsto (fun y : ℝ => ENNReal.ofReal
          (Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w))) (𝓝[<] (π / 2))
          (𝓝 (ENNReal.ofReal (Real.cosh (2 * π * (π / 2) * w) * (σ * hardyXiDensity w)))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp
          ((hc.tendsto (π / 2)).mono_left nhdsWithin_le_nhds)
      rw [hGdef]
      simpa [hfdef, show 2 * π * (π / 2) * w = π ^ 2 * w by ring] using h
    calc ∫⁻ w in S, ENNReal.ofReal (G w)
        = ∫⁻ w in S, liminf (fun y : ℝ => f y w) (𝓝[<] (π / 2)) := by
          refine lintegral_congr ?_
          intro w
          rw [hpt w]
      _ ≤ liminf (fun y : ℝ => ∫⁻ w in S, f y w) (𝓝[<] (π / 2)) := hlim
      _ ≤ ENNReal.ofReal B := by
          refine liminf_le_of_frequently_le (Filter.Eventually.frequently ?_)
          filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < π / 2 by positivity),
            hsintendsto.eventually (eventually_gt_nhds (by norm_num : (63:ℝ) / 65 < 1))]
            with y hy hy2
          have hcos : 0 < Real.cos y :=
            Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩
          have hIntOn : IntegrableOn
              (fun w : ℝ => Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w)) S :=
            (hcoshint y (by rw [abs_of_nonneg hy.1.le]; exact hy.2)).restrict
          have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict S]
              fun w : ℝ => Real.cosh (2 * π * y * w) * (σ * hardyXiDensity w) := by
            filter_upwards [ae_restrict_mem hSmeas] with w hw
            simp only [hS, Set.mem_setOf_eq] at hw
            exact mul_nonneg (Real.cosh_pos _).le (hsign w hw)
          have hofreal := ofReal_integral_eq_lintegral_ofReal hIntOn hnn
          rw [hfdef, ← hofreal]
          exact ENNReal.ofReal_le_ofReal (htail y hy.1.le hy.2 hy2.le hcos)
  -- the exponential moment on the tail
  have hGint : IntegrableOn G S := by
    refine ⟨hGcont.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have heq : ∫⁻ w in S, ENNReal.ofReal ‖G w‖ = ∫⁻ w in S, ENNReal.ofReal (G w) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem hSmeas] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (hGnn w hw)]
    rw [heq]
    exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  have hmomcont : Continuous fun w : ℝ => Real.exp (π ^ 2 * |w|) * |hardyXiDensity w| :=
    (by fun_prop : Continuous fun w : ℝ => Real.exp (π ^ 2 * |w|)).mul
      continuous_hardyXiDensity.abs
  have hSint : IntegrableOn (fun w : ℝ => Real.exp (π ^ 2 * |w|) * |hardyXiDensity w|) S := by
    refine Integrable.mono' (hGint.const_mul 2) hmomcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem hSmeas] with w hw
    show ‖Real.exp (π ^ 2 * |w|) * |hardyXiDensity w|‖ ≤ 2 * G w
    simp only [hS, Set.mem_setOf_eq] at hw
    have habsval : |hardyXiDensity w| = σ * hardyXiDensity w := by
      have h1 : |σ * hardyXiDensity w| = σ * hardyXiDensity w := abs_of_nonneg (hsign w hw)
      rw [abs_mul, hσ, one_mul] at h1
      exact h1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), habsval, hGdef]
    have hexp : Real.exp (π ^ 2 * |w|) ≤ 2 * Real.cosh (π ^ 2 * w) := by
      rw [Real.cosh_eq]
      rcases abs_cases w with ⟨h, _⟩ | ⟨h, _⟩
      · rw [show π ^ 2 * |w| = π ^ 2 * w by rw [h]]
        nlinarith [Real.exp_pos (π ^ 2 * w), Real.exp_pos (-(π ^ 2 * w))]
      · rw [show π ^ 2 * |w| = -(π ^ 2 * w) by rw [h]; ring]
        nlinarith [Real.exp_pos (π ^ 2 * w), Real.exp_pos (-(π ^ 2 * w))]
    have hnn := hsign w hw
    nlinarith [mul_le_mul_of_nonneg_right hexp hnn]
  have hScint : IntegrableOn (fun w : ℝ => Real.exp (π ^ 2 * |w|) * |hardyXiDensity w|) Sᶜ := by
    refine Integrable.mono' (hmidint.const_mul (Real.exp (π ^ 2 * W)))
      hmomcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem hSmeas.compl] with w hw
    show ‖Real.exp (π ^ 2 * |w|) * |hardyXiDensity w|‖
      ≤ Real.exp (π ^ 2 * W) * |hardyXiDensity w|
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hw
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Real.exp_le_exp]
    nlinarith [hw.le, sq_nonneg π, hpi]
  have hunion := hSint.union hScint
  rw [Set.union_compl_self, integrableOn_univ] at hunion
  exact hunion

end TailSign


/-! ## Boundary blow-up of the theta source -/

section BlowUp

/-- The theta argument attached to the boundary point `log 2 + i y`, translated by the period. -/
def hardyBoundaryPoint (y : ℝ) : ℂ :=
  ((2 - 2 * Real.sin y : ℝ) : ℂ) + ((2 * Real.cos y : ℝ) : ℂ) * I

theorem hardyBoundaryPoint_im (y : ℝ) : (hardyBoundaryPoint y).im = 2 * Real.cos y := by
  rw [hardyBoundaryPoint]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

theorem hardyBoundaryPoint_re (y : ℝ) : (hardyBoundaryPoint y).re = 2 - 2 * Real.sin y := by
  rw [hardyBoundaryPoint]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

theorem normSq_hardyBoundaryPoint (y : ℝ) :
    Complex.normSq (hardyBoundaryPoint y) = 8 * (1 - Real.sin y) := by
  rw [Complex.normSq_apply, hardyBoundaryPoint_re, hardyBoundaryPoint_im]
  nlinarith [Real.sin_sq_add_cos_sq y]

theorem I_mul_exp_logTwo (y : ℝ) :
    I * cexp ((Real.log 2 : ℂ) + (y : ℂ) * I) = hardyBoundaryPoint y - 2 := by
  have h2 : cexp ((Real.log 2 : ℂ)) = (2 : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [Complex.exp_add, h2, Complex.exp_mul_I, hardyBoundaryPoint]
  push_cast
  linear_combination (2 * Complex.sin (y : ℂ)) * Complex.I_sq

theorem jacobiTheta_hardyBoundaryPoint (y : ℝ) :
    jacobiTheta (I * cexp ((Real.log 2 : ℂ) + (y : ℂ) * I))
      = jacobiTheta (hardyBoundaryPoint y) := by
  rw [I_mul_exp_logTwo]
  have := jacobiTheta_two_add (hardyBoundaryPoint y - 2)
  rw [show (2 : ℂ) + (hardyBoundaryPoint y - 2) = hardyBoundaryPoint y by ring] at this
  exact this.symm

/-- Below the boundary the translated theta argument sits high above the real axis. -/
theorem one_le_im_neg_inv_hardyBoundaryPoint {y : ℝ} (_hy1 : y < π / 2)
    (hy2 : 15 / 16 ≤ Real.sin y) (hcos : 0 < Real.cos y) :
    1 ≤ (-(hardyBoundaryPoint y)⁻¹).im := by
  rw [im_neg_inv, hardyBoundaryPoint_im, normSq_hardyBoundaryPoint]
  have hs : Real.sin y < 1 := by
    rcases lt_or_ge (Real.sin y) 1 with h | h
    · exact h
    · exfalso
      have h1 : Real.sin y ≤ 1 := Real.sin_le_one y
      have hsin1 : Real.sin y = 1 := le_antisymm h1 h
      have := Real.sin_sq_add_cos_sq y
      nlinarith [hcos]
  have hden : (0 : ℝ) < 8 * (1 - Real.sin y) := by linarith
  rw [le_div_iff₀ hden]
  have hpy : Real.cos y ^ 2 = 1 - Real.sin y ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq y]
  nlinarith [hpy, hcos, hy2, hs]

theorem norm_hardySource_logTwo_ge {y : ℝ} (hy0 : 0 < y) (hy1 : y < π / 2)
    (hy2 : 15 / 16 ≤ Real.sin y) :
    (1 / 2 * ‖hardyBoundaryPoint y‖ ^ (-(1 / 2) : ℝ) - 2) / 2
      ≤ ‖hardySource ((Real.log 2 : ℂ) + (y : ℂ) * I)‖ := by
  have hcos : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy1⟩
  have him : 0 < (hardyBoundaryPoint y).im := by
    rw [hardyBoundaryPoint_im]; linarith
  have hsmall : ‖jacobiTheta (-(hardyBoundaryPoint y)⁻¹) - 1‖ ≤ 1 / 2 :=
    norm_jacobiTheta_sub_one_le_half (one_le_im_neg_inv_hardyBoundaryPoint hy1 hy2 hcos)
  have hlow := le_norm_jacobiTheta him hsmall
  set u : ℂ := (Real.log 2 : ℂ) + (y : ℂ) * I with hu
  have hure : u.re = Real.log 2 := by
    rw [hu]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hA : (1 : ℝ) ≤ ‖cexp (u / 4)‖ := by
    rw [Complex.norm_exp]
    rw [Real.one_le_exp_iff]
    rw [show (u / 4).re = u.re / 4 by simp]
    rw [hure]
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hB : ‖cexp (-u / 4)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    rw [Real.exp_le_one_iff]
    rw [show (-u / 4).re = -u.re / 4 by simp]
    rw [hure]
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hsrc : hardySource u
      = (cexp (u / 4) * (jacobiTheta (hardyBoundaryPoint y) - 1) - cexp (-u / 4)) / 2 := by
    rw [hardySource, jacobiTheta_hardyBoundaryPoint]
  have htri : ‖cexp (u / 4)‖ * ‖jacobiTheta (hardyBoundaryPoint y) - 1‖ -
      ‖cexp (-u / 4)‖ ≤ ‖hardySource u‖ * 2 := by
    have h1 : ‖cexp (u / 4) * (jacobiTheta (hardyBoundaryPoint y) - 1)
        - cexp (-u / 4)‖ = ‖hardySource u‖ * 2 := by
      rw [hsrc, norm_div]
      simp
    rw [← h1, ← norm_mul]
    exact norm_sub_norm_le _ _
  have hthetatri : ‖jacobiTheta (hardyBoundaryPoint y)‖ - 1
      ≤ ‖jacobiTheta (hardyBoundaryPoint y) - 1‖ := by
    have := norm_sub_norm_le (jacobiTheta (hardyBoundaryPoint y)) (1 : ℂ)
    simpa using this
  have hBnn : (0 : ℝ) ≤ ‖jacobiTheta (hardyBoundaryPoint y) - 1‖ := norm_nonneg _
  nlinarith [htri, hthetatri, hlow, hA, hB, hBnn,
    mul_le_mul_of_nonneg_right hA hBnn]

theorem tendsto_hardyBoundaryPoint :
    Tendsto (fun y : ℝ => ‖hardyBoundaryPoint y‖) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
  have hsin : Tendsto (fun y : ℝ => Real.sin y) (𝓝[<] (π / 2)) (𝓝 1) := by
    have : Tendsto (fun y : ℝ => Real.sin y) (𝓝 (π / 2)) (𝓝 (Real.sin (π / 2))) :=
      (Real.continuous_sin.tendsto _)
    rw [Real.sin_pi_div_two] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hcos : Tendsto (fun y : ℝ => Real.cos y) (𝓝[<] (π / 2)) (𝓝 0) := by
    have : Tendsto (fun y : ℝ => Real.cos y) (𝓝 (π / 2)) (𝓝 (Real.cos (π / 2))) :=
      (Real.continuous_cos.tendsto _)
    rw [Real.cos_pi_div_two] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hv : Tendsto (fun y : ℝ => hardyBoundaryPoint y) (𝓝[<] (π / 2)) (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => ((2 - 2 * Real.sin y : ℝ) : ℂ)) (𝓝[<] (π / 2)) (𝓝 0) := by
      have : Tendsto (fun y : ℝ => (2 - 2 * Real.sin y : ℝ)) (𝓝[<] (π / 2)) (𝓝 0) := by
        have := (tendsto_const_nhds (x := (2 : ℝ)) (f := 𝓝[<] (π / 2))).sub
          (hsin.const_mul 2)
        simpa using this
      exact (Complex.continuous_ofReal.tendsto 0).comp this |>.congr' (by
        filter_upwards with y using rfl) |>.congr (fun y => rfl) |>.mono_right (by
          simp)
    have h2 : Tendsto (fun y : ℝ => ((2 * Real.cos y : ℝ) : ℂ) * I) (𝓝[<] (π / 2)) (𝓝 0) := by
      have : Tendsto (fun y : ℝ => (2 * Real.cos y : ℝ)) (𝓝[<] (π / 2)) (𝓝 0) := by
        simpa using hcos.const_mul 2
      have h3 := (Complex.continuous_ofReal.tendsto 0).comp this
      simp only [Complex.ofReal_zero] at h3
      simpa using h3.mul_const I
    have := h1.add h2
    simpa [hardyBoundaryPoint] using this
  have hnorm : Tendsto (fun y : ℝ => ‖hardyBoundaryPoint y‖) (𝓝[<] (π / 2)) (𝓝 0) := by
    have h := (continuous_norm.tendsto (0 : ℂ)).comp hv
    rw [norm_zero] at h
    exact h
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hnorm ?_
  have hmem : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) := Ioo_mem_nhdsLT (by positivity)
  filter_upwards [hmem] with y hy
  have hcosy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩
  have : hardyBoundaryPoint y ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [hardyBoundaryPoint_im] at this
    simp at this
    linarith
  simpa [norm_pos_iff] using this

/-- **Boundary blow-up.**  The theta source is unbounded along the vertical approach to the
boundary point `log 2 + iπ/2`. -/
theorem tendsto_norm_hardySource_logTwo_atTop :
    Tendsto (fun y : ℝ => ‖hardySource ((Real.log 2 : ℂ) + (y : ℂ) * I)‖)
      (𝓝[<] (π / 2)) atTop := by
  have hinv : Tendsto (fun y : ℝ => (Real.sqrt ‖hardyBoundaryPoint y‖)⁻¹)
      (𝓝[<] (π / 2)) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (Real.continuous_sqrt.tendsto 0).comp
        (tendsto_hardyBoundaryPoint.mono_right nhdsWithin_le_nhds)
      rw [Real.sqrt_zero] at h
      exact h
    · filter_upwards [tendsto_hardyBoundaryPoint.eventually_mem
        (self_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0))] with y hy
      exact Real.sqrt_pos.2 hy
  have hlow : Tendsto (fun y : ℝ => (1 / 2 * (Real.sqrt ‖hardyBoundaryPoint y‖)⁻¹ - 2) / 2)
      (𝓝[<] (π / 2)) atTop := by
    exact ((hinv.const_mul_atTop (by norm_num : (0:ℝ) < 1/2)).atTop_add
      tendsto_const_nhds).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hlow
  have hsin : Tendsto (fun y : ℝ => Real.sin y) (𝓝[<] (π / 2)) (𝓝 1) := by
    have : Tendsto (fun y : ℝ => Real.sin y) (𝓝 (π / 2)) (𝓝 (Real.sin (π / 2))) :=
      (Real.continuous_sin.tendsto _)
    rw [Real.sin_pi_div_two] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hmem : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) := Ioo_mem_nhdsLT (by positivity)
  filter_upwards [hmem, hsin.eventually (eventually_gt_nhds (by norm_num : (15:ℝ)/16 < 1))]
    with y hy hy2'
  have hy2 : (15 : ℝ) / 16 ≤ Real.sin y := hy2'.le
  have h := norm_hardySource_logTwo_ge hy.1 hy.2 hy2
  refine le_trans (le_of_eq ?_) h
  congr 2
  rw [Real.rpow_neg (norm_nonneg _), Real.sqrt_eq_rpow]

end BlowUp


/-! ## Hardy's theorem -/

section Hardy

/-- A one-signed tail of the density is impossible: it would bound the source on the whole strip,
contradicting the boundary blow-up. -/
theorem false_of_hardyXiDensity_tail_sign
    {W σ : ℝ} (hW : 0 < W) (hσ : |σ| = 1)
    (hsign : ∀ w : ℝ, W ≤ |w| → 0 ≤ σ * hardyXiDensity w) : False := by
  have hpi := Real.pi_pos
  have hmom := integrable_exp_pi_sq_mul_abs_hardyXiDensity hW hσ hsign
  set M : ℝ := ∫ w : ℝ, Real.exp (π ^ 2 * |w|) * |hardyXiDensity w| with hM
  have hexple : ∀ y : ℝ, 0 ≤ y → y < π / 2 → ∀ w : ℝ,
      Real.exp (-(2 * π * y * w)) ≤ Real.exp (π ^ 2 * |w|) := by
    intro y hy0 hy w
    rw [Real.exp_le_exp]
    have h1 : -w ≤ |w| := neg_le_abs w
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * π * y)
    have h3 : 2 * π * y ≤ π ^ 2 := by nlinarith [hy, hpi]
    have h4 := mul_le_mul_of_nonneg_right h3 (abs_nonneg w)
    nlinarith [h2, h4]
  have hbound : ∀ y : ℝ, 0 ≤ y → y < π / 2 → ∀ a : ℝ,
      ‖hardySource ((a : ℂ) + (y : ℂ) * I)‖ ≤ M := by
    intro y hy0 hy a
    refine (norm_hardySource_line_le hy0 hy a).trans ?_
    rw [hM]
    refine integral_mono ?_ hmom ?_
    · refine Integrable.mono' hmom ?_ ?_
      · exact ((by fun_prop : Continuous fun w : ℝ => Real.exp (-(2 * π * y * w))).mul
          continuous_completedZetaFourier.norm).aestronglyMeasurable
      · filter_upwards with w
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_completedZetaFourier_eq]
        exact mul_le_mul_of_nonneg_right (hexple y hy0 hy w) (abs_nonneg _)
    · intro w
      show Real.exp (-(2 * π * y * w)) * ‖completedZetaFourier w‖
        ≤ Real.exp (π ^ 2 * |w|) * |hardyXiDensity w|
      rw [norm_completedZetaFourier_eq]
      exact mul_le_mul_of_nonneg_right (hexple y hy0 hy w) (abs_nonneg _)
  have hev := tendsto_norm_hardySource_logTwo_atTop.eventually_gt_atTop M
  have hmem : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) := Ioo_mem_nhdsLT (by positivity)
  obtain ⟨y, hlt, hy⟩ := (hev.and hmem).exists
  exact absurd (hbound y hy.1.le hy.2 (Real.log 2)) (not_le.2 hlt)

theorem false_of_Xi_eventually_pos {T : ℝ} (hT : 0 < T) (hpos : ∀ t : ℝ, T < t → 0 < Xi t) :
    False := by
  have hpi := Real.pi_pos
  refine false_of_hardyXiDensity_tail_sign (W := T / (4 * π) + 1) (σ := -1)
    (by positivity) (by norm_num) ?_
  intro w hw
  have habs : hardyXiDensity w = hardyXiDensity |w| := by
    rcases abs_cases w with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hardyXiDensity_neg]
  have hbig : T < 4 * π * |w| := by
    have h1 : T / (4 * π) < |w| := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith [h1]
  have hXi := hpos (4 * π * |w|) hbig
  rw [habs, hardyXiDensity]
  have hden : (0:ℝ) < (4 * π * |w|) ^ 2 + 1 / 4 := by positivity
  rw [neg_one_mul, neg_nonneg]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hXi]) hden.le

theorem false_of_Xi_eventually_neg {T : ℝ} (hT : 0 < T) (hneg : ∀ t : ℝ, T < t → Xi t < 0) :
    False := by
  have hpi := Real.pi_pos
  refine false_of_hardyXiDensity_tail_sign (W := T / (4 * π) + 1) (σ := 1)
    (by positivity) (by norm_num) ?_
  intro w hw
  have habs : hardyXiDensity w = hardyXiDensity |w| := by
    rcases abs_cases w with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hardyXiDensity_neg]
  have hbig : T < 4 * π * |w| := by
    have h1 : T / (4 * π) < |w| := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith [h1]
  have hXi := hneg (4 * π * |w|) hbig
  rw [habs, hardyXiDensity, one_mul]
  have hden : (0:ℝ) < (4 * π * |w|) ^ 2 + 1 / 4 := by positivity
  exact div_nonneg (by nlinarith [hXi]) hden.le

/-- **Hardy's theorem.**  The real detector has zeros above every height. -/
theorem exists_Xi_zero_gt (T : ℝ) : ∃ t : ℝ, T < t ∧ Xi t = 0 := by
  by_contra hcon
  push Not at hcon
  set T' : ℝ := max T 1 with hT'def
  have hT'pos : 0 < T' := lt_of_lt_of_le one_pos (le_max_right T 1)
  have hne : ∀ t : ℝ, T' < t → Xi t ≠ 0 := fun t ht =>
    hcon t (lt_of_le_of_lt (le_max_left T 1) ht)
  set t₀ : ℝ := T' + 1 with ht₀def
  have ht₀gt : T' < t₀ := by rw [ht₀def]; linarith
  have hv := hne t₀ ht₀gt
  have hsame : ∀ t : ℝ, T' < t → 0 < Xi t * Xi t₀ := by
    intro t ht
    rcases lt_trichotomy (Xi t * Xi t₀) 0 with hlt | heq | hgt
    · exfalso
      have hcontOn : ContinuousOn Xi (Set.uIcc t t₀) := continuous_Xi.continuousOn
      have hmem : (0:ℝ) ∈ Set.uIcc (Xi t) (Xi t₀) := by
        rcases mul_neg_iff.1 hlt with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Set.mem_uIcc.2 (Or.inr ⟨h2.le, h1.le⟩)
        · exact Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩)
      obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc hcontOn hmem
      exact hne c (lt_of_lt_of_le (lt_min ht ht₀gt) hc.1) hc0
    · exfalso
      rcases mul_eq_zero.1 heq with h | h
      · exact hne t ht h
      · exact hv h
    · exact hgt
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · refine false_of_Xi_eventually_neg hT'pos ?_
    intro t ht
    have h := hsame t ht
    nlinarith [h, hneg]
  · refine false_of_Xi_eventually_pos hT'pos ?_
    intro t ht
    have h := hsame t ht
    nlinarith [h, hpos]

end Hardy


/-! ## The unconditional pole of Suzuki's displayed target -/

/-- **Two distinct positive real zeros of the centered completed function**, unconditionally, from
Hardy's theorem. -/
theorem exists_two_distinct_positive_real_XiC_zeros :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ≠ b ∧ XiC (a : ℂ) = 0 ∧ XiC (b : ℂ) = 0 := by
  obtain ⟨a, ha, hza⟩ := exists_Xi_zero_gt 0
  obtain ⟨b, hb, hzb⟩ := exists_Xi_zero_gt a
  refine ⟨a, b, ha, lt_trans ha hb, ne_of_lt hb, ?_, ?_⟩
  · rw [XiC_ofReal, hza]
    norm_num
  · rw [XiC_ofReal, hzb]
    norm_num

/-- **The unconditional pole.**  Suzuki's displayed characteristic target has a genuine pole at a
positive real critical point of the centered completed function. -/
theorem exists_pole_suzukiXiCharacteristicTarget :
    ∃ c : ℝ, 0 < c ∧ XiC (c : ℂ) ≠ 0 ∧ deriv XiC (c : ℂ) = 0 ∧
      ¬ AnalyticAt ℂ suzukiXiCharacteristicTarget (c : ℂ) := by
  obtain ⟨a, b, ha, hb, hab, hza, hzb⟩ := exists_two_distinct_positive_real_XiC_zeros
  exact exists_pole_suzukiXiCharacteristicTarget_of_two_positive_real_XiC_zeros ha hab hza hzb hb

/-- **Suzuki's displayed characteristic target is not entire**, unconditionally.  The
entire-compact reading of the displayed limit is therefore impossible without any hypothesis. -/
theorem not_analyticOnNhd_suzukiXiCharacteristicTarget :
    ¬ AnalyticOnNhd ℂ suzukiXiCharacteristicTarget Set.univ := by
  intro hanalytic
  obtain ⟨c, _, _, _, hpole⟩ := exists_pole_suzukiXiCharacteristicTarget
  exact hpole (hanalytic (c : ℂ) (Set.mem_univ _))

end

end RHTower
