import GaloisForLFunctions.RHTower.ThetaSourceHorizontalFluxExtractor
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Strict source log-concavity does not force neutral tilt-flux positivity

An explicit cosine-modulated Gaussian is positive, even, continuous, faster than every
exponential, and globally strictly log-concave. Its bilateral Laplace transform nevertheless has
an exact zero in the open right half-plane. The horizontal mean-value extractor therefore produces
a negative diagonal source Bezoutian, hence a negative one-mode neutral tilt flux.

This is a source-native no-go for deriving the TTF sign from positivity, rapid decay, strict
log-concavity, reflected midpoint order, or the correlation-angle consequences of those local
shape properties alone. Any successful source theorem needs additional global frequency rigidity.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

def modulatedGaussianEpsilon : ℝ := Real.exp (9 / 4) / Real.cosh 8

theorem real_exp_four_gt_sixteen : (16 : ℝ) < Real.exp 4 := by
  have htwo := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
  norm_num at htwo
  have hp : (2 : ℝ) ^ (4 : ℕ) < Real.exp 1 ^ (4 : ℕ) :=
    pow_lt_pow_left₀ htwo (by norm_num) (by norm_num)
  have heq : Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by
    simpa using Real.exp_nat_mul 1 4
  calc
    (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
    _ < Real.exp 1 ^ (4 : ℕ) := hp
    _ = Real.exp 4 := heq.symm

theorem modulatedGaussianEpsilon_pos : 0 < modulatedGaussianEpsilon := by
  unfold modulatedGaussianEpsilon
  positivity

theorem modulatedGaussianEpsilon_lt_one_eighth :
    modulatedGaussianEpsilon < 1 / 8 := by
  have hExp : (16 : ℝ) < Real.exp (23 / 4) := by
    exact real_exp_four_gt_sixteen.trans
      (Real.exp_lt_exp.mpr (by norm_num : (4 : ℝ) < 23 / 4))
  have hsplit : Real.exp 8 = Real.exp (9 / 4) * Real.exp (23 / 4) := by
    rw [← Real.exp_add]
    norm_num
  have hmul : 16 * Real.exp (9 / 4) < Real.exp 8 := by
    rw [hsplit]
    simpa [mul_comm] using mul_lt_mul_of_pos_left hExp (Real.exp_pos (9 / 4))
  have hcosh : Real.exp 8 / 2 < Real.cosh 8 := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-8)]
  have hkey : 8 * Real.exp (9 / 4) < Real.cosh 8 := by
    calc
      8 * Real.exp (9 / 4) < Real.exp 8 / 2 := by nlinarith
      _ < Real.cosh 8 := hcosh
  unfold modulatedGaussianEpsilon
  rw [div_lt_iff₀ (Real.cosh_pos 8)]
  norm_num
  nlinarith

theorem modulatedGaussianEpsilon_lt_one : modulatedGaussianEpsilon < 1 :=
  modulatedGaussianEpsilon_lt_one_eighth.trans (by norm_num)

def modulatedGaussianKernel (x : ℝ) : ℝ :=
  Real.exp (-(x ^ (2 : ℕ))) * (1 + modulatedGaussianEpsilon * Real.cos (3 * x))

theorem modulatedGaussianKernel_factor_pos (x : ℝ) :
    0 < 1 + modulatedGaussianEpsilon * Real.cos (3 * x) := by
  have heps := modulatedGaussianEpsilon_pos
  have hcos := Real.neg_one_le_cos (3 * x)
  have hmul : -modulatedGaussianEpsilon ≤
      modulatedGaussianEpsilon * Real.cos (3 * x) := by
    nlinarith
  linarith [modulatedGaussianEpsilon_lt_one]

theorem modulatedGaussianKernel_factor_lt_two (x : ℝ) :
    1 + modulatedGaussianEpsilon * Real.cos (3 * x) < 2 := by
  have heps := modulatedGaussianEpsilon_pos
  have hcos := Real.cos_le_one (3 * x)
  have hmul : modulatedGaussianEpsilon * Real.cos (3 * x) ≤
      modulatedGaussianEpsilon := by
    nlinarith
  linarith [modulatedGaussianEpsilon_lt_one]

theorem modulatedGaussianKernel_pos (x : ℝ) : 0 < modulatedGaussianKernel x := by
  unfold modulatedGaussianKernel
  exact mul_pos (Real.exp_pos _) (modulatedGaussianKernel_factor_pos x)

theorem modulatedGaussianKernel_even (x : ℝ) :
    modulatedGaussianKernel (-x) = modulatedGaussianKernel x := by
  unfold modulatedGaussianKernel
  rw [neg_sq, show 3 * -x = -(3 * x) by ring, Real.cos_neg]

theorem continuous_modulatedGaussianKernel : Continuous modulatedGaussianKernel := by
  unfold modulatedGaussianKernel
  fun_prop

theorem modulatedGaussianKernel_decay (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x,
      modulatedGaussianKernel x ≤ C * Real.exp (-(M * |x|)) := by
  refine ⟨2 * Real.exp (M ^ (2 : ℕ) / 4), by positivity, fun x => ?_⟩
  have hfactorPos := (modulatedGaussianKernel_factor_pos x).le
  have hfactor := (modulatedGaussianKernel_factor_lt_two x).le
  have hkernel : modulatedGaussianKernel x ≤ 2 * Real.exp (-(x ^ (2 : ℕ))) := by
    unfold modulatedGaussianKernel
    nlinarith [Real.exp_pos (-(x ^ (2 : ℕ)))]
  have hsquare : 0 ≤ (|x| - M / 2) ^ (2 : ℕ) := sq_nonneg _
  have hexponent : -(x ^ (2 : ℕ)) ≤ M ^ (2 : ℕ) / 4 - M * |x| := by
    nlinarith [sq_abs x]
  have hexp : Real.exp (-(x ^ (2 : ℕ))) ≤
      Real.exp (M ^ (2 : ℕ) / 4) * Real.exp (-(M * |x|)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    modulatedGaussianKernel x ≤ 2 * Real.exp (-(x ^ (2 : ℕ))) := hkernel
    _ ≤ 2 * (Real.exp (M ^ (2 : ℕ) / 4) * Real.exp (-(M * |x|))) := by gcongr
    _ = (2 * Real.exp (M ^ (2 : ℕ) / 4)) * Real.exp (-(M * |x|)) := by ring

def modulatedGaussianSource : ThetaSource where
  k := modulatedGaussianKernel
  pos := modulatedGaussianKernel_pos
  even' := modulatedGaussianKernel_even
  cont := continuous_modulatedGaussianKernel
  decay := modulatedGaussianKernel_decay

def gaussianBilateralClosed (w : ℂ) : ℂ :=
  ((Real.pi : ℂ) ^ (1 / 2 : ℂ)) * Complex.exp (w ^ (2 : ℕ) / 4)

theorem integral_cexp_neg_sq_add_linear (w : ℂ) :
    (∫ x : ℝ, Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + w * (x : ℂ))) =
      gaussianBilateralClosed w := by
  have h := integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num) w 0
  rw [show (fun x : ℝ => Complex.exp
      ((-1 : ℂ) * (x : ℂ) ^ (2 : ℕ) + w * (x : ℂ) + 0)) =
      fun x : ℝ => Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + w * (x : ℂ)) by
        funext x
        ring] at h
  rw [gaussianBilateralClosed]
  convert h using 1
  norm_num
  apply congrArg Complex.exp
  field_simp

theorem integrable_cexp_neg_sq_add_linear (w : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + w * (x : ℂ))) := by
  have h := integrable_cexp_quadratic' (b := (-1 : ℂ)) (by norm_num) w 0
  convert h using 1
  funext x
  ring

theorem ofReal_cos_three_eq_exp_average (x : ℝ) :
    ((Real.cos (3 * x) : ℝ) : ℂ) =
      (Complex.exp (((3 * x : ℝ) : ℂ) * I) +
        Complex.exp (-(((3 * x : ℝ) : ℂ) * I))) / 2 := by
  rw [Complex.ofReal_cos]
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  simpa [mul_comm] using Complex.two_cos ((3 * x : ℝ) : ℂ)

theorem modulatedGaussian_integrand_eq (w : ℂ) (x : ℝ) :
    (modulatedGaussianKernel x : ℂ) * Complex.exp (w * (x : ℂ)) =
      Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + w * (x : ℂ)) +
      (modulatedGaussianEpsilon : ℂ) / 2 *
        (Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + (w + 3 * I) * (x : ℂ)) +
          Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + (w - 3 * I) * (x : ℂ))) := by
  rw [modulatedGaussianKernel, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul,
    ofReal_cos_three_eq_exp_average]
  push_cast
  ring_nf
  have hp :
      Complex.exp (-((x : ℂ) ^ (2 : ℕ))) * Complex.exp ((x : ℂ) * I * 3) *
          Complex.exp ((x : ℂ) * w) =
        Complex.exp ((x : ℂ) * I * 3 + (x : ℂ) * w - (x : ℂ) ^ (2 : ℕ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hm :
      Complex.exp (-((x : ℂ) ^ (2 : ℕ))) * Complex.exp ((x : ℂ) * w) *
          Complex.exp (-((x : ℂ) * I * 3)) =
        Complex.exp (-((x : ℂ) * I * 3) + (x : ℂ) * w - (x : ℂ) ^ (2 : ℕ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have h0 :
      Complex.exp (-((x : ℂ) ^ (2 : ℕ))) * Complex.exp ((x : ℂ) * w) =
        Complex.exp ((x : ℂ) * w - (x : ℂ) ^ (2 : ℕ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (modulatedGaussianEpsilon : ℂ) *
          (Complex.exp (-((x : ℂ) ^ (2 : ℕ))) * Complex.exp ((x : ℂ) * I * 3) *
            Complex.exp ((x : ℂ) * w)) * (1 / 2) +
        (modulatedGaussianEpsilon : ℂ) *
          (Complex.exp (-((x : ℂ) ^ (2 : ℕ))) * Complex.exp ((x : ℂ) * w) *
            Complex.exp (-((x : ℂ) * I * 3))) * (1 / 2) +
        Complex.exp (-((x : ℂ) ^ (2 : ℕ))) * Complex.exp ((x : ℂ) * w) := by ring
    _ = _ := by rw [hp, hm, h0]

theorem bilateralLaplace_modulatedGaussianSource_raw (w : ℂ) :
    bilateralLaplace modulatedGaussianSource w =
      gaussianBilateralClosed w +
      (modulatedGaussianEpsilon : ℂ) / 2 *
        (gaussianBilateralClosed (w + 3 * I) +
          gaussianBilateralClosed (w - 3 * I)) := by
  rw [bilateralLaplace]
  change (∫ x : ℝ,
      (modulatedGaussianKernel x : ℂ) * Complex.exp (w * (x : ℂ))) = _
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (modulatedGaussian_integrand_eq w))]
  have h0 := integrable_cexp_neg_sq_add_linear w
  have hp := integrable_cexp_neg_sq_add_linear (w + 3 * I)
  have hm := integrable_cexp_neg_sq_add_linear (w - 3 * I)
  calc
    (∫ x : ℝ,
        Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + w * (x : ℂ)) +
          (modulatedGaussianEpsilon : ℂ) / 2 *
            (Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + (w + 3 * I) * (x : ℂ)) +
              Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + (w - 3 * I) * (x : ℂ)))) =
        (∫ x : ℝ, Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + w * (x : ℂ))) +
          ∫ x : ℝ, (modulatedGaussianEpsilon : ℂ) / 2 *
            (Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + (w + 3 * I) * (x : ℂ)) +
              Complex.exp (-((x : ℂ) ^ (2 : ℕ)) + (w - 3 * I) * (x : ℂ))) :=
      MeasureTheory.integral_add h0 ((hp.add hm).const_mul _)
    _ = _ := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hp hm,
        integral_cexp_neg_sq_add_linear, integral_cexp_neg_sq_add_linear,
        integral_cexp_neg_sq_add_linear]

theorem gaussianBilateralClosed_add_three_I (w : ℂ) :
    gaussianBilateralClosed (w + 3 * I) =
      gaussianBilateralClosed w * Complex.exp (-(9 / 4 : ℝ)) *
        Complex.exp ((3 / 2 : ℂ) * I * w) := by
  have hexp :
      Complex.exp ((w + 3 * I) ^ (2 : ℕ) / 4) =
        Complex.exp (w ^ (2 : ℕ) / 4) * Complex.exp (-(9 / 4 : ℝ)) *
          Complex.exp ((3 / 2 : ℂ) * I * w) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    apply congrArg Complex.exp
    ring_nf
    simp [I_sq]
    ring
  rw [gaussianBilateralClosed, gaussianBilateralClosed, hexp]
  ring

theorem gaussianBilateralClosed_sub_three_I (w : ℂ) :
    gaussianBilateralClosed (w - 3 * I) =
      gaussianBilateralClosed w * Complex.exp (-(9 / 4 : ℝ)) *
        Complex.exp (-((3 / 2 : ℂ) * I * w)) := by
  have hexp :
      Complex.exp ((w - 3 * I) ^ (2 : ℕ) / 4) =
        Complex.exp (w ^ (2 : ℕ) / 4) * Complex.exp (-(9 / 4 : ℝ)) *
          Complex.exp (-((3 / 2 : ℂ) * I * w)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    apply congrArg Complex.exp
    ring_nf
    simp [I_sq]
    ring
  rw [gaussianBilateralClosed, gaussianBilateralClosed, hexp]
  ring

theorem bilateralLaplace_modulatedGaussianSource (w : ℂ) :
    bilateralLaplace modulatedGaussianSource w =
      gaussianBilateralClosed w *
        (1 + (modulatedGaussianEpsilon : ℂ) * Complex.exp (-(9 / 4 : ℝ)) *
          Complex.cos ((3 / 2 : ℂ) * w)) := by
  rw [bilateralLaplace_modulatedGaussianSource_raw,
    gaussianBilateralClosed_add_three_I,
    gaussianBilateralClosed_sub_three_I]
  have hcos := Complex.two_cos ((3 / 2 : ℂ) * w)
  have hp : ((3 / 2 : ℂ) * w) * I = (3 / 2 : ℂ) * I * w := by ring
  have hm : -((3 / 2 : ℂ) * w) * I = -((3 / 2 : ℂ) * I * w) := by ring
  rw [hp, hm] at hcos
  have hcos' : Complex.cos ((3 / 2 : ℂ) * w) =
      (Complex.exp ((3 / 2 : ℂ) * I * w) +
        Complex.exp (-((3 / 2 : ℂ) * I * w))) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    simpa [mul_comm] using hcos
  rw [hcos']
  ring

theorem modulatedGaussian_transformCoefficient_eq :
    (modulatedGaussianEpsilon : ℂ) * Complex.exp (-(9 / 4 : ℝ)) =
      ((1 / Real.cosh 8 : ℝ) : ℂ) := by
  rw [modulatedGaussianEpsilon, Complex.ofReal_div, Complex.ofReal_exp]
  have hcosh : (Real.cosh 8 : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (Real.cosh_pos 8).ne'
  push_cast
  field_simp [hcosh]
  rw [← Complex.exp_add]
  norm_num

theorem bilateralLaplace_modulatedGaussianSource_normalized (w : ℂ) :
    bilateralLaplace modulatedGaussianSource w =
      gaussianBilateralClosed w *
        (1 + ((1 / Real.cosh 8 : ℝ) : ℂ) *
          Complex.cos ((3 / 2 : ℂ) * w)) := by
  rw [bilateralLaplace_modulatedGaussianSource,
    modulatedGaussian_transformCoefficient_eq]

def modulatedGaussianRightZero : ℂ :=
  (2 * Real.pi / 3 : ℝ) + (16 / 3 : ℝ) * I

theorem modulatedGaussianRightZero_re_pos :
    0 < modulatedGaussianRightZero.re := by
  rw [modulatedGaussianRightZero]
  simp
  positivity

theorem modulatedGaussianRightZero_argument :
    (3 / 2 : ℂ) * modulatedGaussianRightZero =
      (Real.pi : ℂ) + (8 : ℂ) * I := by
  rw [modulatedGaussianRightZero]
  push_cast
  ring

theorem complex_cos_pi_add_eight_I :
    Complex.cos ((Real.pi : ℂ) + (8 : ℂ) * I) = -(Real.cosh 8 : ℂ) := by
  rw [Complex.cos_add_mul_I]
  simp

theorem bilateralLaplace_modulatedGaussianSource_rightZero :
    bilateralLaplace modulatedGaussianSource modulatedGaussianRightZero = 0 := by
  rw [bilateralLaplace_modulatedGaussianSource_normalized,
    modulatedGaussianRightZero_argument, complex_cos_pi_add_eight_I]
  have hcosh : (Real.cosh 8 : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (Real.cosh_pos 8).ne'
  rw [Complex.ofReal_div, Complex.ofReal_one]
  change gaussianBilateralClosed modulatedGaussianRightZero *
    (1 + (1 / (Real.cosh 8 : ℂ)) * -(Real.cosh 8 : ℂ)) = 0
  field_simp [hcosh]
  ring

theorem gaussianBilateralClosed_ne_zero (w : ℂ) : gaussianBilateralClosed w ≠ 0 := by
  rw [gaussianBilateralClosed]
  exact mul_ne_zero ((Complex.cpow_ne_zero_iff).2
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (Complex.exp_ne_zero _)

theorem bilateralLaplace_modulatedGaussianSource_imaginaryBase_ne_zero :
    bilateralLaplace modulatedGaussianSource ((16 / 3 : ℝ) * I) ≠ 0 := by
  rw [bilateralLaplace_modulatedGaussianSource_normalized]
  have harg : (3 / 2 : ℂ) * ((16 / 3 : ℝ) * I) = (8 : ℂ) * I := by
    push_cast
    ring
  rw [harg, Complex.cos_mul_I]
  have hcoshCast : Complex.cosh (8 : ℂ) = (Real.cosh 8 : ℂ) := by
    simpa using (Complex.ofReal_cosh 8).symm
  rw [hcoshCast]
  have hcosh : (Real.cosh 8 : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (Real.cosh_pos 8).ne'
  have hfactor : 1 + ((1 / Real.cosh 8 : ℝ) : ℂ) * (Real.cosh 8 : ℂ) = 2 := by
    rw [Complex.ofReal_div, Complex.ofReal_one]
    field_simp [hcosh]
    ring
  rw [hfactor]
  exact mul_ne_zero (gaussianBilateralClosed_ne_zero _) (by norm_num)

def modulatedGaussianLogFactor (x : ℝ) : ℝ :=
  Real.log (1 + modulatedGaussianEpsilon * Real.cos (3 * x))

def modulatedGaussianLogModel (x : ℝ) : ℝ :=
  -(x ^ (2 : ℕ)) + modulatedGaussianLogFactor x

theorem modulatedGaussianLogModel_eq_log_kernel (x : ℝ) :
    modulatedGaussianLogModel x = Real.log (modulatedGaussianKernel x) := by
  rw [modulatedGaussianLogModel, modulatedGaussianLogFactor, modulatedGaussianKernel,
    Real.log_mul (Real.exp_ne_zero _) (modulatedGaussianKernel_factor_pos x).ne',
    Real.log_exp]

theorem hasDerivAt_modulatedGaussianFactor (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 + modulatedGaussianEpsilon * Real.cos (3 * y))
      (-3 * modulatedGaussianEpsilon * Real.sin (3 * x)) x := by
  have h := (((Real.hasDerivAt_cos (3 * x)).comp x
      ((hasDerivAt_id x).const_mul 3)).const_mul modulatedGaussianEpsilon).const_add 1
  have hder : modulatedGaussianEpsilon * (-Real.sin (3 * x) * (3 * 1)) =
      -3 * modulatedGaussianEpsilon * Real.sin (3 * x) := by ring
  rw [hder] at h
  simpa only [Function.comp_apply] using h

theorem hasDerivAt_modulatedGaussianLogModel (x : ℝ) :
    HasDerivAt modulatedGaussianLogModel
      (-(2 * x) +
        (-3 * modulatedGaussianEpsilon * Real.sin (3 * x)) /
          (1 + modulatedGaussianEpsilon * Real.cos (3 * x))) x := by
  have hquad : HasDerivAt (fun y : ℝ => -(y ^ (2 : ℕ))) (-(2 * x)) x := by
    have h := (hasDerivAt_pow 2 x).const_sub 0
    norm_num at h
    exact h
  have hlog := (hasDerivAt_modulatedGaussianFactor x).log
    (modulatedGaussianKernel_factor_pos x).ne'
  exact hquad.add hlog

theorem hasDerivAt_modulatedGaussianLogModel_deriv (x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        -(2 * y) +
          (-3 * modulatedGaussianEpsilon * Real.sin (3 * y)) /
            (1 + modulatedGaussianEpsilon * Real.cos (3 * y)))
      (-2 +
        (-9 * modulatedGaussianEpsilon *
          (Real.cos (3 * x) + modulatedGaussianEpsilon)) /
            (1 + modulatedGaussianEpsilon * Real.cos (3 * x)) ^ (2 : ℕ)) x := by
  let e : ℝ := modulatedGaussianEpsilon
  let s : ℝ := Real.sin (3 * x)
  let c : ℝ := Real.cos (3 * x)
  have hlin : HasDerivAt (fun y : ℝ => -(2 * y)) (-2) x := by
    have h := ((hasDerivAt_id x).const_mul 2).const_sub 0
    norm_num at h
    exact h
  have hsin : HasDerivAt (fun y : ℝ => -3 * e * Real.sin (3 * y))
      (-9 * e * c) x := by
    have h := ((Real.hasDerivAt_sin (3 * x)).comp x
      ((hasDerivAt_id x).const_mul 3)).const_mul (-3 * e)
    simpa [e, c] using h.congr_deriv (by ring)
  have hden : HasDerivAt (fun y : ℝ => 1 + e * Real.cos (3 * y))
      (-3 * e * s) x := by
    simpa [e, s] using hasDerivAt_modulatedGaussianFactor x
  have hden0 : 1 + e * c ≠ 0 := by
    exact (modulatedGaussianKernel_factor_pos x).ne'
  have hquot := hsin.div hden hden0
  have htrig : s ^ (2 : ℕ) + c ^ (2 : ℕ) = 1 := by
    dsimp [s, c]
    nlinarith [Real.sin_sq_add_cos_sq (3 * x)]
  have hval :
      -2 +
          ((-9 * e * c * (1 + e * c) - (-3 * e * s) * (-3 * e * s)) /
            (1 + e * c) ^ (2 : ℕ)) =
        -2 + (-9 * e * (c + e)) / (1 + e * c) ^ (2 : ℕ) := by
    field_simp [hden0]
    ring_nf at htrig ⊢
    nlinarith [htrig]
  have hsum := hlin.add hquot
  dsimp [e, s, c] at hsum hval
  rw [hval] at hsum
  exact hsum

theorem iteratedDeriv_two_modulatedGaussianLogModel (x : ℝ) :
    iteratedDeriv 2 modulatedGaussianLogModel x =
      -2 +
        (-9 * modulatedGaussianEpsilon *
          (Real.cos (3 * x) + modulatedGaussianEpsilon)) /
            (1 + modulatedGaussianEpsilon * Real.cos (3 * x)) ^ (2 : ℕ) := by
  have hderiv : deriv modulatedGaussianLogModel =
      fun y : ℝ => -(2 * y) +
        (-3 * modulatedGaussianEpsilon * Real.sin (3 * y)) /
          (1 + modulatedGaussianEpsilon * Real.cos (3 * y)) := by
    funext y
    exact (hasDerivAt_modulatedGaussianLogModel y).deriv
  rw [show iteratedDeriv 2 modulatedGaussianLogModel x =
      deriv (deriv modulatedGaussianLogModel) x by simp [iteratedDeriv_succ], hderiv]
  exact (hasDerivAt_modulatedGaussianLogModel_deriv x).deriv

theorem iteratedDeriv_two_modulatedGaussianLogModel_neg (x : ℝ) :
    iteratedDeriv 2 modulatedGaussianLogModel x < 0 := by
  let e : ℝ := modulatedGaussianEpsilon
  let c : ℝ := Real.cos (3 * x)
  have he0 : 0 < e := modulatedGaussianEpsilon_pos
  have he : e < 1 / 8 := modulatedGaussianEpsilon_lt_one_eighth
  have hc0 : -1 ≤ c := Real.neg_one_le_cos (3 * x)
  have hf : 0 < 1 + e * c := by
    simpa [e, c] using modulatedGaussianKernel_factor_pos x
  have hcoarse : -13 * e * c ≤ 13 * e := by
    nlinarith
  have hnum :
      -2 * (1 + e * c) ^ (2 : ℕ) - 9 * e * (c + e) < 0 := by
    nlinarith [sq_nonneg c, sq_nonneg e]
  rw [iteratedDeriv_two_modulatedGaussianLogModel]
  change -2 + (-9 * e * (c + e)) / (1 + e * c) ^ (2 : ℕ) < 0
  have heq : -2 + (-9 * e * (c + e)) / (1 + e * c) ^ (2 : ℕ) =
      (-2 * (1 + e * c) ^ (2 : ℕ) - 9 * e * (c + e)) /
        (1 + e * c) ^ (2 : ℕ) := by
    field_simp [(ne_of_gt hf)]
    ring
  rw [heq]
  exact div_neg_of_neg_of_pos hnum (sq_pos_of_pos hf)

theorem strictConcaveOn_modulatedGaussianLogModel :
    StrictConcaveOn ℝ Set.univ modulatedGaussianLogModel := by
  apply strictConcaveOn_univ_of_deriv2_neg
  · unfold modulatedGaussianLogModel modulatedGaussianLogFactor
    apply Continuous.add
    · fun_prop
    · exact (continuous_const.add
        (continuous_const.mul (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)))).log
        (fun x => (modulatedGaussianKernel_factor_pos x).ne')
  · intro x
    rw [show (deriv^[2]) modulatedGaussianLogModel x =
      iteratedDeriv 2 modulatedGaussianLogModel x by simp [iteratedDeriv_succ]]
    exact iteratedDeriv_two_modulatedGaussianLogModel_neg x

theorem strictConcaveOn_log_modulatedGaussianKernel :
    StrictConcaveOn ℝ Set.univ (fun x => Real.log (modulatedGaussianKernel x)) := by
  have hfun : (fun x => Real.log (modulatedGaussianKernel x)) =
      modulatedGaussianLogModel := by
    funext x
    exact (modulatedGaussianLogModel_eq_log_kernel x).symm
  rw [hfun]
  exact strictConcaveOn_modulatedGaussianLogModel

/-- The explicit strictly log-concave source has a negative diagonal Bezoutian at some point of
the open right half-plane. The witness is extracted between its nonzero imaginary-axis value and
its exact right-half-plane zero. -/
theorem exists_modulatedGaussianSource_sourceBezoutian_diagonal_neg :
    ∃ a : ℝ, a ∈ Ioo 0 (2 * Real.pi / 3) ∧
      (sourceBezoutian modulatedGaussianSource
        ((a : ℂ) + (16 / 3 : ℝ) * I)
        ((a : ℂ) + (16 / 3 : ℝ) * I)).re < 0 := by
  apply exists_sourceBezoutian_diagonal_neg_of_horizontal_zero
    modulatedGaussianSource
  · positivity
  · simpa [modulatedGaussianRightZero] using
      bilateralLaplace_modulatedGaussianSource_rightZero
  · exact bilateralLaplace_modulatedGaussianSource_imaginaryBase_ne_zero

/-- The obstruction is the literal neutral one-mode tilt flux: at some right-half-plane point,
the derivative at zero of the one-mode tilt correlation exists and is strictly negative. -/
theorem exists_modulatedGaussianSource_tiltCorrelation_deriv_neg :
    ∃ w : ℂ, 0 < w.re ∧
      ∃ D : ℝ,
        HasDerivAt
          (tiltCorrelation modulatedGaussianSource
            (fun _ : Fin 1 => 1) (fun _ : Fin 1 => w)) D 0 ∧
        D < 0 := by
  obtain ⟨a, ha, hneg⟩ :=
    exists_modulatedGaussianSource_sourceBezoutian_diagonal_neg
  let w : ℂ := (a : ℂ) + (16 / 3 : ℝ) * I
  refine ⟨w, ?_, (sourceBezoutian modulatedGaussianSource w w).re, ?_, hneg⟩
  · simpa [w] using ha.1
  · simpa [w] using
      hasDerivAt_tiltCorrelation modulatedGaussianSource
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => w)
        (fun _ => by simpa [w] using ha.1)

/-- **Closed local-shape no-go.** There exists a positive, even, faster-than-every-exponential
source with globally strictly concave logarithm whose neutral one-mode flux is negative somewhere
in the open right half-plane. -/
theorem exists_strictLogConcave_thetaSource_with_negative_flux :
    ∃ S : ThetaSource,
      StrictConcaveOn ℝ Set.univ (fun x => Real.log (S.k x)) ∧
      ∃ w : ℂ, 0 < w.re ∧ (sourceBezoutian S w w).re < 0 := by
  refine ⟨modulatedGaussianSource, strictConcaveOn_log_modulatedGaussianKernel, ?_⟩
  obtain ⟨a, ha, hneg⟩ :=
    exists_modulatedGaussianSource_sourceBezoutian_diagonal_neg
  refine ⟨(a : ℂ) + (16 / 3 : ℝ) * I, ?_, hneg⟩
  simpa using ha.1

end

end RHTower
