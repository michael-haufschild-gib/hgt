import GaloisForLFunctions.RHTower.Sieve.InghamZetaSquarePoleDecomposition
import GaloisForLFunctions.RHTower.SmoothAFEGaussianKernel

noncomputable section

open Complex Set

namespace RHTower.Sieve

/-- Pole-filled numerator for the Gaussian zeta-square Mellin integrand. -/
def smoothAFEZetaSquarePoleNumerator (s : ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  (x : ℂ) ^ w * Complex.exp (w ^ 2) *
    regularizedRiemannZeta (s + w) ^ 2

/-- Literal Gaussian zeta-square Mellin integrand. -/
def smoothAFEZetaSquareMellinIntegrand (s : ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  riemannZeta (s + w) ^ 2 * (x : ℂ) ^ w *
    smoothAFEGaussianKernel w

theorem differentiable_smoothAFEZetaSquarePoleNumerator
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (smoothAFEZetaSquarePoleNumerator s x) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  unfold smoothAFEZetaSquarePoleNumerator
  intro w
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z) w :=
    ((hasDerivAt_id w).const_cpow (c := (x : ℂ)) (Or.inl hxC)).differentiableAt
  have hexp : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (z ^ 2)) w :=
    ((hasDerivAt_id w).pow 2).cexp.differentiableAt
  have hreg : DifferentiableAt ℂ
      (fun z : ℂ => regularizedRiemannZeta (s + z)) w :=
    differentiable_regularizedRiemannZeta.differentiableAt.comp w (by fun_prop)
  exact (hpow.mul hexp).mul (hreg.pow 2)

theorem smoothAFEZetaSquareMellinIntegrand_eq_poleQuotient
    {s w : ℂ} {x : ℝ} (hw0 : w ≠ 0) (hwa : w ≠ 1 - s) :
    smoothAFEZetaSquareMellinIntegrand s x w =
      smoothAFEZetaSquarePoleNumerator s x w /
        (w * (w - (1 - s)) ^ 2) := by
  have hshift : s + w ≠ 1 := by
    intro h
    apply hwa
    linear_combination h
  rw [smoothAFEZetaSquareMellinIntegrand,
    smoothAFEZetaSquarePoleNumerator, smoothAFEGaussianKernel,
    regularizedRiemannZeta_of_ne_one hshift]
  have hcoord : s + w - 1 = w - (1 - s) := by ring
  rw [hcoord]
  field_simp [hw0, sub_ne_zero.mpr hwa]

theorem confluentSimpleCoeff_smoothAFEZetaSquarePoleNumerator
    (tau : ℝ) (x : ℝ) :
    confluentSimpleCoeff
        (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
        (1 - linePt tau) = riemannZeta (linePt tau) ^ 2 := by
  have hs : linePt tau ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [linePt_re, Complex.one_re] at hre
    norm_num at hre
  rw [confluentSimpleCoeff, smoothAFEZetaSquarePoleNumerator, add_zero,
    regularizedRiemannZeta_of_ne_one hs]
  simp only [cpow_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Complex.exp_zero, one_mul]
  have hsq : (linePt tau - 1) ^ 2 = (1 - linePt tau) ^ 2 := by ring
  rw [mul_pow, hsq]
  field_simp [sub_ne_zero.mpr (Ne.symm hs)]

theorem deriv_smoothAFEZetaSquarePoleNumerator_shiftedPole
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    deriv (smoothAFEZetaSquarePoleNumerator s x) (1 - s) =
      (x : ℂ) ^ (1 - s) * Complex.exp ((1 - s) ^ 2) *
        ((Real.log x : ℂ) + 2 * (1 - s) +
          2 * deriv regularizedRiemannZeta 1) := by
  let a : ℂ := 1 - s
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpow : HasDerivAt (fun w : ℂ => (x : ℂ) ^ w)
      ((x : ℂ) ^ a * Complex.log (x : ℂ)) a := by
    simpa using (hasDerivAt_id a).const_cpow (c := (x : ℂ)) (Or.inl hxC)
  have hsq : HasDerivAt (fun w : ℂ => w ^ 2) (2 * a) a := by
    have h := (hasDerivAt_id a).pow 2
    have h' := h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _w : ℂ => rfl)
    convert h' using 1
    case e'_4 => rfl
    case e'_5 => rfl
    case e'_8 => funext w; rfl
    all_goals norm_num
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (w ^ 2))
      (Complex.exp (a ^ 2) * (2 * a)) a := hsq.cexp
  have hadd : HasDerivAt (fun w : ℂ => s + w) 1 a := by
    exact (hasDerivAt_id a).const_add s
  have hreg : HasDerivAt
      (fun w : ℂ => regularizedRiemannZeta (s + w))
      (deriv regularizedRiemannZeta 1) a := by
    have hcomp :=
      differentiable_regularizedRiemannZeta.differentiableAt.hasDerivAt.comp a hadd
    have hsa : s + a = 1 := by dsimp only [a]; ring
    have hcomp' := hcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _w : ℂ => rfl)
    convert hcomp' using 1
    case e'_4 => rfl
    case e'_5 => rfl
    case e'_8 => funext w; rfl
    all_goals simp only [hsa, mul_one]
  have hfull : HasDerivAt (fun w : ℂ =>
      ((x : ℂ) ^ w * Complex.exp (w ^ 2)) *
        regularizedRiemannZeta (s + w) ^ 2)
      (((x : ℂ) ^ a * Complex.log (x : ℂ) * Complex.exp (a ^ 2) +
          (x : ℂ) ^ a * (Complex.exp (a ^ 2) * (2 * a))) *
          regularizedRiemannZeta (s + a) ^ 2 +
        ((x : ℂ) ^ a * Complex.exp (a ^ 2)) *
          (2 * regularizedRiemannZeta (s + a) *
            deriv regularizedRiemannZeta 1)) a := by
    have h := (hpow.mul hexp).mul (hreg.pow 2)
    have h' := h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _w : ℂ => rfl)
    convert h' using 1
    case e'_4 => rfl
    case e'_5 => rfl
    case e'_8 =>
      funext w
      simp only [Pi.mul_apply, Pi.pow_apply]
    all_goals norm_num
  change deriv (fun w : ℂ =>
      ((x : ℂ) ^ w * Complex.exp (w ^ 2)) *
        regularizedRiemannZeta (s + w) ^ 2) a = _
  rw [hfull.deriv]
  have hsa : s + a = 1 := by dsimp only [a]; ring
  rw [hsa, regularizedRiemannZeta_one, ← Complex.ofReal_log hx.le]
  dsimp only [a]
  ring

theorem confluentResidueCoeff_smoothAFEZetaSquarePoleNumerator
    (s : ℂ) {x : ℝ} (hx : 0 < x) (hs : s ≠ 1) :
    confluentResidueCoeff (smoothAFEZetaSquarePoleNumerator s x) (1 - s) =
      ((x : ℂ) ^ (1 - s) * Complex.exp ((1 - s) ^ 2) / (1 - s)) *
        ((Real.log x : ℂ) + 2 * (1 - s) +
          2 * deriv regularizedRiemannZeta 1 - (1 - s)⁻¹) := by
  have ha : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  rw [confluentResidueCoeff,
    deriv_smoothAFEZetaSquarePoleNumerator_shiftedPole s hx,
    confluentDoubleCoeff, smoothAFEZetaSquarePoleNumerator]
  have hsa : s + (1 - s) = 1 := by ring
  rw [hsa, regularizedRiemannZeta_one]
  field_simp [ha]

theorem smoothAFEZetaSquareMellinIntegrand_confluent_decomposition
    (tau : ℝ) {x : ℝ} (hx : 0 < x) {w : ℂ}
    (hw0 : w ≠ 0) (hwa : w ≠ 1 - linePt tau) :
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x w =
      riemannZeta (linePt tau) ^ 2 * w⁻¹ +
        confluentDoubleCoeff
            (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau) * (w - (1 - linePt tau))⁻¹ ^ 2 +
        confluentResidueCoeff
            (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau) * (w - (1 - linePt tau))⁻¹ +
        confluentPoleRemainder
            (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau) w := by
  have ha : (1 : ℂ) - linePt tau ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, linePt_re] at hre
    norm_num at hre
  rw [smoothAFEZetaSquareMellinIntegrand_eq_poleQuotient hw0 hwa,
    confluent_twoPole_decomposition _ ha hw0 hwa
      ((differentiable_smoothAFEZetaSquarePoleNumerator
        (linePt tau) hx).differentiableAt),
    confluentSimpleCoeff_smoothAFEZetaSquarePoleNumerator]

/-- The literal square integrand is the single-zeta Gaussian integrand times
one additional zeta factor. -/
theorem smoothAFEZetaSquareMellinIntegrand_eq_single_mul_zeta
    (s : ℂ) (x : ℝ) (w : ℂ) :
    smoothAFEZetaSquareMellinIntegrand s x w =
      smoothAFEZetaMellinIntegrand s x w * riemannZeta (s + w) := by
  unfold smoothAFEZetaSquareMellinIntegrand smoothAFEZetaMellinIntegrand
  ring

end RHTower.Sieve
