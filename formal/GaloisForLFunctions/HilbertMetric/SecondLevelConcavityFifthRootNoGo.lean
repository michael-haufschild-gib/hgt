import GaloisForLFunctions.HilbertMetric.FifthRootCurvatureCusp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Second-level concavity does not force fifth-root divided-drop convexity

Planat--Solé second-level concavity is a one-point Laguerre law.  This module gives a closed
structural counterexample to promoting that law, without theta-specific input, to the nonlocal
fifth-root curvature required by the reflected rank-four route.

For the positive even kernel `F(r) = exp (-r^4)`, its radial profile is
`s(x) = F(sqrt x) = exp (-x^2)`.  The first Laguerre expression is exactly
`2 exp (-2x^2)`, so its logarithm has constant second derivative `-4`.  Nevertheless the
centered reflected product `P(t) = F(t)F(-t) = exp (-2t^4)` has strictly negative fifth-root
divided-drop curvature numerator at `t = 1/2`.

Thus second-level Laguerre concavity alone cannot close C5.  Any successful use of the published
theta theorem must retain additional completed-theta structure.
-/

open Set

namespace HilbertMetric

noncomputable section

/-- Positive even quartic Gaussian kernel used by the no-go. -/
def quarticGaussianKernel (x : ℝ) : ℝ := Real.exp (-x ^ 4)

/-- Centered reflected product of the quartic Gaussian kernel. -/
def quarticGaussianReflectedProfile (x : ℝ) : ℝ := Real.exp (-2 * x ^ 4)

/-- Radial square-coordinate profile of the quartic Gaussian kernel. -/
def quadraticGaussianRadialProfile (x : ℝ) : ℝ := Real.exp (-x ^ 2)

/-- First Laguerre expression in the convention used by second-level concavity. -/
def firstLaguerreExpression (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  iteratedDeriv 1 f x ^ 2 - f x * iteratedDeriv 2 f x

theorem hasDerivAt_quadraticGaussianRadialProfile (x : ℝ) :
    HasDerivAt quadraticGaussianRadialProfile
      (-2 * x * Real.exp (-x ^ 2)) x := by
  have h := (Real.hasDerivAt_exp (-x ^ 2)).comp x
    (((hasDerivAt_id x).pow 2).neg)
  have hfun : quadraticGaussianRadialProfile = Real.exp ∘ (-id ^ 2) := by
    funext y
    rfl
  rw [hfun]
  refine h.congr_deriv ?_
  norm_num
  ring

theorem iteratedDeriv_one_quadraticGaussianRadialProfile (x : ℝ) :
    iteratedDeriv 1 quadraticGaussianRadialProfile x =
      -2 * x * Real.exp (-x ^ 2) := by
  rw [iteratedDeriv_one, (hasDerivAt_quadraticGaussianRadialProfile x).deriv]

theorem iteratedDeriv_two_quadraticGaussianRadialProfile (x : ℝ) :
    iteratedDeriv 2 quadraticGaussianRadialProfile x =
      (4 * x ^ 2 - 2) * Real.exp (-x ^ 2) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hfun : deriv quadraticGaussianRadialProfile =
      fun y : ℝ => -2 * y * Real.exp (-y ^ 2) := by
    funext y
    exact (hasDerivAt_quadraticGaussianRadialProfile y).deriv
  rw [hfun]
  have hmul := ((hasDerivAt_id x).const_mul (-2)).mul
    (hasDerivAt_quadraticGaussianRadialProfile x)
  have hprod : (fun y : ℝ => -2 * y * Real.exp (-y ^ 2)) =
      (fun y : ℝ => -2 * id y) * quadraticGaussianRadialProfile := by
    funext y
    rfl
  rw [hprod, hmul.deriv]
  simp only [quadraticGaussianRadialProfile, id_eq]
  ring

/-- The first Laguerre expression of `exp (-x^2)` is a single quadratic Gaussian. -/
theorem firstLaguerreExpression_quadraticGaussianRadialProfile (x : ℝ) :
    firstLaguerreExpression quadraticGaussianRadialProfile x =
      2 * Real.exp (-2 * x ^ 2) := by
  unfold firstLaguerreExpression
  rw [iteratedDeriv_one_quadraticGaussianRadialProfile,
    iteratedDeriv_two_quadraticGaussianRadialProfile]
  unfold quadraticGaussianRadialProfile
  have hexp : Real.exp (-2 * x ^ 2) = Real.exp (-x ^ 2) ^ 2 := by
    calc
      Real.exp (-2 * x ^ 2) = Real.exp (-x ^ 2 + -x ^ 2) := by congr 1; ring
      _ = Real.exp (-x ^ 2) * Real.exp (-x ^ 2) := Real.exp_add _ _
      _ = Real.exp (-x ^ 2) ^ 2 := by ring
  rw [hexp]
  ring

/-- Exact second-level logarithmic curvature of the radial profile. -/
theorem quadraticGaussianRadialProfile_secondLevelLogCurvature (x : ℝ) :
    iteratedDeriv 2
      (fun y => Real.log (firstLaguerreExpression quadraticGaussianRadialProfile y)) x = -4 := by
  have hlog (y : ℝ) :
      Real.log (firstLaguerreExpression quadraticGaussianRadialProfile y) =
        Real.log 2 - 2 * y ^ 2 := by
    rw [firstLaguerreExpression_quadraticGaussianRadialProfile,
      Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hfun :
      (fun y => Real.log (firstLaguerreExpression quadraticGaussianRadialProfile y)) =
        fun y => Real.log 2 - 2 * y ^ 2 := by
    funext y
    exact hlog y
  rw [hfun, iteratedDeriv_succ, iteratedDeriv_one]
  have hfirst : deriv (fun y : ℝ => Real.log 2 - 2 * y ^ 2) =
      fun y => -4 * y := by
    funext y
    have hderiv := (hasDerivAt_const y (Real.log 2)).sub
      (((hasDerivAt_id y).pow 2).const_mul 2)
    have htarget : HasDerivAt (fun z : ℝ => Real.log 2 - 2 * z ^ 2)
        (-4 * y) y := by
      rw [show (fun z : ℝ => Real.log 2 - 2 * z ^ 2) =
          (fun _ : ℝ => Real.log 2) - fun z => 2 * (id ^ 2) z by
        funext z
        simp only [Pi.sub_apply, Pi.pow_apply, id_eq]]
      refine hderiv.congr_deriv ?_
      norm_num
      ring
    exact htarget.deriv
  rw [hfirst]
  simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (-4)).deriv

/-- The radial profile has strict second-level concavity at every real point. -/
theorem quadraticGaussianRadialProfile_secondLevel_strict (x : ℝ) :
    iteratedDeriv 2
      (fun y => Real.log (firstLaguerreExpression quadraticGaussianRadialProfile y)) x < 0 := by
  rw [quadraticGaussianRadialProfile_secondLevelLogCurvature]
  norm_num

theorem hasDerivAt_quarticGaussianReflectedProfile (x : ℝ) :
    HasDerivAt quarticGaussianReflectedProfile
      (-8 * x ^ 3 * Real.exp (-2 * x ^ 4)) x := by
  have hinner := (((hasDerivAt_id x).pow 4).const_mul 2).neg
  have hinner' : HasDerivAt (fun y : ℝ => -2 * y ^ 4) (-8 * x ^ 3) x := by
    rw [show (fun y : ℝ => -2 * y ^ 4) =
        -(fun y : ℝ => 2 * (id ^ 4) y) by
      funext y
      simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
      ring]
    refine hinner.congr_deriv ?_
    norm_num
    ring
  have h := (Real.hasDerivAt_exp (-2 * x ^ 4)).comp x hinner'
  have hfun : quarticGaussianReflectedProfile =
      Real.exp ∘ fun y : ℝ => -2 * y ^ 4 := by
    funext y
    rfl
  rw [hfun]
  refine h.congr_deriv ?_
  norm_num
  ring

theorem iteratedDeriv_one_quarticGaussianReflectedProfile (x : ℝ) :
    iteratedDeriv 1 quarticGaussianReflectedProfile x =
      -8 * x ^ 3 * Real.exp (-2 * x ^ 4) := by
  rw [iteratedDeriv_one, (hasDerivAt_quarticGaussianReflectedProfile x).deriv]

theorem iteratedDeriv_two_quarticGaussianReflectedProfile (x : ℝ) :
    iteratedDeriv 2 quarticGaussianReflectedProfile x =
      (64 * x ^ 6 - 24 * x ^ 2) * Real.exp (-2 * x ^ 4) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hfun : deriv quarticGaussianReflectedProfile =
      fun y : ℝ => -8 * y ^ 3 * Real.exp (-2 * y ^ 4) := by
    funext y
    exact (hasDerivAt_quarticGaussianReflectedProfile y).deriv
  rw [hfun]
  have hmul := (((hasDerivAt_id x).pow 3).const_mul (-8)).mul
    (hasDerivAt_quarticGaussianReflectedProfile x)
  have hprod : (fun y : ℝ => -8 * y ^ 3 * Real.exp (-2 * y ^ 4)) =
      (fun y : ℝ => -8 * (id ^ 3) y) * quarticGaussianReflectedProfile := by
    funext y
    rfl
  rw [hprod, hmul.deriv]
  simp only [quarticGaussianReflectedProfile, Pi.pow_apply, id_eq]
  ring

private theorem exp_one_eighth_lt_eight_sevenths :
    Real.exp (1 / 8 : ℝ) < 8 / 7 := by
  have hb := Real.exp_bound (x := (1 / 8 : ℝ)) (by norm_num)
    (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  nlinarith [le_abs_self
    (Real.exp (1 / 8 : ℝ) -
      (1 + (1 / 8 : ℝ) + (1 / 8 : ℝ) ^ 2 / 2 +
        (1 / 8 : ℝ) ^ 3 / 6))]

/-- Despite strict second-level concavity, the reflected fifth-root curvature is negative. -/
theorem quarticGaussianReflectedProfile_fifthRootCurvature_neg :
    fifthRootDividedDropCurvatureNumerator quarticGaussianReflectedProfile (1 / 2) < 0 := by
  let p := Real.exp (-(1 / 8 : ℝ))
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hp1 : p < 1 := by
    dsimp [p]
    rw [Real.exp_lt_one_iff]
    norm_num
  have hprod : p * Real.exp (1 / 8 : ℝ) = 1 := by
    dsimp [p]
    rw [← Real.exp_add]
    norm_num
  have hpLower : 7 / 8 < p := by
    have hmul := mul_lt_mul_of_pos_left exp_one_eighth_lt_eight_sevenths hp0
    nlinarith
  have hpoly : 85 * p ^ 2 - 185 * p + 96 < 0 := by
    have hfactor : 85 * p ^ 2 - 185 * p + 96 =
        -(51 / 64 : ℝ) +
          (p - 7 / 8) * (85 * (p + 7 / 8) - 185) := by ring
    have hcoeff : 85 * (p + 7 / 8) - 185 < 0 := by nlinarith
    have hmulNeg : (p - 7 / 8) * (85 * (p + 7 / 8) - 185) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hpLower) hcoeff
    rw [hfactor]
    linarith
  unfold fifthRootDividedDropCurvatureNumerator
  rw [iteratedDeriv_one_quarticGaussianReflectedProfile,
    iteratedDeriv_two_quarticGaussianReflectedProfile]
  norm_num [quarticGaussianReflectedProfile]
  change 24 * (1 - p) ^ 2 - 9 / 2 * (1 - p) * p +
      1 / 4 * (5 * (1 - p) * (5 * p) - 4 * p ^ 2) < 0
  nlinarith

theorem quarticGaussianKernel_pos (x : ℝ) :
    0 < quarticGaussianKernel x := by
  unfold quarticGaussianKernel
  positivity

theorem quarticGaussianKernel_even : Function.Even quarticGaussianKernel := by
  intro x
  unfold quarticGaussianKernel
  congr 1
  ring

theorem quadraticGaussianRadialProfile_eq_quarticGaussianKernel_sqrt
    {x : ℝ} (hx : 0 ≤ x) :
    quadraticGaussianRadialProfile x = quarticGaussianKernel (Real.sqrt x) := by
  unfold quadraticGaussianRadialProfile quarticGaussianKernel
  congr 1
  rw [show Real.sqrt x ^ 4 = (Real.sqrt x ^ 2) ^ 2 by ring,
    Real.sq_sqrt hx]

theorem firstLaguerreExpression_quadraticGaussianRadialProfile_pos (x : ℝ) :
    0 < firstLaguerreExpression quadraticGaussianRadialProfile x := by
  rw [firstLaguerreExpression_quadraticGaussianRadialProfile]
  positivity

theorem quarticGaussianReflectedProfile_eq_kernel_mul (x : ℝ) :
    quarticGaussianReflectedProfile x =
      quarticGaussianKernel x * quarticGaussianKernel (-x) := by
  unfold quarticGaussianReflectedProfile quarticGaussianKernel
  rw [← Real.exp_add]
  congr 1
  ring

/-- **No-go capstone.**  A positive even kernel can have a radial profile with a positive first
Laguerre expression and globally strict second-level logarithmic concavity while its centered
reflected product has negative fifth-root divided-drop curvature. -/
theorem exists_secondLevelStrict_kernel_with_fifthRootCurvatureFailure :
    ∃ (F s P : ℝ → ℝ),
      (∀ x, 0 < F x) ∧
      Function.Even F ∧
      (∀ x, 0 ≤ x → s x = F (Real.sqrt x)) ∧
      (∀ x, 0 < firstLaguerreExpression s x) ∧
      (∀ x, iteratedDeriv 2
        (fun y => Real.log (firstLaguerreExpression s y)) x < 0) ∧
      (∀ x, P x = F x * F (-x)) ∧
      fifthRootDividedDropCurvatureNumerator P (1 / 2) < 0 := by
  refine ⟨quarticGaussianKernel, quadraticGaussianRadialProfile,
    quarticGaussianReflectedProfile, quarticGaussianKernel_pos,
    quarticGaussianKernel_even, ?_, ?_, ?_,
    quarticGaussianReflectedProfile_eq_kernel_mul,
    quarticGaussianReflectedProfile_fifthRootCurvature_neg⟩
  · intro x hx
    exact quadraticGaussianRadialProfile_eq_quarticGaussianKernel_sqrt hx
  · exact firstLaguerreExpression_quadraticGaussianRadialProfile_pos
  · exact quadraticGaussianRadialProfile_secondLevel_strict

end

end HilbertMetric
