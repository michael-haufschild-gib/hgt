import GaloisForLFunctions.HilbertMetric.SecondLevelConcavityFifthRootNoGo
import GaloisForLFunctions.HilbertMetric.RiccatiCorrelationAngle
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Second-level plus Riccati concavity still does not force global fifth-root curvature

This module strengthens `SecondLevelConcavityFifthRootNoGo`.  The positive even kernel

`F(t) = exp (-(t^2 + t^4/10 + t^6/2))`

has all three source-independent properties currently available to the reflected fifth-root
route:

* its radial profile has a positive first Laguerre expression and strictly negative second
  logarithmic curvature on the physical half-line;
* its normalized action has a globally nonnegative Riccati margin, hence a concave correlation
  angle on every nonnegative compact interval;
* its reflected profile has positive second--sixth Hankel determinant, so C5 is strictly positive
  immediately to the right of the cusp.

Nevertheless C5 is strictly negative at `t = sqrt (1/2)`.  Therefore these three facts, even in
combination, cannot close the global fifth-root route.  A successful proof must use information
specific to the completed-theta atom--likelihood decomposition.
-/

open Set

namespace HilbertMetric

noncomputable section

private theorem exp_fortyseven_fortieth_lt_eightyone_twentyfifth :
    Real.exp (47 / 40 : ℝ) < 81 / 25 := by
  have hb := Real.exp_bound (x := (47 / 80 : ℝ)) (by norm_num)
    (n := 10) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  have hhalf : Real.exp (47 / 80 : ℝ) < 9 / 5 := by
    nlinarith [le_abs_self
      (Real.exp (47 / 80 : ℝ) -
        (1 + (47 / 80 : ℝ) + (47 / 80 : ℝ) ^ 2 / 2 +
          (47 / 80 : ℝ) ^ 3 / 6 + (47 / 80 : ℝ) ^ 4 / 24 +
          (47 / 80 : ℝ) ^ 5 / 120 + (47 / 80 : ℝ) ^ 6 / 720 +
          (47 / 80 : ℝ) ^ 7 / 5040 + (47 / 80 : ℝ) ^ 8 / 40320 +
          (47 / 80 : ℝ) ^ 9 / 362880))]
  rw [show (47 / 40 : ℝ) = 47 / 80 + 47 / 80 by ring, Real.exp_add]
  nlinarith [Real.exp_pos (47 / 80 : ℝ)]

/-- Exact scalar sign at the later C5-failure point. -/
theorem sexticGaussianC5ActionPolynomial_neg :
    let r := Real.exp (47 / 40 : ℝ) - 1
    24 * r ^ 2 - 613 / 16 * r - 3481 / 100 < 0 := by
  dsimp
  let r := Real.exp (47 / 40 : ℝ) - 1
  have hrUpper : r < 56 / 25 := by
    dsimp [r]
    linarith [exp_fortyseven_fortieth_lt_eightyone_twentyfifth]
  have hrLower : 1 < r := by
    dsimp [r]
    have h := Real.add_one_lt_exp (by norm_num : (47 / 40 : ℝ) ≠ 0)
    nlinarith
  have hmono : 0 < 48 * r - 613 / 16 := by nlinarith
  have hfactor :
      (24 * (56 / 25 : ℝ) ^ 2 - 613 / 16 * (56 / 25 : ℝ) - 3481 / 100) -
          (24 * r ^ 2 - 613 / 16 * r - 3481 / 100) =
        ((56 / 25 : ℝ) - r) * (24 * ((56 / 25 : ℝ) + r) - 613 / 16) := by
    ring
  have hfactorPos :
      0 < ((56 / 25 : ℝ) - r) * (24 * ((56 / 25 : ℝ) + r) - 613 / 16) := by
    apply mul_pos
    · linarith
    · nlinarith
  rw [← hfactor] at hfactorPos
  norm_num at hfactorPos ⊢
  linarith

def sexticGaussianAction (t : ℝ) : ℝ := 2 * t ^ 2 + t ^ 4 / 5 + t ^ 6

def sexticGaussianActionOne (t : ℝ) : ℝ := 4 * t + 4 / 5 * t ^ 3 + 6 * t ^ 5

def sexticGaussianActionTwo (t : ℝ) : ℝ := 4 + 12 / 5 * t ^ 2 + 30 * t ^ 4

def sexticGaussianActionThree (t : ℝ) : ℝ := 24 / 5 * t + 120 * t ^ 3

theorem sexticGaussianAction_riccatiMargin_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 2 * sexticGaussianActionOne t * sexticGaussianActionTwo t -
      sexticGaussianActionThree t := by
  have hy : 0 ≤ t ^ 2 := sq_nonneg t
  have hquad : 0 < 680 - 2360 * t ^ 2 + 7296 * (t ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (7296 * t ^ 2 - 1180)]
  unfold sexticGaussianActionOne sexticGaussianActionTwo sexticGaussianActionThree
  have hfactor :
      2 * (4 * t + 4 / 5 * t ^ 3 + 6 * t ^ 5) *
          (4 + 12 / 5 * t ^ 2 + 30 * t ^ 4) -
          (24 / 5 * t + 120 * t ^ 3) =
        t / 25 *
          (680 - 2360 * t ^ 2 + 7296 * (t ^ 2) ^ 2 +
            1920 * (t ^ 2) ^ 3 + 9000 * (t ^ 2) ^ 4) := by
    ring
  rw [hfactor]
  positivity

theorem hasDerivAt_sexticGaussianAction (t : ℝ) :
    HasDerivAt sexticGaussianAction (sexticGaussianActionOne t) t := by
  unfold sexticGaussianAction sexticGaussianActionOne
  have hraw := (((hasDerivAt_id t).pow 2).const_mul 2).add
    (((hasDerivAt_id t).pow 4).div_const 5 |>.add ((hasDerivAt_id t).pow 6))
  rw [show (fun y : ℝ => 2 * y ^ 2 + y ^ 4 / 5 + y ^ 6) =
      (fun y => 2 * (id ^ 2) y) +
        ((fun y => (id ^ 4) y / 5) + id ^ 6) by
      funext y
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]
      ring]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_sexticGaussianActionOne (t : ℝ) :
    HasDerivAt sexticGaussianActionOne (sexticGaussianActionTwo t) t := by
  unfold sexticGaussianActionOne sexticGaussianActionTwo
  have hraw := ((hasDerivAt_id t).const_mul 4).add
    ((((hasDerivAt_id t).pow 3).const_mul (4 / 5 : ℝ)).add
      (((hasDerivAt_id t).pow 5).const_mul 6))
  rw [show (fun y : ℝ => 4 * y + 4 / 5 * y ^ 3 + 6 * y ^ 5) =
      (fun y => 4 * id y) +
        ((fun y => (4 / 5 : ℝ) * (id ^ 3) y) +
          fun y => 6 * (id ^ 5) y) by
      funext y
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]
      ring]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_sexticGaussianActionTwo (t : ℝ) :
    HasDerivAt sexticGaussianActionTwo (sexticGaussianActionThree t) t := by
  unfold sexticGaussianActionTwo sexticGaussianActionThree
  have hraw := (hasDerivAt_const t 4).add
    ((((hasDerivAt_id t).pow 2).const_mul (12 / 5 : ℝ)).add
      (((hasDerivAt_id t).pow 4).const_mul 30))
  rw [show (fun y : ℝ => 4 + 12 / 5 * y ^ 2 + 30 * y ^ 4) =
      (fun _ : ℝ => 4) +
        ((fun y => (12 / 5 : ℝ) * (id ^ 2) y) +
          fun y => 30 * (id ^ 4) y) by
      funext y
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]
      ring]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

/-- Positive even kernel with a cubic action in the squared coordinate. -/
def sexticGaussianKernel (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2 + t ^ 4 / 10 + t ^ 6 / 2))

/-- Centered reflected product of `sexticGaussianKernel`. -/
def sexticGaussianReflectedProfile (t : ℝ) : ℝ :=
  Real.exp (-sexticGaussianAction t)

theorem hasDerivAt_sexticGaussianReflectedProfile (t : ℝ) :
    HasDerivAt sexticGaussianReflectedProfile
      (-sexticGaussianActionOne t * sexticGaussianReflectedProfile t) t := by
  have h := ((hasDerivAt_sexticGaussianAction t).neg).exp
  rw [show sexticGaussianReflectedProfile =
      (fun y => Real.exp (-sexticGaussianAction y)) by rfl]
  convert h using 1
  all_goals simp only [Pi.neg_apply]
  all_goals ring

theorem iteratedDeriv_one_sexticGaussianReflectedProfile (t : ℝ) :
    iteratedDeriv 1 sexticGaussianReflectedProfile t =
      -sexticGaussianActionOne t * sexticGaussianReflectedProfile t := by
  rw [iteratedDeriv_one, (hasDerivAt_sexticGaussianReflectedProfile t).deriv]

theorem iteratedDeriv_two_sexticGaussianReflectedProfile (t : ℝ) :
    iteratedDeriv 2 sexticGaussianReflectedProfile t =
      (sexticGaussianActionOne t ^ 2 - sexticGaussianActionTwo t) *
        sexticGaussianReflectedProfile t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hfun : deriv sexticGaussianReflectedProfile = fun y =>
      -sexticGaussianActionOne y * sexticGaussianReflectedProfile y := by
    funext y
    exact (hasDerivAt_sexticGaussianReflectedProfile y).deriv
  rw [hfun]
  have h := (hasDerivAt_sexticGaussianActionOne t).neg.mul
    (hasDerivAt_sexticGaussianReflectedProfile t)
  have h' : HasDerivAt
      (fun y => -sexticGaussianActionOne y * sexticGaussianReflectedProfile y)
      (-sexticGaussianActionTwo t * sexticGaussianReflectedProfile t +
        (-sexticGaussianActionOne t) *
          (-sexticGaussianActionOne t * sexticGaussianReflectedProfile t)) t := by
    convert h using 1 <;> rfl
  rw [h'.deriv]
  ring

theorem sexticGaussianCorrelationAngle_concaveOn {T : ℝ} (hT : 0 ≤ T) :
    ConcaveOn ℝ (Icc 0 T) (riccatiCorrelationAngle sexticGaussianAction) := by
  apply concaveOn_riccatiCorrelationAngle_of_margin_nonneg
    (q := sexticGaussianAction)
    (q₁ := sexticGaussianActionOne)
    (q₂ := sexticGaussianActionTwo)
    (q₃ := sexticGaussianActionThree)
    hT
  · norm_num [sexticGaussianAction]
  · norm_num [sexticGaussianActionOne]
  · exact fun t _ => hasDerivAt_sexticGaussianAction t
  · exact fun t _ => hasDerivAt_sexticGaussianActionOne t
  · exact fun t _ => hasDerivAt_sexticGaussianActionTwo t
  · intro t ht
    unfold sexticGaussianAction
    positivity
  · intro t ht
    rw [interior_Icc] at ht
    unfold sexticGaussianAction
    have : 0 < t ^ 2 := sq_pos_of_pos ht.1
    positivity
  · intro t ht
    exact sexticGaussianAction_riccatiMargin_nonneg ht.1

theorem sexticGaussianReflectedProfile_fifthRootCurvature_neg :
    fifthRootDividedDropCurvatureNumerator sexticGaussianReflectedProfile
      (Real.sqrt (1 / 2)) < 0 := by
  let t : ℝ := Real.sqrt (1 / 2)
  let p : ℝ := Real.exp (-(47 / 40 : ℝ))
  let r : ℝ := Real.exp (47 / 40 : ℝ) - 1
  have htSq : t ^ 2 = 1 / 2 := by
    dsimp [t]
    rw [Real.sq_sqrt]
    norm_num
  have htFour : t ^ 4 = 1 / 4 := by nlinarith [sq_nonneg (t ^ 2 - 1 / 2)]
  have htSix : t ^ 6 = 1 / 8 := by
    calc
      t ^ 6 = t ^ 4 * t ^ 2 := by ring
      _ = 1 / 8 := by rw [htFour, htSq]; norm_num
  have hq : sexticGaussianAction t = 47 / 40 := by
    unfold sexticGaussianAction
    rw [htSq, htFour, htSix]
    norm_num
  have hqOne : t * sexticGaussianActionOne t = 59 / 20 := by
    unfold sexticGaussianActionOne
    calc
      t * (4 * t + 4 / 5 * t ^ 3 + 6 * t ^ 5) =
          4 * t ^ 2 + 4 / 5 * t ^ 4 + 6 * t ^ 6 := by ring
      _ = 59 / 20 := by rw [htSq, htFour, htSix]; norm_num
  have hqTwo : t ^ 2 * sexticGaussianActionTwo t = 127 / 20 := by
    unfold sexticGaussianActionTwo
    calc
      t ^ 2 * (4 + 12 / 5 * t ^ 2 + 30 * t ^ 4) =
          4 * t ^ 2 + 12 / 5 * t ^ 4 + 30 * t ^ 6 := by ring
      _ = 127 / 20 := by rw [htSq, htFour, htSix]; norm_num
  have hP : sexticGaussianReflectedProfile t = p := by
    dsimp [p]
    unfold sexticGaussianReflectedProfile
    rw [hq]
  have hPzero : sexticGaussianReflectedProfile 0 = 1 := by
    norm_num [sexticGaussianReflectedProfile, sexticGaussianAction]
  have hpPos : 0 < p := by dsimp [p]; positivity
  have hpr : 1 - p = p * r := by
    dsimp [p, r]
    rw [mul_sub, ← Real.exp_add]
    norm_num
  have hpoly : 24 * r ^ 2 - 613 / 16 * r - 3481 / 100 < 0 :=
    sexticGaussianC5ActionPolynomial_neg
  have hformula :
      fifthRootDividedDropCurvatureNumerator sexticGaussianReflectedProfile t =
        p ^ 2 * (24 * r ^ 2 - 613 / 16 * r - 3481 / 100) := by
    unfold fifthRootDividedDropCurvatureNumerator
    rw [iteratedDeriv_one_sexticGaussianReflectedProfile,
      iteratedDeriv_two_sexticGaussianReflectedProfile,
      hPzero, hP]
    dsimp only
    rw [hpr]
    calc
      24 * (p * r) ^ 2 +
            9 * t * (p * r) * (-sexticGaussianActionOne t * p) +
            t ^ 2 *
              (-5 * (p * r) *
                  ((sexticGaussianActionOne t ^ 2 - sexticGaussianActionTwo t) * p) -
                4 * (-sexticGaussianActionOne t * p) ^ 2) =
          p ^ 2 *
            (24 * r ^ 2 - 9 * r * (t * sexticGaussianActionOne t) +
              5 * r *
                (t ^ 2 * sexticGaussianActionTwo t -
                  (t * sexticGaussianActionOne t) ^ 2) -
              4 * (t * sexticGaussianActionOne t) ^ 2) := by ring
      _ = p ^ 2 * (24 * r ^ 2 - 613 / 16 * r - 3481 / 100) := by
        rw [hqOne, hqTwo]
        ring
  rw [hformula]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos hpPos) hpoly

theorem sexticGaussianKernel_reflected (t : ℝ) :
    sexticGaussianReflectedProfile t =
      sexticGaussianKernel t * sexticGaussianKernel (-t) := by
  unfold sexticGaussianReflectedProfile sexticGaussianAction sexticGaussianKernel
  rw [← Real.exp_add]
  congr 1
  ring

/-- Cubic squared-coordinate action whose exponential is the kernel's radial profile. -/
def cubicGaussianRadialAction (x : ℝ) : ℝ := x + x ^ 2 / 10 + x ^ 3 / 2

def cubicGaussianRadialActionOne (x : ℝ) : ℝ := 1 + x / 5 + 3 / 2 * x ^ 2

def cubicGaussianRadialActionTwo (x : ℝ) : ℝ := 1 / 5 + 3 * x

def cubicGaussianRadialProfile (x : ℝ) : ℝ := Real.exp (-cubicGaussianRadialAction x)

theorem hasDerivAt_cubicGaussianRadialAction (x : ℝ) :
    HasDerivAt cubicGaussianRadialAction (cubicGaussianRadialActionOne x) x := by
  unfold cubicGaussianRadialAction cubicGaussianRadialActionOne
  have hraw := (hasDerivAt_id x).add
    (((hasDerivAt_id x).pow 2).div_const 10 |>.add
      (((hasDerivAt_id x).pow 3).div_const 2))
  rw [show (fun y : ℝ => y + y ^ 2 / 10 + y ^ 3 / 2) =
      id + ((fun y => (id ^ 2) y / 10) + fun y => (id ^ 3) y / 2) by
      funext y
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]
      ring]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_cubicGaussianRadialActionOne (x : ℝ) :
    HasDerivAt cubicGaussianRadialActionOne (cubicGaussianRadialActionTwo x) x := by
  unfold cubicGaussianRadialActionOne cubicGaussianRadialActionTwo
  have hraw := (hasDerivAt_const x 1).add
    ((hasDerivAt_id x).div_const 5 |>.add
      (((hasDerivAt_id x).pow 2).const_mul (3 / 2 : ℝ)))
  rw [show (fun y : ℝ => 1 + y / 5 + 3 / 2 * y ^ 2) =
      (fun _ : ℝ => 1) + ((fun y => id y / 5) +
        fun y => (3 / 2 : ℝ) * (id ^ 2) y) by
      funext y
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]
      ring]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_cubicGaussianRadialActionTwo (x : ℝ) :
    HasDerivAt cubicGaussianRadialActionTwo 3 x := by
  unfold cubicGaussianRadialActionTwo
  have hraw := (hasDerivAt_const x (1 / 5 : ℝ)).add
    ((hasDerivAt_id x).const_mul 3)
  rw [show (fun y : ℝ => 1 / 5 + 3 * y) =
      (fun _ : ℝ => 1 / 5) + fun y => 3 * id y by
      funext y
      simp only [Pi.add_apply, id_eq]]
  refine hraw.congr_deriv ?_
  norm_num

theorem hasDerivAt_cubicGaussianRadialProfile (x : ℝ) :
    HasDerivAt cubicGaussianRadialProfile
      (-cubicGaussianRadialActionOne x * cubicGaussianRadialProfile x) x := by
  have h := ((hasDerivAt_cubicGaussianRadialAction x).neg).exp
  rw [show cubicGaussianRadialProfile =
      (fun y => Real.exp (-cubicGaussianRadialAction y)) by rfl]
  convert h using 1
  all_goals simp only [Pi.neg_apply]
  all_goals ring

theorem iteratedDeriv_one_cubicGaussianRadialProfile (x : ℝ) :
    iteratedDeriv 1 cubicGaussianRadialProfile x =
      -cubicGaussianRadialActionOne x * cubicGaussianRadialProfile x := by
  rw [iteratedDeriv_one, (hasDerivAt_cubicGaussianRadialProfile x).deriv]

theorem iteratedDeriv_two_cubicGaussianRadialProfile (x : ℝ) :
    iteratedDeriv 2 cubicGaussianRadialProfile x =
      (cubicGaussianRadialActionOne x ^ 2 - cubicGaussianRadialActionTwo x) *
        cubicGaussianRadialProfile x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hfun : deriv cubicGaussianRadialProfile = fun y =>
      -cubicGaussianRadialActionOne y * cubicGaussianRadialProfile y := by
    funext y
    exact (hasDerivAt_cubicGaussianRadialProfile y).deriv
  rw [hfun]
  have h := (hasDerivAt_cubicGaussianRadialActionOne x).neg.mul
    (hasDerivAt_cubicGaussianRadialProfile x)
  have h' : HasDerivAt
      (fun y => -cubicGaussianRadialActionOne y * cubicGaussianRadialProfile y)
      (-cubicGaussianRadialActionTwo x * cubicGaussianRadialProfile x +
        (-cubicGaussianRadialActionOne x) *
          (-cubicGaussianRadialActionOne x * cubicGaussianRadialProfile x)) x := by
    convert h using 1 <;> rfl
  rw [h'.deriv]
  ring

theorem firstLaguerreExpression_cubicGaussianRadialProfile (x : ℝ) :
    firstLaguerreExpression cubicGaussianRadialProfile x =
      cubicGaussianRadialActionTwo x *
        Real.exp (-2 * cubicGaussianRadialAction x) := by
  unfold firstLaguerreExpression
  rw [iteratedDeriv_one_cubicGaussianRadialProfile,
    iteratedDeriv_two_cubicGaussianRadialProfile]
  unfold cubicGaussianRadialProfile
  have hexp : Real.exp (-2 * cubicGaussianRadialAction x) =
      Real.exp (-cubicGaussianRadialAction x) ^ 2 := by
    rw [show -2 * cubicGaussianRadialAction x =
        -cubicGaussianRadialAction x + -cubicGaussianRadialAction x by ring,
      Real.exp_add]
    ring
  rw [hexp]
  ring

theorem firstLaguerreExpression_cubicGaussianRadialProfile_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < firstLaguerreExpression cubicGaussianRadialProfile x := by
  rw [firstLaguerreExpression_cubicGaussianRadialProfile]
  unfold cubicGaussianRadialActionTwo
  positivity

theorem iteratedDeriv_one_log_firstLaguerre_cubicGaussianRadialProfile
    {x : ℝ} (hx : 0 < cubicGaussianRadialActionTwo x) :
    iteratedDeriv 1
        (fun y => Real.log (firstLaguerreExpression cubicGaussianRadialProfile y)) x =
      3 / cubicGaussianRadialActionTwo x - 2 * cubicGaussianRadialActionOne x := by
  rw [iteratedDeriv_one]
  have hExp := ((hasDerivAt_cubicGaussianRadialAction x).const_mul (-2)).exp
  have hProd := (hasDerivAt_cubicGaussianRadialActionTwo x).mul hExp
  have hL : HasDerivAt
      (fun y => cubicGaussianRadialActionTwo y *
        Real.exp (-2 * cubicGaussianRadialAction y))
      ((3 - 2 * cubicGaussianRadialActionTwo x * cubicGaussianRadialActionOne x) *
        Real.exp (-2 * cubicGaussianRadialAction x)) x := by
    rw [show (fun y => cubicGaussianRadialActionTwo y *
        Real.exp (-2 * cubicGaussianRadialAction y)) =
      cubicGaussianRadialActionTwo *
        fun y => Real.exp (-2 * cubicGaussianRadialAction y) by
      funext y
      rfl]
    refine hProd.congr_deriv ?_
    ring
  have hfun : (fun y => firstLaguerreExpression cubicGaussianRadialProfile y) =
      fun y => cubicGaussianRadialActionTwo y *
        Real.exp (-2 * cubicGaussianRadialAction y) := by
    funext y
    exact firstLaguerreExpression_cubicGaussianRadialProfile y
  have hL' : HasDerivAt
      (fun y => firstLaguerreExpression cubicGaussianRadialProfile y)
      ((3 - 2 * cubicGaussianRadialActionTwo x * cubicGaussianRadialActionOne x) *
        Real.exp (-2 * cubicGaussianRadialAction x)) x := by
    rw [hfun]
    exact hL
  have hLne : firstLaguerreExpression cubicGaussianRadialProfile x ≠ 0 := by
    rw [firstLaguerreExpression_cubicGaussianRadialProfile]
    positivity
  have hlog := HasDerivAt.log hL' hLne
  rw [hlog.deriv]
  rw [firstLaguerreExpression_cubicGaussianRadialProfile]
  field_simp [hx.ne', Real.exp_ne_zero]

theorem cubicGaussianRadialProfile_secondLevelLogCurvature
    {x : ℝ} (hx : 0 ≤ x) :
    iteratedDeriv 2
        (fun y => Real.log (firstLaguerreExpression cubicGaussianRadialProfile y)) x =
      -9 / cubicGaussianRadialActionTwo x ^ 2 -
        2 * cubicGaussianRadialActionTwo x := by
  rw [iteratedDeriv_succ]
  have hthreshold : (-1 / 15 : ℝ) < x := by linarith
  have hEq : deriv
      (fun y => Real.log (firstLaguerreExpression cubicGaussianRadialProfile y)) =ᶠ[nhds x]
      fun y => 3 / cubicGaussianRadialActionTwo y -
        2 * cubicGaussianRadialActionOne y := by
    filter_upwards [eventually_gt_nhds hthreshold] with y hy
    have hyTwo : 0 < cubicGaussianRadialActionTwo y := by
      unfold cubicGaussianRadialActionTwo
      linarith
    simpa only [iteratedDeriv_one] using
      iteratedDeriv_one_log_firstLaguerre_cubicGaussianRadialProfile hyTwo
  rw [iteratedDeriv_one, hEq.deriv_eq]
  have hDiv := (hasDerivAt_const x (3 : ℝ)).div
    (hasDerivAt_cubicGaussianRadialActionTwo x)
    (by
      unfold cubicGaussianRadialActionTwo
      nlinarith)
  have hSub := hDiv.sub
    ((hasDerivAt_cubicGaussianRadialActionOne x).const_mul 2)
  have hSub' : HasDerivAt
      (fun y => 3 / cubicGaussianRadialActionTwo y -
        2 * cubicGaussianRadialActionOne y)
      ((0 * cubicGaussianRadialActionTwo x - 3 * 3) /
          cubicGaussianRadialActionTwo x ^ 2 -
        2 * cubicGaussianRadialActionTwo x) x := by
    rw [show (fun y => 3 / cubicGaussianRadialActionTwo y -
        2 * cubicGaussianRadialActionOne y) =
      (fun _ : ℝ => 3) / cubicGaussianRadialActionTwo -
        fun y => 2 * cubicGaussianRadialActionOne y by
      funext y
      rfl]
    exact hSub
  rw [hSub'.deriv]
  ring

theorem cubicGaussianRadialProfile_secondLevel_strict
    {x : ℝ} (hx : 0 ≤ x) :
    iteratedDeriv 2
        (fun y => Real.log (firstLaguerreExpression cubicGaussianRadialProfile y)) x < 0 := by
  rw [cubicGaussianRadialProfile_secondLevelLogCurvature hx]
  have hTwo : 0 < cubicGaussianRadialActionTwo x := by
    unfold cubicGaussianRadialActionTwo
    positivity
  have hsq : 0 < cubicGaussianRadialActionTwo x ^ 2 := sq_pos_of_pos hTwo
  have hfirst : -9 / cubicGaussianRadialActionTwo x ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hsq
  nlinarith

def sexticGaussianActionFour (t : ℝ) : ℝ := 24 / 5 + 360 * t ^ 2

def sexticGaussianActionFive (t : ℝ) : ℝ := 720 * t

def sexticGaussianActionSix (_t : ℝ) : ℝ := 720

theorem hasDerivAt_sexticGaussianActionThree (t : ℝ) :
    HasDerivAt sexticGaussianActionThree (sexticGaussianActionFour t) t := by
  unfold sexticGaussianActionThree sexticGaussianActionFour
  have hraw := ((hasDerivAt_id t).const_mul (24 / 5 : ℝ)).add
    (((hasDerivAt_id t).pow 3).const_mul 120)
  rw [show (fun y : ℝ => 24 / 5 * y + 120 * y ^ 3) =
      (fun y => (24 / 5 : ℝ) * id y) + fun y => 120 * (id ^ 3) y by
      funext y
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_sexticGaussianActionFour (t : ℝ) :
    HasDerivAt sexticGaussianActionFour (sexticGaussianActionFive t) t := by
  unfold sexticGaussianActionFour sexticGaussianActionFive
  have hraw := (hasDerivAt_const t (24 / 5 : ℝ)).add
    (((hasDerivAt_id t).pow 2).const_mul 360)
  rw [show (fun y : ℝ => 24 / 5 + 360 * y ^ 2) =
      (fun _ : ℝ => 24 / 5) + fun y => 360 * (id ^ 2) y by
      funext y
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_sexticGaussianActionFive (t : ℝ) :
    HasDerivAt sexticGaussianActionFive (sexticGaussianActionSix t) t := by
  unfold sexticGaussianActionFive sexticGaussianActionSix
  have hraw := (hasDerivAt_id t).const_mul 720
  rw [show (fun y : ℝ => 720 * y) = fun y => 720 * id y by
    funext y
    rfl]
  refine hraw.congr_deriv ?_
  norm_num

def sexticGaussianJetTwo (t : ℝ) : ℝ :=
  sexticGaussianActionOne t ^ 2 - sexticGaussianActionTwo t

def sexticGaussianJetThree (t : ℝ) : ℝ :=
  -sexticGaussianActionOne t ^ 3 +
    3 * sexticGaussianActionOne t * sexticGaussianActionTwo t -
    sexticGaussianActionThree t

def sexticGaussianJetFour (t : ℝ) : ℝ :=
  sexticGaussianActionOne t ^ 4 -
    6 * sexticGaussianActionOne t ^ 2 * sexticGaussianActionTwo t +
    3 * sexticGaussianActionTwo t ^ 2 +
    4 * sexticGaussianActionOne t * sexticGaussianActionThree t -
    sexticGaussianActionFour t

def sexticGaussianJetFive (t : ℝ) : ℝ :=
  -sexticGaussianActionOne t ^ 5 +
    10 * sexticGaussianActionOne t ^ 3 * sexticGaussianActionTwo t -
    15 * sexticGaussianActionOne t * sexticGaussianActionTwo t ^ 2 -
    10 * sexticGaussianActionOne t ^ 2 * sexticGaussianActionThree t +
    10 * sexticGaussianActionTwo t * sexticGaussianActionThree t +
    5 * sexticGaussianActionOne t * sexticGaussianActionFour t -
    sexticGaussianActionFive t

def sexticGaussianJetSix (t : ℝ) : ℝ :=
  sexticGaussianActionOne t ^ 6 -
    15 * sexticGaussianActionOne t ^ 4 * sexticGaussianActionTwo t +
    45 * sexticGaussianActionOne t ^ 2 * sexticGaussianActionTwo t ^ 2 -
    15 * sexticGaussianActionTwo t ^ 3 +
    20 * sexticGaussianActionOne t ^ 3 * sexticGaussianActionThree t -
    60 * sexticGaussianActionOne t * sexticGaussianActionTwo t *
      sexticGaussianActionThree t +
    10 * sexticGaussianActionThree t ^ 2 -
    15 * sexticGaussianActionOne t ^ 2 * sexticGaussianActionFour t +
    15 * sexticGaussianActionTwo t * sexticGaussianActionFour t +
    6 * sexticGaussianActionOne t * sexticGaussianActionFive t -
    sexticGaussianActionSix t

theorem hasDerivAt_sexticGaussianJetTwo (t : ℝ) :
    HasDerivAt sexticGaussianJetTwo
      (sexticGaussianJetThree t +
        sexticGaussianActionOne t * sexticGaussianJetTwo t) t := by
  unfold sexticGaussianJetTwo
  have hraw := (hasDerivAt_sexticGaussianActionOne t).pow 2 |>.sub
    (hasDerivAt_sexticGaussianActionTwo t)
  rw [show (fun y => sexticGaussianActionOne y ^ 2 - sexticGaussianActionTwo y) =
      sexticGaussianActionOne ^ 2 - sexticGaussianActionTwo by
      funext y
      rfl]
  refine hraw.congr_deriv ?_
  unfold sexticGaussianJetThree
  norm_num
  ring

theorem hasDerivAt_sexticGaussianJetThree (t : ℝ) :
    HasDerivAt sexticGaussianJetThree
      (sexticGaussianJetFour t +
        sexticGaussianActionOne t * sexticGaussianJetThree t) t := by
  unfold sexticGaussianJetThree
  have hraw := ((hasDerivAt_sexticGaussianActionOne t).pow 3).neg |>.add
    (((hasDerivAt_sexticGaussianActionOne t).mul
      (hasDerivAt_sexticGaussianActionTwo t)).const_mul 3) |>.sub
    (hasDerivAt_sexticGaussianActionThree t)
  rw [show (fun y => -sexticGaussianActionOne y ^ 3 +
        3 * sexticGaussianActionOne y * sexticGaussianActionTwo y -
        sexticGaussianActionThree y) =
      -(sexticGaussianActionOne ^ 3) +
          (fun y => 3 * (sexticGaussianActionOne * sexticGaussianActionTwo) y) -
        sexticGaussianActionThree by
      funext y
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.pow_apply, Pi.mul_apply]
      ring]
  refine hraw.congr_deriv ?_
  unfold sexticGaussianJetFour
  norm_num
  ring

theorem hasDerivAt_sexticGaussianJetFour (t : ℝ) :
    HasDerivAt sexticGaussianJetFour
      (sexticGaussianJetFive t +
        sexticGaussianActionOne t * sexticGaussianJetFour t) t := by
  unfold sexticGaussianJetFour
  have hraw := ((((hasDerivAt_sexticGaussianActionOne t).pow 4).sub
      ((((hasDerivAt_sexticGaussianActionOne t).pow 2).mul
        (hasDerivAt_sexticGaussianActionTwo t)).const_mul 6)).add
      (((hasDerivAt_sexticGaussianActionTwo t).pow 2).const_mul 3)).add
      (((hasDerivAt_sexticGaussianActionOne t).mul
        (hasDerivAt_sexticGaussianActionThree t)).const_mul 4) |>.sub
      (hasDerivAt_sexticGaussianActionFour t)
  rw [show (fun y => sexticGaussianActionOne y ^ 4 -
        6 * sexticGaussianActionOne y ^ 2 * sexticGaussianActionTwo y +
        3 * sexticGaussianActionTwo y ^ 2 +
        4 * sexticGaussianActionOne y * sexticGaussianActionThree y -
        sexticGaussianActionFour y) =
      (((sexticGaussianActionOne ^ 4 -
          fun y => 6 * ((sexticGaussianActionOne ^ 2) * sexticGaussianActionTwo) y) +
        fun y => 3 * (sexticGaussianActionTwo ^ 2) y) +
        fun y => 4 * (sexticGaussianActionOne * sexticGaussianActionThree) y) -
        sexticGaussianActionFour by
      funext y
      simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Pi.mul_apply]
      ring]
  refine hraw.congr_deriv ?_
  unfold sexticGaussianJetFive
  norm_num
  ring

theorem hasDerivAt_sexticGaussianJetFive (t : ℝ) :
    HasDerivAt sexticGaussianJetFive
      (sexticGaussianJetSix t +
        sexticGaussianActionOne t * sexticGaussianJetFive t) t := by
  unfold sexticGaussianJetFive
  have h₁ := ((hasDerivAt_sexticGaussianActionOne t).pow 5).neg.add
    ((((hasDerivAt_sexticGaussianActionOne t).pow 3).mul
      (hasDerivAt_sexticGaussianActionTwo t)).const_mul 10)
  have h₂ := h₁.sub
    (((hasDerivAt_sexticGaussianActionOne t).mul
      ((hasDerivAt_sexticGaussianActionTwo t).pow 2)).const_mul 15)
  have h₃ := h₂.sub
    ((((hasDerivAt_sexticGaussianActionOne t).pow 2).mul
      (hasDerivAt_sexticGaussianActionThree t)).const_mul 10)
  have h₄ := h₃.add
    (((hasDerivAt_sexticGaussianActionTwo t).mul
      (hasDerivAt_sexticGaussianActionThree t)).const_mul 10)
  have h₅ := h₄.add
    (((hasDerivAt_sexticGaussianActionOne t).mul
      (hasDerivAt_sexticGaussianActionFour t)).const_mul 5)
  have hraw := h₅.sub (hasDerivAt_sexticGaussianActionFive t)
  rw [show (fun y => -sexticGaussianActionOne y ^ 5 +
        10 * sexticGaussianActionOne y ^ 3 * sexticGaussianActionTwo y -
        15 * sexticGaussianActionOne y * sexticGaussianActionTwo y ^ 2 -
        10 * sexticGaussianActionOne y ^ 2 * sexticGaussianActionThree y +
        10 * sexticGaussianActionTwo y * sexticGaussianActionThree y +
        5 * sexticGaussianActionOne y * sexticGaussianActionFour y -
        sexticGaussianActionFive y) =
      (((((-(sexticGaussianActionOne ^ 5) +
          fun y => 10 * ((sexticGaussianActionOne ^ 3) *
            sexticGaussianActionTwo) y) -
          fun y => 15 * (sexticGaussianActionOne *
            (sexticGaussianActionTwo ^ 2)) y) -
          fun y => 10 * ((sexticGaussianActionOne ^ 2) *
            sexticGaussianActionThree) y) +
          fun y => 10 * (sexticGaussianActionTwo * sexticGaussianActionThree) y) +
          fun y => 5 * (sexticGaussianActionOne * sexticGaussianActionFour) y) -
        sexticGaussianActionFive by
      funext y
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.pow_apply, Pi.mul_apply]
      ring]
  refine hraw.congr_deriv ?_
  unfold sexticGaussianJetSix
  norm_num
  ring

private theorem hasDerivAt_jet_mul_sexticGaussianReflectedProfile
    {c : ℝ → ℝ} {c' t : ℝ} (hc : HasDerivAt c c' t) :
    HasDerivAt (fun y => c y * sexticGaussianReflectedProfile y)
      ((c' - c t * sexticGaussianActionOne t) *
        sexticGaussianReflectedProfile t) t := by
  have hraw := hc.mul (hasDerivAt_sexticGaussianReflectedProfile t)
  rw [show (fun y => c y * sexticGaussianReflectedProfile y) =
      c * sexticGaussianReflectedProfile by
      funext y
      rfl]
  refine hraw.congr_deriv ?_
  ring

theorem iteratedDeriv_three_sexticGaussianReflectedProfile (t : ℝ) :
    iteratedDeriv 3 sexticGaussianReflectedProfile t =
      sexticGaussianJetThree t * sexticGaussianReflectedProfile t := by
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
    show iteratedDeriv 2 sexticGaussianReflectedProfile =
      fun y => sexticGaussianJetTwo y * sexticGaussianReflectedProfile y by
      funext y
      rw [iteratedDeriv_two_sexticGaussianReflectedProfile]
      rfl]
  have h := hasDerivAt_jet_mul_sexticGaussianReflectedProfile
    (hasDerivAt_sexticGaussianJetTwo t)
  rw [h.deriv]
  ring

theorem iteratedDeriv_four_sexticGaussianReflectedProfile (t : ℝ) :
    iteratedDeriv 4 sexticGaussianReflectedProfile t =
      sexticGaussianJetFour t * sexticGaussianReflectedProfile t := by
  rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ,
    show iteratedDeriv 3 sexticGaussianReflectedProfile =
      fun y => sexticGaussianJetThree y * sexticGaussianReflectedProfile y by
      funext y
      exact iteratedDeriv_three_sexticGaussianReflectedProfile y]
  have h := hasDerivAt_jet_mul_sexticGaussianReflectedProfile
    (hasDerivAt_sexticGaussianJetThree t)
  rw [h.deriv]
  ring

theorem iteratedDeriv_five_sexticGaussianReflectedProfile (t : ℝ) :
    iteratedDeriv 5 sexticGaussianReflectedProfile t =
      sexticGaussianJetFive t * sexticGaussianReflectedProfile t := by
  rw [show 5 = 4 + 1 by norm_num, iteratedDeriv_succ,
    show iteratedDeriv 4 sexticGaussianReflectedProfile =
      fun y => sexticGaussianJetFour y * sexticGaussianReflectedProfile y by
      funext y
      exact iteratedDeriv_four_sexticGaussianReflectedProfile y]
  have h := hasDerivAt_jet_mul_sexticGaussianReflectedProfile
    (hasDerivAt_sexticGaussianJetFour t)
  rw [h.deriv]
  ring

theorem iteratedDeriv_six_sexticGaussianReflectedProfile (t : ℝ) :
    iteratedDeriv 6 sexticGaussianReflectedProfile t =
      sexticGaussianJetSix t * sexticGaussianReflectedProfile t := by
  rw [show 6 = 5 + 1 by norm_num, iteratedDeriv_succ,
    show iteratedDeriv 5 sexticGaussianReflectedProfile =
      fun y => sexticGaussianJetFive y * sexticGaussianReflectedProfile y by
      funext y
      exact iteratedDeriv_five_sexticGaussianReflectedProfile y]
  have h := hasDerivAt_jet_mul_sexticGaussianReflectedProfile
    (hasDerivAt_sexticGaussianJetFive t)
  rw [h.deriv]
  ring

theorem contDiff_sexticGaussianReflectedProfile :
    ContDiff ℝ (⊤ : ℕ∞) sexticGaussianReflectedProfile := by
  unfold sexticGaussianReflectedProfile sexticGaussianAction
  fun_prop

theorem sexticGaussianReflectedProfile_even :
    Function.Even sexticGaussianReflectedProfile := by
  intro t
  unfold sexticGaussianReflectedProfile sexticGaussianAction
  congr 1
  ring

theorem sexticGaussianReflectedProfile_secondSixthHankel :
    iteratedDeriv 2 sexticGaussianReflectedProfile 0 *
          iteratedDeriv 6 sexticGaussianReflectedProfile 0 -
        iteratedDeriv 4 sexticGaussianReflectedProfile 0 ^ 2 = 92544 / 25 := by
  rw [iteratedDeriv_two_sexticGaussianReflectedProfile,
    iteratedDeriv_four_sexticGaussianReflectedProfile,
    iteratedDeriv_six_sexticGaussianReflectedProfile]
  norm_num [sexticGaussianJetTwo, sexticGaussianJetFour, sexticGaussianJetSix,
    sexticGaussianActionOne, sexticGaussianActionTwo, sexticGaussianActionThree,
    sexticGaussianActionFour, sexticGaussianActionFive, sexticGaussianActionSix,
    sexticGaussianReflectedProfile, sexticGaussianAction]

/-- C5 starts strictly positive at the cusp for the same profile that later violates C5. -/
theorem exists_sexticGaussianReflectedProfile_fifthRootCurvature_pos_right :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < fifthRootDividedDropCurvatureNumerator sexticGaussianReflectedProfile t := by
  apply exists_fifthRootDividedDropCurvatureNumerator_pos_right
    contDiff_sexticGaussianReflectedProfile sexticGaussianReflectedProfile_even
  rw [sexticGaussianReflectedProfile_secondSixthHankel]
  norm_num

theorem sexticGaussianKernel_pos (t : ℝ) : 0 < sexticGaussianKernel t := by
  unfold sexticGaussianKernel
  positivity

theorem sexticGaussianKernel_even : Function.Even sexticGaussianKernel := by
  intro t
  unfold sexticGaussianKernel
  congr 1
  ring

theorem cubicGaussianRadialProfile_eq_sexticGaussianKernel_sqrt
    {x : ℝ} (hx : 0 ≤ x) :
    cubicGaussianRadialProfile x = sexticGaussianKernel (Real.sqrt x) := by
  unfold cubicGaussianRadialProfile cubicGaussianRadialAction sexticGaussianKernel
  congr 1
  rw [show Real.sqrt x ^ 4 = (Real.sqrt x ^ 2) ^ 2 by ring,
    show Real.sqrt x ^ 6 = (Real.sqrt x ^ 2) ^ 3 by ring,
    Real.sq_sqrt hx]

/-- **Strengthened no-go.** Strict radial second-level concavity, a globally concave
correlation angle, and a strictly positive coalesced C5 chamber can coexist with a later C5
failure. Thus no combination of those three source-independent facts closes the fifth-root route;
additional completed-theta atom--likelihood information is indispensable. -/
theorem exists_secondLevelStrict_angleConcave_localC5Pos_kernel_with_globalC5Failure :
    ∃ (F s P q : ℝ → ℝ),
      (∀ x, 0 < F x) ∧
      Function.Even F ∧
      (∀ x, 0 ≤ x → s x = F (Real.sqrt x)) ∧
      (∀ x, 0 ≤ x → 0 < firstLaguerreExpression s x) ∧
      (∀ x, 0 ≤ x → iteratedDeriv 2
        (fun y => Real.log (firstLaguerreExpression s y)) x < 0) ∧
      (∀ x, P x = F x * F (-x)) ∧
      (∀ x, P x = Real.exp (-q x)) ∧
      (∀ T, 0 ≤ T → ConcaveOn ℝ (Icc 0 T) (riccatiCorrelationAngle q)) ∧
      (∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
        0 < fifthRootDividedDropCurvatureNumerator P t) ∧
      fifthRootDividedDropCurvatureNumerator P (Real.sqrt (1 / 2)) < 0 := by
  refine ⟨sexticGaussianKernel, cubicGaussianRadialProfile,
    sexticGaussianReflectedProfile, sexticGaussianAction,
    sexticGaussianKernel_pos, sexticGaussianKernel_even, ?_, ?_, ?_,
    sexticGaussianKernel_reflected, ?_, ?_,
    exists_sexticGaussianReflectedProfile_fifthRootCurvature_pos_right,
    sexticGaussianReflectedProfile_fifthRootCurvature_neg⟩
  · intro x hx
    exact cubicGaussianRadialProfile_eq_sexticGaussianKernel_sqrt hx
  · intro x hx
    exact firstLaguerreExpression_cubicGaussianRadialProfile_pos hx
  · intro x hx
    exact cubicGaussianRadialProfile_secondLevel_strict hx
  · intro x
    rfl
  · intro T hT
    exact sexticGaussianCorrelationAngle_concaveOn hT

end

end HilbertMetric
