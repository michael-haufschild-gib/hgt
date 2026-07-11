import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeDerivatives

/-!
# Reflection of the full theta-cusp source

The Gaussian theta tail is not itself even in logarithmic coordinates: its reflection differs by
the two elementary modes `exp(x/2)` and `exp(-x/2)`.  The Hedenmalm cusp operator
`d²/dx² - 1/4` kills exactly those modes.  This file makes that cancellation literal and proves
that the all-integer theta-cusp source is even.
-/

open Filter Topology Set Polynomial HurwitzZeta
open scoped ContDiff

noncomputable section

namespace RHTower

/-- Polynomial recursion for derivatives of the unmodified logarithmic Gaussian theta tail. -/
def thetaCuspTailDerivativePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | m + 1 => thetaCuspLogDerivativeStep (thetaCuspTailDerivativePolynomial m)

/-- The `m`-th derivative series of the positive-integer logarithmic Gaussian theta tail. -/
def thetaCuspTailDerivative (m : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial m) (n + 1) x

theorem summable_thetaCuspTailDerivative (m : ℕ) (x : ℝ) :
    Summable (fun n : ℕ =>
      thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial m) (n + 1) x) := by
  let R := |x|
  have hx : x ∈ Icc (-R) R := by
    dsimp [R]
    exact ⟨neg_abs_le x, le_abs_self x⟩
  have hM := summable_thetaCuspPolynomialMajorant
    (thetaCuspTailDerivativePolynomial m) R
  apply Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hM)
  intro n
  rw [Real.norm_eq_abs]
  exact abs_thetaCuspPolynomialAtom_le_majorant _ hx (n + 1)

theorem hasDerivAt_thetaCuspTailDerivative (m : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspTailDerivative m) (thetaCuspTailDerivative (m + 1) x) x := by
  let R : ℝ := |x| + 1
  have hx : x ∈ Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [neg_abs_le x, le_abs_self x]
  let u : ℕ → ℝ := fun n =>
    thetaCuspPolynomialMajorant (thetaCuspTailDerivativePolynomial (m + 1)) R (n + 1)
  have hu : Summable u := by
    exact (summable_nat_add_iff 1).mpr
      (summable_thetaCuspPolynomialMajorant
        (thetaCuspTailDerivativePolynomial (m + 1)) R)
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    ordConnected_Ioo.isPreconnected
    (fun n y _hy =>
      hasDerivAt_thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial m) (n + 1) y)
    (fun n y hy => by
      rw [Real.norm_eq_abs]
      exact abs_thetaCuspPolynomialAtom_le_majorant _ (Ioo_subset_Icc_self hy) (n + 1))
    hx (summable_thetaCuspTailDerivative m x) hx
  simpa [thetaCuspTailDerivative, thetaCuspTailDerivativePolynomial, u] using key

theorem differentiable_thetaCuspTailDerivative (m : ℕ) :
    Differentiable ℝ (thetaCuspTailDerivative m) :=
  fun x => (hasDerivAt_thetaCuspTailDerivative m x).differentiableAt

/-- The tail series is the standard positive theta tail in logarithmic coordinates. -/
theorem thetaCuspTailDerivative_zero_eq_evenKernel (x : ℝ) :
    thetaCuspTailDerivative 0 x =
      Real.exp (x / 2) * (evenKernel 0 (Real.exp (2 * x)) - 1) / 2 := by
  have hs := (hasSum_nat_cosKernel₀ 0 (Real.exp_pos (2 * x))).mul_left
    (Real.exp (x / 2) / 2)
  have hexp : Real.exp x ^ 2 = Real.exp (x * 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [thetaCuspTailDerivative]
  calc
    ∑' n : ℕ, thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 0) (n + 1) x =
        ∑' n : ℕ, Real.exp (x / 2) / 2 *
          (2 * Real.cos (2 * Real.pi * 0 * (n + 1)) *
            Real.exp (-Real.pi * (n + 1) ^ 2 * Real.exp (2 * x))) := by
      apply tsum_congr
      intro n
      simp [thetaCuspTailDerivativePolynomial, thetaCuspPolynomialAtom]
      rw [mul_pow, hexp]
      rw [show Real.exp (x * 2) = Real.exp (2 * x) by
        congr 1
        ring]
      ring
    _ = Real.exp (x / 2) / 2 *
        (cosKernel 0 (Real.exp (2 * x)) - 1) := hs.tsum_eq
    _ = Real.exp (x / 2) * (evenKernel 0 (Real.exp (2 * x)) - 1) / 2 := by
      rw [congrFun evenKernel_eq_cosKernel_of_zero (Real.exp (2 * x))]
      ring

/-- The theta functional equation leaves only the two elementary half-exponential modes under
reflection of the positive Gaussian tail. -/
theorem thetaCuspTailDerivative_zero_neg (x : ℝ) :
    thetaCuspTailDerivative 0 (-x) = thetaCuspTailDerivative 0 x +
      (Real.exp (x / 2) - Real.exp (-x / 2)) / 2 := by
  rw [thetaCuspTailDerivative_zero_eq_evenKernel,
    thetaCuspTailDerivative_zero_eq_evenKernel]
  have hfe := evenKernel_functional_equation (0 : UnitAddCircle) (Real.exp (-2 * x))
  have hcos : cosKernel (0 : UnitAddCircle) (Real.exp (2 * x)) =
      evenKernel (0 : UnitAddCircle) (Real.exp (2 * x)) := by
    simpa using congrFun evenKernel_eq_cosKernel_of_zero (Real.exp (2 * x)) |>.symm
  have hpow : Real.exp (-2 * x) ^ (1 / 2 : ℝ) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hinv : 1 / Real.exp (-2 * x) = Real.exp (2 * x) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hpow, hinv, hcos] at hfe
  have hinv' : 1 / Real.exp (-x) = Real.exp x := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hinv'] at hfe
  rw [show 2 * -x = -2 * x by ring, hfe]
  have hmul : Real.exp (-x / 2) * Real.exp x = Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_sub]
  rw [← mul_assoc (Real.exp (-x / 2)) (Real.exp x), hmul]
  ring

/-- The second tail polynomial minus its `1/4` ground mode is exactly the theta-cusp seed
polynomial. -/
theorem thetaCuspTailDerivativePolynomial_two_sub :
    thetaCuspTailDerivativePolynomial 2 - C (1 / 4) = thetaCuspSeedPolynomial := by
  apply Polynomial.funext
  intro y
  simp [thetaCuspTailDerivativePolynomial, thetaCuspLogDerivativeStep,
    thetaCuspSeedPolynomial]
  ring

/-- Applying `d²/dx² - 1/4` to the positive Gaussian tail gives the all-integer theta-cusp
source. -/
theorem thetaCuspFullSource_eq_tail_second_sub (x : ℝ) :
    thetaCuspFullSource x =
      thetaCuspTailDerivative 2 x - (1 / 4 : ℝ) * thetaCuspTailDerivative 0 x := by
  have hs : Summable (fun n : ℕ => thetaCuspSourceTerm x n) :=
    summable_thetaCuspSourceTerm x
  have hshift := hs.sum_add_tsum_nat_add 1
  have hzero : thetaCuspSourceTerm x 0 = 0 := by
    simp [thetaCuspSourceTerm, thetaCuspSeed]
  have htail : (∑' n : ℕ, thetaCuspSourceTerm x (n + 1)) = thetaCuspFullSource x := by
    rw [thetaCuspFullSource, ← hshift]
    simp [hzero]
  rw [← htail, thetaCuspTailDerivative, thetaCuspTailDerivative]
  symm
  rw [← tsum_mul_left]
  rw [← (summable_thetaCuspTailDerivative 2 x).tsum_sub
    ((summable_thetaCuspTailDerivative 0 x).mul_left (1 / 4 : ℝ))]
  apply tsum_congr
  intro n
  calc
    thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 2) (n + 1) x -
        (1 / 4 : ℝ) *
          thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 0) (n + 1) x =
      thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 2 - C (1 / 4)) (n + 1) x := by
          unfold thetaCuspPolynomialAtom
          simp [thetaCuspTailDerivativePolynomial]
          ring
    _ = thetaCuspPolynomialAtom thetaCuspSeedPolynomial (n + 1) x := by
      rw [thetaCuspTailDerivativePolynomial_two_sub]
    _ = thetaCuspSourceTerm x (n + 1) := by
      exact (congrFun (thetaCuspSourceTerm_eq_polynomialAtom (n + 1)) x).symm

/-- The elementary half-exponential reflection defect of the positive theta tail. -/
def thetaCuspReflectionMode (x : ℝ) : ℝ :=
  (Real.exp (x / 2) - Real.exp (-x / 2)) / 2

/-- First derivative of the elementary reflection defect. -/
def thetaCuspReflectionModeDeriv (x : ℝ) : ℝ :=
  (Real.exp (x / 2) + Real.exp (-x / 2)) / 4

theorem hasDerivAt_thetaCuspReflectionMode (x : ℝ) :
    HasDerivAt thetaCuspReflectionMode (thetaCuspReflectionModeDeriv x) x := by
  unfold thetaCuspReflectionMode thetaCuspReflectionModeDeriv
  convert (((Real.hasDerivAt_exp (x / 2)).comp x
    ((hasDerivAt_id x).div_const 2)).sub
      ((Real.hasDerivAt_exp (-x / 2)).comp x
        (((hasDerivAt_id x).neg).div_const 2))).div_const 2 using 1
  all_goals ring

theorem hasDerivAt_thetaCuspReflectionModeDeriv (x : ℝ) :
    HasDerivAt thetaCuspReflectionModeDeriv
      ((1 / 4 : ℝ) * thetaCuspReflectionMode x) x := by
  unfold thetaCuspReflectionMode thetaCuspReflectionModeDeriv
  convert (((Real.hasDerivAt_exp (x / 2)).comp x
    ((hasDerivAt_id x).div_const 2)).add
      ((Real.hasDerivAt_exp (-x / 2)).comp x
        (((hasDerivAt_id x).neg).div_const 2))).div_const 4 using 1
  all_goals ring

/-- The one-sided theta tail has the exact cusp slope which supplies the constant term of `Xi`. -/
theorem thetaCuspTailDerivative_one_zero :
    thetaCuspTailDerivative 1 0 = -(1 / 4 : ℝ) := by
  have hreflection : (fun y : ℝ => thetaCuspTailDerivative 0 (-y)) =
      fun y => thetaCuspTailDerivative 0 y + thetaCuspReflectionMode y := by
    funext y
    simpa [thetaCuspReflectionMode] using thetaCuspTailDerivative_zero_neg y
  have hl := (hasDerivAt_thetaCuspTailDerivative 0 (-(0 : ℝ))).comp (0 : ℝ)
    (hasDerivAt_neg (0 : ℝ))
  have hr := (hasDerivAt_thetaCuspTailDerivative 0 (0 : ℝ)).add
    (hasDerivAt_thetaCuspReflectionMode (0 : ℝ))
  have hl' : HasDerivAt (fun y : ℝ => thetaCuspTailDerivative 0 (-y))
      (-thetaCuspTailDerivative 1 0) 0 := by
    simpa [Function.comp_def] using hl
  have hr' : HasDerivAt
      (fun y : ℝ => thetaCuspTailDerivative 0 y + thetaCuspReflectionMode y)
      (thetaCuspTailDerivative 1 0 + 1 / 2) 0 := by
    convert hr using 1 <;> norm_num [thetaCuspReflectionModeDeriv]
  rw [hreflection] at hl'
  have h := hl'.unique hr'
  linarith

/-- **Theta-cusp reflection law.** The elementary reflection defect of the Gaussian tail is
annihilated by `d²/dx² - 1/4`, so the actual all-integer cusp source is even. -/
theorem thetaCuspFullSource_neg (x : ℝ) :
    thetaCuspFullSource (-x) = thetaCuspFullSource x := by
  have hreflection : (fun y : ℝ => thetaCuspTailDerivative 0 (-y)) =
      fun y => thetaCuspTailDerivative 0 y + thetaCuspReflectionMode y := by
    funext y
    simpa [thetaCuspReflectionMode] using thetaCuspTailDerivative_zero_neg y
  have hfirst (y : ℝ) :
      -thetaCuspTailDerivative 1 (-y) =
        thetaCuspTailDerivative 1 y + thetaCuspReflectionModeDeriv y := by
    have hl := (hasDerivAt_thetaCuspTailDerivative 0 (-y)).comp y (hasDerivAt_neg y)
    have hr := (hasDerivAt_thetaCuspTailDerivative 0 y).add
      (hasDerivAt_thetaCuspReflectionMode y)
    have hl' : HasDerivAt (fun z : ℝ => thetaCuspTailDerivative 0 (-z))
        (-thetaCuspTailDerivative 1 (-y)) y := by
      simpa [Function.comp_def] using hl
    have hr' : HasDerivAt
        (fun z : ℝ => thetaCuspTailDerivative 0 z + thetaCuspReflectionMode z)
        (thetaCuspTailDerivative 1 y + thetaCuspReflectionModeDeriv y) y := by
      simpa using hr
    rw [hreflection] at hl'
    exact hl'.unique hr'
  have hfirstFun : (fun y : ℝ => -thetaCuspTailDerivative 1 (-y)) =
      fun y => thetaCuspTailDerivative 1 y + thetaCuspReflectionModeDeriv y :=
    funext hfirst
  have hsecond : thetaCuspTailDerivative 2 (-x) =
      thetaCuspTailDerivative 2 x +
        (1 / 4 : ℝ) * thetaCuspReflectionMode x := by
    have hl := ((hasDerivAt_thetaCuspTailDerivative 1 (-x)).comp x
      (hasDerivAt_neg x)).neg
    have hr := (hasDerivAt_thetaCuspTailDerivative 1 x).add
      (hasDerivAt_thetaCuspReflectionModeDeriv x)
    have hl' : HasDerivAt (fun z : ℝ => -thetaCuspTailDerivative 1 (-z))
        (thetaCuspTailDerivative 2 (-x)) x := by
      simpa [Function.comp_def] using hl
    have hr' : HasDerivAt
        (fun z : ℝ => thetaCuspTailDerivative 1 z + thetaCuspReflectionModeDeriv z)
        (thetaCuspTailDerivative 2 x +
          (1 / 4 : ℝ) * thetaCuspReflectionMode x) x := by
      simpa using hr
    rw [hfirstFun] at hl'
    exact hl'.unique hr'
  rw [thetaCuspFullSource_eq_tail_second_sub,
    thetaCuspFullSource_eq_tail_second_sub, hsecond,
    thetaCuspTailDerivative_zero_neg]
  change thetaCuspTailDerivative 2 x +
      (1 / 4 : ℝ) * thetaCuspReflectionMode x -
        (1 / 4 : ℝ) *
          (thetaCuspTailDerivative 0 x + thetaCuspReflectionMode x) =
    thetaCuspTailDerivative 2 x - (1 / 4 : ℝ) * thetaCuspTailDerivative 0 x
  ring

/-- The all-integer theta-cusp source is smooth to every order. -/
theorem contDiff_thetaCuspFullSource : ContDiff ℝ ∞ thetaCuspFullSource := by
  rw [contDiff_infty]
  intro n
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _hm
  rw [iteratedDeriv_thetaCuspFullSource]
  exact fun x => (hasDerivAt_thetaCuspFullDerivative m x).differentiableAt

/-- Every derivative has the parity forced by evenness of the theta-cusp source. -/
theorem iteratedDeriv_thetaCuspFullSource_neg (m : ℕ) (x : ℝ) :
    iteratedDeriv m thetaCuspFullSource (-x) =
      (-1 : ℝ) ^ m * iteratedDeriv m thetaCuspFullSource x := by
  have hfun : (fun y : ℝ => thetaCuspFullSource (-y)) = thetaCuspFullSource := by
    funext y
    exact thetaCuspFullSource_neg y
  have hder := congrArg (iteratedDeriv m) hfun
  have hx := congrFun hder (-x)
  rw [iteratedDeriv_comp_neg] at hx
  simpa [smul_eq_mul] using hx.symm

theorem abs_iteratedDeriv_thetaCuspFullSource_neg (m : ℕ) (x : ℝ) :
    |iteratedDeriv m thetaCuspFullSource (-x)| =
      |iteratedDeriv m thetaCuspFullSource x| := by
  rw [iteratedDeriv_thetaCuspFullSource_neg, abs_mul, abs_pow]
  simp

end RHTower
