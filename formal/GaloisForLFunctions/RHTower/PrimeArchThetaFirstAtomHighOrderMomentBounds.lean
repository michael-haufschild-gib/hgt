import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomHighOrderQuadrature

/-!
# Exact first-atom moment bounds from high-order quadrature

The local exponential enclosures are assembled into polynomial density certificates.  Their
integrals are exact rational numbers, leaving only one uniform analytic tail estimate.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

theorem integral_Ioi_eq_intervalIntegral_add_tail_local
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ → Y} {a b : ℝ} (hab : a ≤ b) (hint : IntegrableOn f (Ioi a)) :
    (∫ t in Ioi a, f t) = (∫ t in a..b, f t) + ∫ t in Ioi b, f t := by
  have hunion : Ioi a = Ioc a b ∪ Ioi b := (Ioc_union_Ioi_eq_Ioi hab).symm
  have hdisj : Disjoint (Ioc a b) (Ioi b) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht.2 (not_le.mpr ht')
  have h1 : IntegrableOn f (Ioc a b) :=
    hint.mono_set (by rw [hunion]; exact subset_union_left)
  have h2 : IntegrableOn f (Ioi b) :=
    hint.mono_set (by rw [hunion]; exact subset_union_right)
  rw [hunion, setIntegral_union hdisj measurableSet_Ioi h1 h2,
    intervalIntegral.integral_of_le hab]

namespace ThetaRationalQuadrature

def momentMass : QPoly → ℕ → ℚ → ℚ
  | [], _, _ => 0
  | a :: p, k, h =>
      a * h ^ (k + 1) / (k + 1 : ℚ) + momentMass p (k + 1) h

def integralMass (p : QPoly) (h : ℚ) : ℚ := momentMass p 0 h

def upperDelta (j : ℕ) : QPoly :=
  sub (mul (C ((3.14159265358979323847 : ℚ) * thirtySecondExpUpper ^ j))
      (sub expTwoTaylorUpper (C 1)))
    (mul (C (5 / 2)) X)

def lowerDelta (j : ℕ) : QPoly :=
  sub (mul (C ((3.14159265358979323846 : ℚ) * thirtySecondExpLower ^ j))
      (sub expTwoTaylor (C 1)))
    (mul (C (5 / 2)) X)

def localLower (j : ℕ) : QPoly := comp (expNeg 6) (upperDelta j)
def localUpper (j : ℕ) : QPoly := comp (expNeg 5) (lowerDelta j)

def sourceLower (j : ℕ) : QPoly :=
  sub (mul (C ((6.28318530717958647692 : ℚ) * thirtySecondExpLower ^ j))
    expTwoTaylor) (C 3)

def sourceUpper (j : ℕ) : QPoly :=
  sub (mul (C ((6.28318530717958647694 : ℚ) * thirtySecondExpUpper ^ j))
    expTwoTaylorUpper) (C 3)

def lowerPolynomial (r j : ℕ) : QPoly :=
  mul (mul (mul (C (12.5663706143591729538 : ℚ))
    (pow (add (C ((j : ℚ) / 64)) X) (2 * r))) (sourceLower j))
    (mul (C ((0.0432139182637 : ℚ) * endpointLower j)) (localLower j))

def upperPolynomial (r j : ℕ) : QPoly :=
  mul (mul (mul (C (12.5663706143591729539 : ℚ))
    (pow (add (C ((j : ℚ) / 64)) X) (2 * r))) (sourceUpper j))
    (mul (C ((0.0432139182638 : ℚ) * endpointUpper j)) (localUpper j))

def lowerMass (r j : ℕ) : ℚ := integralMass (lowerPolynomial r j) (1 / 64)
def upperMass (r j : ℕ) : ℚ := integralMass (upperPolynomial r j) (1 / 64)

noncomputable def realPolynomial : QPoly → ℝ[X]
  | [] => 0
  | a :: p => Polynomial.C (a : ℝ) + Polynomial.X * realPolynomial p

@[simp] theorem realPolynomial_nil : realPolynomial [] = 0 := rfl

@[simp] theorem realPolynomial_cons (a : ℚ) (p : QPoly) :
    realPolynomial (a :: p) =
      Polynomial.C (a : ℝ) + Polynomial.X * realPolynomial p := rfl

theorem realPolynomial_add (p q : QPoly) :
    realPolynomial (add p q) = realPolynomial p + realPolynomial q := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
      cases q with
      | nil => simp [add]
      | cons b q =>
          rw [add, realPolynomial_cons, realPolynomial_cons,
            realPolynomial_cons, ih]
          push_cast
          simp only [map_add]
          ring

theorem realPolynomial_scale (a : ℚ) (p : QPoly) :
    realPolynomial (scale a p) = Polynomial.C (a : ℝ) * realPolynomial p := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
      change realPolynomial ((a * b) :: scale a p) =
        Polynomial.C (a : ℝ) * realPolynomial (b :: p)
      rw [realPolynomial_cons, realPolynomial_cons, ih]
      push_cast
      simp only [map_mul]
      ring

theorem realPolynomial_neg (p : QPoly) : realPolynomial (neg p) = -realPolynomial p := by
  induction p with
  | nil => simp [neg]
  | cons a p ih =>
      change realPolynomial ((-a) :: neg p) = -realPolynomial (a :: p)
      rw [realPolynomial_cons, realPolynomial_cons, ih]
      push_cast
      simp only [map_neg]
      ring

theorem realPolynomial_sub (p q : QPoly) :
    realPolynomial (sub p q) = realPolynomial p - realPolynomial q := by
  rw [sub, realPolynomial_add, realPolynomial_neg]
  ring

@[simp] theorem realPolynomial_C (a : ℚ) : realPolynomial (C a) = Polynomial.C (a : ℝ) := by
  simp [C, realPolynomial]

@[simp] theorem realPolynomial_X : realPolynomial X = Polynomial.X := by
  simp [X, realPolynomial]

theorem realPolynomial_mul (p q : QPoly) :
    realPolynomial (mul p q) = realPolynomial p * realPolynomial q := by
  induction p generalizing q with
  | nil => simp [mul]
  | cons a p ih =>
      cases q with
      | nil => simp [mul]
      | cons b q =>
          change realPolynomial
              (add (scale a (b :: q)) (0 :: mul p (b :: q))) =
            realPolynomial (a :: p) * realPolynomial (b :: q)
          rw [realPolynomial_add, realPolynomial_scale]
          simp only [realPolynomial_cons]
          rw [ih]
          simp [realPolynomial]
          ring

theorem realPolynomial_pow (p : QPoly) (n : ℕ) :
    realPolynomial (pow p n) = realPolynomial p ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => rw [pow, realPolynomial_mul, ih, pow_succ]

theorem realPolynomial_comp (p q : QPoly) :
    realPolynomial (comp p q) = (realPolynomial p).comp (realPolynomial q) := by
  induction p with
  | nil => simp [comp]
  | cons a p ih =>
      change realPolynomial (add [a] (mul q (comp p q))) =
        (realPolynomial (a :: p)).comp (realPolynomial q)
      rw [realPolynomial_add, realPolynomial_mul,
        realPolynomial_cons, realPolynomial_cons, ih]
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_C, eval_mul, eval_X, eval_comp]
      simp [realPolynomial]

theorem realPolynomial_expTwoTaylor :
    realPolynomial expTwoTaylor = thetaCuspExpTwoTaylorEightPolynomial := by
  norm_num [expTwoTaylor, realPolynomial, thetaCuspExpTwoTaylorEightPolynomial]
  ring

theorem realPolynomial_expTwoTaylorUpper :
    realPolynomial expTwoTaylorUpper = thetaCuspExpTwoTaylorEightUpperPolynomial := by
  rw [expTwoTaylorUpper, realPolynomial_add, realPolynomial_mul,
    realPolynomial_C, realPolynomial_pow, realPolynomial_X,
    realPolynomial_expTwoTaylor]
  norm_num [thetaCuspExpTwoTaylorEightUpperPolynomial]

theorem realPolynomial_expNeg_six : realPolynomial (expNeg 6) = expNegTruncPoly 6 := by
  norm_num [expNeg, realPolynomial, expNegTruncPoly, Finset.sum_range_succ]
  ring

theorem realPolynomial_expNeg_five : realPolynomial (expNeg 5) = expNegTruncPoly 5 := by
  norm_num [expNeg, realPolynomial, expNegTruncPoly, Finset.sum_range_succ]
  ring

theorem realPolynomial_upperDelta (j : ℕ) :
    realPolynomial (upperDelta j) = thetaCuspFirstRateTaylorUpperDelta64 j := by
  rw [upperDelta, realPolynomial_sub, realPolynomial_mul,
    realPolynomial_C, realPolynomial_sub, realPolynomial_expTwoTaylorUpper,
    realPolynomial_C, realPolynomial_mul, realPolynomial_C,
    realPolynomial_X, thetaCuspFirstRateTaylorUpperDelta64,
    ← thetaRationalQuadrature_thirtySecondExpUpper_cast]
  push_cast
  simp

theorem realPolynomial_lowerDelta (j : ℕ) :
    realPolynomial (lowerDelta j) = thetaCuspFirstRateTaylorLowerDelta64 j := by
  rw [lowerDelta, realPolynomial_sub, realPolynomial_mul,
    realPolynomial_C, realPolynomial_sub, realPolynomial_expTwoTaylor,
    realPolynomial_C, realPolynomial_mul, realPolynomial_C,
    realPolynomial_X, thetaCuspFirstRateTaylorLowerDelta64,
    ← thetaRationalQuadrature_thirtySecondExpLower_cast]
  push_cast
  simp

theorem realPolynomial_localLower (j : ℕ) :
    realPolynomial (localLower j) = thetaCuspFirstRateTaylorLocalLowerCertificate64 j := by
  rw [localLower, realPolynomial_comp, realPolynomial_expNeg_six,
    realPolynomial_upperDelta, thetaCuspFirstRateTaylorLocalLowerCertificate64]

theorem realPolynomial_localUpper (j : ℕ) :
    realPolynomial (localUpper j) = thetaCuspFirstRateTaylorLocalUpperCertificate64 j := by
  rw [localUpper, realPolynomial_comp, realPolynomial_expNeg_five,
    realPolynomial_lowerDelta, thetaCuspFirstRateTaylorLocalUpperCertificate64]

theorem realPolynomial_sourceLower (j : ℕ) :
    realPolynomial (sourceLower j) = thetaCuspFirstSourceTaylorLower64 j := by
  rw [sourceLower, realPolynomial_sub, realPolynomial_mul,
    realPolynomial_C, realPolynomial_expTwoTaylor, realPolynomial_C,
    thetaCuspFirstSourceTaylorLower64,
    ← thetaRationalQuadrature_thirtySecondExpLower_cast]
  push_cast
  rfl

theorem realPolynomial_sourceUpper (j : ℕ) :
    realPolynomial (sourceUpper j) = thetaCuspFirstSourceTaylorUpper64 j := by
  rw [sourceUpper, realPolynomial_sub, realPolynomial_mul,
    realPolynomial_C, realPolynomial_expTwoTaylorUpper, realPolynomial_C,
    thetaCuspFirstSourceTaylorUpper64,
    ← thetaRationalQuadrature_thirtySecondExpUpper_cast]
  push_cast
  rfl

end ThetaRationalQuadrature

def thetaCuspFirstAtomHighOrderLowerPolynomial64 (r j : ℕ) : ℝ[X] :=
  C (12.5663706143591729538 : ℝ) *
    (C ((j : ℝ) / 64) + X) ^ (2 * r) *
    thetaCuspFirstSourceTaylorLower64 j *
    (C ((0.0432139182637 : ℝ) *
      thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j) *
      thetaCuspFirstRateTaylorLocalLowerCertificate64 j)

def thetaCuspFirstAtomHighOrderUpperPolynomial64 (r j : ℕ) : ℝ[X] :=
  C (12.5663706143591729539 : ℝ) *
    (C ((j : ℝ) / 64) + X) ^ (2 * r) *
    thetaCuspFirstSourceTaylorUpper64 j *
    (C ((0.0432139182638 : ℝ) *
      thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j) *
      thetaCuspFirstRateTaylorLocalUpperCertificate64 j)

namespace ThetaRationalQuadrature

theorem realPolynomial_lowerPolynomial (r j : ℕ) :
    realPolynomial (lowerPolynomial r j) =
      thetaCuspFirstAtomHighOrderLowerPolynomial64 r j := by
  rw [lowerPolynomial, realPolynomial_mul, realPolynomial_mul,
    realPolynomial_mul, realPolynomial_C, realPolynomial_pow,
    realPolynomial_add, realPolynomial_C, realPolynomial_X,
    realPolynomial_sourceLower, realPolynomial_mul,
    realPolynomial_C, realPolynomial_localLower,
    thetaCuspFirstAtomHighOrderLowerPolynomial64,
    thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64]
  push_cast
  rfl

theorem realPolynomial_upperPolynomial (r j : ℕ) :
    realPolynomial (upperPolynomial r j) =
      thetaCuspFirstAtomHighOrderUpperPolynomial64 r j := by
  rw [upperPolynomial, realPolynomial_mul, realPolynomial_mul,
    realPolynomial_mul, realPolynomial_C, realPolynomial_pow,
    realPolynomial_add, realPolynomial_C, realPolynomial_X,
    realPolynomial_sourceUpper, realPolynomial_mul,
    realPolynomial_C, realPolynomial_localUpper,
    thetaCuspFirstAtomHighOrderUpperPolynomial64,
    thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64]
  push_cast
  rfl

theorem intervalIntegral_pow_mul_realPolynomial_eval_eq_momentMass
    (p : QPoly) (k : ℕ) (h : ℚ) :
    (∫ x : ℝ in 0..(h : ℝ), x ^ k * (realPolynomial p).eval x) =
      (momentMass p k h : ℚ) := by
  induction p generalizing k with
  | nil => simp [realPolynomial, momentMass]
  | cons a p ih =>
      rw [realPolynomial_cons]
      simp only [eval_add, eval_C, eval_mul, eval_X]
      rw [show (fun x : ℝ => x ^ k * (↑a + x * (realPolynomial p).eval x)) =
          fun x : ℝ => ↑a * x ^ k + x ^ (k + 1) * (realPolynomial p).eval x by
        funext x
        rw [pow_succ]
        ring]
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const_mul, integral_pow, ih]
        rw [momentMass]
        push_cast
        ring
      · exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
      · exact ((continuous_id.pow _).mul (Polynomial.continuous _)).intervalIntegrable _ _

theorem intervalIntegral_realPolynomial_eval_eq_integralMass (p : QPoly) (h : ℚ) :
    (∫ x : ℝ in 0..(h : ℝ), (realPolynomial p).eval x) =
      (integralMass p h : ℚ) := by
  simpa [integralMass] using
    intervalIntegral_pow_mul_realPolynomial_eval_eq_momentMass p 0 h

end ThetaRationalQuadrature

theorem thetaCuspFirstAtomHighOrderLowerPolynomial64_eval_le_density
    {r j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    (thetaCuspFirstAtomHighOrderLowerPolynomial64 r j).eval y ≤
      2 * (((j : ℝ) / 64 + y) ^ (2 * r) *
        thetaCuspSourceTerm ((j : ℝ) / 64 + y) 1) := by
  let x : ℝ := (j : ℝ) / 64 + y
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hs := thetaCuspFirstSourceTaylorLower64_eval_le_actual j hy
  have hs0 := thetaCuspFirstSourceTaylorLower64_eval_nonneg j hy
  have hg := thetaCuspFirstGibbsTaylorLower64_le hj hy hyh
  have hg0 : 0 ≤
      (0.0432139182637 : ℝ) *
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
        (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64_pos hj).le)
      (thetaCuspFirstRateTaylorLocalLowerCertificate64_eval_pos hj hy hyh).le
  have hactualG0 : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [thetaCuspLiouvilleGibbsAtom_apply]
    positivity
  have hactualS0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := hs0.trans hs
  have houter : (12.5663706143591729538 : ℝ) ≤ 4 * Real.pi := by
    nlinarith [Real.pi_gt_d20]
  rw [thetaCuspFirstAtomHighOrderLowerPolynomial64]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]
  change (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
      (thetaCuspFirstSourceTaylorLower64 j).eval y *
      ((0.0432139182637 : ℝ) *
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
        (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y) ≤
    2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
  rw [thetaCuspSourceTerm_one_eq_liouvilleGibbs]
  calc
    (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
          (thetaCuspFirstSourceTaylorLower64 j).eval y *
          ((0.0432139182637 : ℝ) *
            thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
            (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y) ≤
        (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
          (thetaCuspFirstSourceTaylorLower64 j).eval y *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_left hg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 _)) hs0)
    _ ≤ (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs
          (mul_nonneg (by norm_num) (pow_nonneg hx0 _))) hactualG0
    _ ≤ (4 * Real.pi) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right houter (pow_nonneg hx0 _)) hactualS0)
        hactualG0
    _ = 2 * (x ^ (2 * r) *
          (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x)) := by ring

theorem thetaCuspFirstAtom_density_le_highOrderUpperPolynomial64_eval
    {r j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    2 * (((j : ℝ) / 64 + y) ^ (2 * r) *
        thetaCuspSourceTerm ((j : ℝ) / 64 + y) 1) ≤
      (thetaCuspFirstAtomHighOrderUpperPolynomial64 r j).eval y := by
  let x : ℝ := (j : ℝ) / 64 + y
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hs := actual_le_thetaCuspFirstSourceTaylorUpper64_eval j hy hyh
  have hactualS0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := by
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by positivity)
    nlinarith [Real.pi_gt_d4]
  have hs0 : 0 ≤ (thetaCuspFirstSourceTaylorUpper64 j).eval y :=
    hactualS0.trans hs
  have hg := thetaCuspFirstGibbs_le_taylorUpper64 hj hy hyh
  have hactualG0 : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [thetaCuspLiouvilleGibbsAtom_apply]
    positivity
  have hcertG0 : 0 ≤
      (0.0432139182638 : ℝ) *
        thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
        (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y :=
    hactualG0.trans hg
  have houter : 4 * Real.pi ≤ (12.5663706143591729539 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  rw [thetaCuspFirstAtomHighOrderUpperPolynomial64]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]
  change 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) ≤
    (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
      (thetaCuspFirstSourceTaylorUpper64 j).eval y *
      ((0.0432139182638 : ℝ) *
        thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
        (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y)
  rw [thetaCuspSourceTerm_one_eq_liouvilleGibbs]
  calc
    2 * (x ^ (2 * r) *
          (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x)) =
        (4 * Real.pi) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by ring
    _ ≤ (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right houter (pow_nonneg hx0 _)) hactualS0)
        hactualG0
    _ ≤ (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
          (thetaCuspFirstSourceTaylorUpper64 j).eval y *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs
          (mul_nonneg (by norm_num) (pow_nonneg hx0 _))) hactualG0
    _ ≤ (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
          (thetaCuspFirstSourceTaylorUpper64 j).eval y *
          ((0.0432139182638 : ℝ) *
            thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
            (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y) := by
      exact mul_le_mul_of_nonneg_left hg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 _)) hs0)

def thetaCuspFirstAtomHighOrderLowerIntervalMass64 (r j : ℕ) : ℝ :=
  (ThetaRationalQuadrature.lowerMass r j : ℚ)

def thetaCuspFirstAtomHighOrderUpperIntervalMass64 (r j : ℕ) : ℝ :=
  (ThetaRationalQuadrature.upperMass r j : ℚ)

theorem intervalIntegral_thetaCuspFirstAtomHighOrderLowerPolynomial64_eq_mass
    (r j : ℕ) :
    (∫ y in (0 : ℝ)..1 / 64,
      (thetaCuspFirstAtomHighOrderLowerPolynomial64 r j).eval y) =
      thetaCuspFirstAtomHighOrderLowerIntervalMass64 r j := by
  rw [← ThetaRationalQuadrature.realPolynomial_lowerPolynomial]
  convert ThetaRationalQuadrature.intervalIntegral_realPolynomial_eval_eq_integralMass
    (ThetaRationalQuadrature.lowerPolynomial r j) (1 / 64) using 1 <;>
    norm_num [thetaCuspFirstAtomHighOrderLowerIntervalMass64,
      ThetaRationalQuadrature.lowerMass]

theorem intervalIntegral_thetaCuspFirstAtomHighOrderUpperPolynomial64_eq_mass
    (r j : ℕ) :
    (∫ y in (0 : ℝ)..1 / 64,
      (thetaCuspFirstAtomHighOrderUpperPolynomial64 r j).eval y) =
      thetaCuspFirstAtomHighOrderUpperIntervalMass64 r j := by
  rw [← ThetaRationalQuadrature.realPolynomial_upperPolynomial]
  convert ThetaRationalQuadrature.intervalIntegral_realPolynomial_eval_eq_integralMass
    (ThetaRationalQuadrature.upperPolynomial r j) (1 / 64) using 1 <;>
    norm_num [thetaCuspFirstAtomHighOrderUpperIntervalMass64,
      ThetaRationalQuadrature.upperMass]

theorem sum_firstAtomHighOrderLowerMass64_le_thetaCuspAtomRawEvenMoment
    (r : ℕ) :
    (∑ j ∈ Finset.range 64,
        thetaCuspFirstAtomHighOrderLowerIntervalMass64 r j) ≤
      thetaCuspAtomRawEvenMoment r 1 := by
  let f : ℝ → ℝ := fun x => 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
  have hfcont : Continuous f := by
    dsimp only [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_pow_mul_thetaCuspSourceTerm r 1).const_mul 2
    apply h.congr
    filter_upwards [] with x
    dsimp only [f]
  have hfnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (by norm_num) <|
      mul_nonneg (pow_nonneg hx.le _) (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  have hsegment (j : ℕ) (hj : j < 64) :
      thetaCuspFirstAtomHighOrderLowerIntervalMass64 r j ≤
        ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
    rw [← intervalIntegral_thetaCuspFirstAtomHighOrderLowerPolynomial64_eq_mass]
    calc
      (∫ y in (0 : ℝ)..1 / 64,
          (thetaCuspFirstAtomHighOrderLowerPolynomial64 r j).eval y) ≤
          ∫ y in (0 : ℝ)..1 / 64, f (y + (j : ℝ) / 64) := by
        apply intervalIntegral.integral_mono_on
        · norm_num
        · exact (Polynomial.continuous _).intervalIntegrable _ _
        · exact (hfcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
        · intro y hy
          simpa only [f, add_comm] using
            thetaCuspFirstAtomHighOrderLowerPolynomial64_eval_le_density
              hj hy.1 hy.2
      _ = ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
        rw [intervalIntegral.integral_comp_add_right]
        congr 2 <;> push_cast <;> ring
  have hsum :
      (∑ j ∈ Finset.range 64,
          thetaCuspFirstAtomHighOrderLowerIntervalMass64 r j) ≤
        ∑ j ∈ Finset.range 64,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
    exact Finset.sum_le_sum fun j hj => hsegment j (Finset.mem_range.mp hj)
  have hjoin :
      (∑ j ∈ Finset.range 64,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    convert
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := f) (a := fun k : ℕ => (k : ℝ) / 64) (n := 64) (μ := volume)
        (fun k _ => hfcont.intervalIntegrable _ _)) using 1 <;> norm_num
  have hwindow : (∫ x in (0 : ℝ)..1, f x) ≤ ∫ x in Ioi 0, f x := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_mono_set hfint hfnonneg
      (Filter.Eventually.of_forall fun x hx => hx.1)
  have hraw : (∫ x in Ioi 0, f x) = thetaCuspAtomRawEvenMoment r 1 := by
    rw [thetaCuspAtomRawEvenMoment]
    dsimp only [f]
    rw [← integral_const_mul]
  exact hsum.trans (hjoin.le.trans (hwindow.trans hraw.le))

theorem thetaCuspAtomRawEvenMoment_le_sum_firstAtomHighOrderUpperMass64_add_tail
    (r : ℕ) :
    thetaCuspAtomRawEvenMoment r 1 ≤
      (∑ j ∈ Finset.range 64,
        thetaCuspFirstAtomHighOrderUpperIntervalMass64 r j) +
      ∫ x in Ioi (1 : ℝ), 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) := by
  let f : ℝ → ℝ := fun x => 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
  have hfcont : Continuous f := by
    dsimp only [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_pow_mul_thetaCuspSourceTerm r 1).const_mul 2
    apply h.congr
    filter_upwards [] with x
    dsimp only [f]
  have hsegment (j : ℕ) (hj : j < 64) :
      (∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) ≤
        thetaCuspFirstAtomHighOrderUpperIntervalMass64 r j := by
    rw [← intervalIntegral_thetaCuspFirstAtomHighOrderUpperPolynomial64_eq_mass]
    calc
      (∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) =
          ∫ y in (0 : ℝ)..1 / 64, f (y + (j : ℝ) / 64) := by
        rw [intervalIntegral.integral_comp_add_right]
        congr 2 <;> push_cast <;> ring
      _ ≤ ∫ y in (0 : ℝ)..1 / 64,
          (thetaCuspFirstAtomHighOrderUpperPolynomial64 r j).eval y := by
        apply intervalIntegral.integral_mono_on
        · norm_num
        · exact (hfcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
        · exact (Polynomial.continuous _).intervalIntegrable _ _
        · intro y hy
          simpa only [f, add_comm] using
            thetaCuspFirstAtom_density_le_highOrderUpperPolynomial64_eval
              hj hy.1 hy.2
  have hsum :
      (∑ j ∈ Finset.range 64,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) ≤
        ∑ j ∈ Finset.range 64,
          thetaCuspFirstAtomHighOrderUpperIntervalMass64 r j := by
    exact Finset.sum_le_sum fun j hj => hsegment j (Finset.mem_range.mp hj)
  have hjoin :
      (∑ j ∈ Finset.range 64,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    convert
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := f) (a := fun k : ℕ => (k : ℝ) / 64) (n := 64) (μ := volume)
        (fun k _ => hfcont.intervalIntegrable _ _)) using 1 <;> norm_num
  have hsplit : (∫ x in Ioi (0 : ℝ), f x) =
      (∫ x in (0 : ℝ)..1, f x) + ∫ x in Ioi (1 : ℝ), f x :=
    integral_Ioi_eq_intervalIntegral_add_tail_local (by norm_num) hfint
  have hraw : (∫ x in Ioi 0, f x) = thetaCuspAtomRawEvenMoment r 1 := by
    rw [thetaCuspAtomRawEvenMoment]
    dsimp only [f]
    rw [← integral_const_mul]
  rw [← hraw, hsplit]
  simpa only [f] using add_le_add (hjoin ▸ hsum)
    (le_refl (∫ x in Ioi (1 : ℝ), f x))

theorem twentyThree_lt_pi_mul_exp_two :
    (23 : ℝ) < Real.pi * Real.exp 2 := by
  have he : (331 / 45 : ℝ) ≤ Real.exp 2 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 7
    norm_num [Finset.sum_range_succ] at h ⊢
    exact h
  have hpi := Real.pi_gt_d20
  have h1 : (3.14159265358979323846 : ℝ) * (331 / 45) <
      Real.pi * (331 / 45) := by gcongr
  have h2 : Real.pi * (331 / 45) ≤ Real.pi * Real.exp 2 := by gcongr
  have h23 : (23 : ℝ) < (3.14159265358979323846 : ℝ) * (331 / 45) := by
    norm_num
  exact h23.trans (h1.trans_le h2)

theorem thetaCuspFirstAtom_tail_density_le_exp_majorant
    {r : ℕ} (hr : r ≤ 3) {x : ℝ} (hx : 1 ≤ x) :
    2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) ≤
      79 * Real.exp (-37 / 2) * Real.exp (-(71 / 2) * (x - 1)) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hxshift : 0 ≤ x - 1 := sub_nonneg.mpr hx
  have hxexp : x ≤ Real.exp (x - 1) := by
    nlinarith [Real.add_one_le_exp (x - 1)]
  have hrNat : 2 * r ≤ 6 := by omega
  have hrReal : ((2 * r : ℕ) : ℝ) ≤ 6 := by exact_mod_cast hrNat
  have hxpow : x ^ (2 * r) ≤ Real.exp (6 * (x - 1)) := by
    calc
      x ^ (2 * r) ≤ Real.exp (x - 1) ^ (2 * r) :=
        pow_le_pow_left₀ hx0 hxexp _
      _ = Real.exp (((2 * r : ℕ) : ℝ) * (x - 1)) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (6 * (x - 1)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hrReal hxshift
  have hdouble : 46 * x - 23 ≤ Real.pi * Real.exp (2 * x) := by
    have hconvex : 1 + 2 * (x - 1) ≤ Real.exp (2 * (x - 1)) :=
      by simpa [add_comm] using Real.add_one_le_exp (2 * (x - 1))
    calc
      46 * x - 23 = 23 * (1 + 2 * (x - 1)) := by ring
      _ ≤ (Real.pi * Real.exp 2) * Real.exp (2 * (x - 1)) := by
        exact mul_le_mul twentyThree_lt_pi_mul_exp_two.le hconvex
          (by nlinarith) (by positivity)
      _ = Real.pi * Real.exp (2 * x) := by
        rw [show Real.pi * Real.exp 2 * Real.exp (2 * (x - 1)) =
          Real.pi * (Real.exp 2 * Real.exp (2 * (x - 1))) by ring,
          ← Real.exp_add]
        congr 1
        ring
  have hpiCoeff : 8 * Real.pi ^ 2 ≤ (79 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d20]
  have hsource := HedenmalmThetaSource.thetaCuspSourceTerm_one_le x
  have henv0 := (HedenmalmThetaSource.thetaEnvelope_pos x).le
  calc
    2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) ≤
        2 * (x ^ (2 * r) *
          (4 * Real.pi ^ 2 * HedenmalmThetaSource.thetaEnvelope x)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsource (pow_nonneg hx0 _)) (by norm_num)
    _ = 8 * Real.pi ^ 2 * (x ^ (2 * r) *
          HedenmalmThetaSource.thetaEnvelope x) := by ring
    _ ≤ 79 * (x ^ (2 * r) * HedenmalmThetaSource.thetaEnvelope x) := by
      exact mul_le_mul_of_nonneg_right hpiCoeff
        (mul_nonneg (pow_nonneg hx0 _) henv0)
    _ ≤ 79 * (Real.exp (6 * (x - 1)) *
          HedenmalmThetaSource.thetaEnvelope x) := by
      gcongr
    _ = 79 * Real.exp
          (6 * (x - 1) + 9 * x / 2 - Real.pi * Real.exp (2 * x)) := by
      rw [HedenmalmThetaSource.thetaEnvelope, ← Real.exp_add, ← Real.exp_add]
      ring
    _ ≤ 79 * Real.exp (-37 / 2 - (71 / 2) * (x - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (by nlinarith [hdouble])
    _ = 79 * Real.exp (-37 / 2) * Real.exp (-(71 / 2) * (x - 1)) := by
      rw [show -37 / 2 - (71 / 2) * (x - 1) =
        -37 / 2 + (-(71 / 2) * (x - 1)) by ring, Real.exp_add]
      ring

theorem ninetyMillion_lt_exp_thirtySeven_div_two :
    (90000000 : ℝ) < Real.exp (37 / 2) := by
  have heOne : (685 / 252 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 8
    norm_num [Finset.sum_range_succ] at h ⊢
    exact h
  have heHalf : (79 / 48 : ℝ) ≤ Real.exp (1 / 2) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 4
    norm_num [Finset.sum_range_succ] at h ⊢
    exact h
  have hePow : (685 / 252 : ℝ) ^ 18 ≤ Real.exp 1 ^ 18 :=
    pow_le_pow_left₀ (by norm_num) heOne 18
  have hprod : (685 / 252 : ℝ) ^ 18 * (79 / 48) ≤
      Real.exp 1 ^ 18 * Real.exp (1 / 2) := by
    exact mul_le_mul hePow heHalf (by positivity) (by positivity)
  have hrat : (90000000 : ℝ) < (685 / 252 : ℝ) ^ 18 * (79 / 48) := by
    norm_num
  calc
    (90000000 : ℝ) < (685 / 252 : ℝ) ^ 18 * (79 / 48) := hrat
    _ ≤ Real.exp 1 ^ 18 * Real.exp (1 / 2) := hprod
    _ = Real.exp (37 / 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num

theorem exp_neg_thirtySeven_div_two_lt_one_div_ninetyMillion :
    Real.exp (-37 / 2) < (1 / 90000000 : ℝ) := by
  rw [show (-37 / 2 : ℝ) = -(37 / 2) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num)
    ninetyMillion_lt_exp_thirtySeven_div_two

theorem thetaCuspFirstAtom_tail_evenMoment_lt_one_div_fortyMillion
    {r : ℕ} (hr : r ≤ 3) :
    (∫ x in Ioi (1 : ℝ),
      2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)) <
      (1 / 40000000 : ℝ) := by
  let f : ℝ → ℝ := fun x => 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
  let g : ℝ → ℝ := fun x =>
    79 * Real.exp (-37 / 2) * Real.exp (-(71 / 2) * (x - 1))
  have hfint : IntegrableOn f (Ioi (1 : ℝ)) := by
    have hzero : IntegrableOn f (Ioi (0 : ℝ)) := by
      have h := (integrableOn_pow_mul_thetaCuspSourceTerm r 1).const_mul 2
      apply h.congr
      filter_upwards [] with x
      dsimp only [f]
    exact hzero.mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro x hx
      change (1 : ℝ) < x at hx
      exact zero_lt_one.trans hx)
  have hgint : IntegrableOn g (Ioi (1 : ℝ)) := by
    exact (HedenmalmThetaSource.integrableOn_exp_neg_shift
      (x := (1 : ℝ)) (a := (71 / 2 : ℝ)) (by norm_num)).const_mul
        (79 * Real.exp (-37 / 2))
  have hmono : (∫ x in Ioi (1 : ℝ), f x) ≤ ∫ x in Ioi (1 : ℝ), g x := by
    apply MeasureTheory.integral_mono_ae hfint hgint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact thetaCuspFirstAtom_tail_density_le_exp_majorant hr hx.le
  have hgeval : (∫ x in Ioi (1 : ℝ), g x) =
      (158 / 71 : ℝ) * Real.exp (-37 / 2) := by
    rw [show g = fun x : ℝ =>
        (79 * Real.exp (-37 / 2)) *
          Real.exp (-(71 / 2) * (x - 1)) by rfl,
      integral_const_mul,
      HedenmalmThetaSource.integral_Ioi_exp_neg_shift (by norm_num)]
    ring
  have hnumeric : (158 / 71 : ℝ) * Real.exp (-37 / 2) <
      (1 / 40000000 : ℝ) := by
    calc
      (158 / 71 : ℝ) * Real.exp (-37 / 2) <
          (158 / 71 : ℝ) * (1 / 90000000) :=
        mul_lt_mul_of_pos_left
          exp_neg_thirtySeven_div_two_lt_one_div_ninetyMillion (by norm_num)
      _ < (1 / 40000000 : ℝ) := by norm_num
  exact hmono.trans_lt (hgeval ▸ hnumeric)

theorem thetaRationalQuadrature_firstAtom_bounds :
    ((0.4969488 : ℚ) <
        ∑ j ∈ Finset.range 64, ThetaRationalQuadrature.lowerMass 0 j) ∧
    ((0.02297 : ℚ) <
        ∑ j ∈ Finset.range 64, ThetaRationalQuadrature.lowerMass 1 j) ∧
    ((0.0029627 : ℚ) <
        ∑ j ∈ Finset.range 64, ThetaRationalQuadrature.lowerMass 2 j) ∧
    ((∑ j ∈ Finset.range 64, ThetaRationalQuadrature.upperMass 1 j) +
        1 / 40000000 < (0.0229718 : ℚ)) ∧
    ((∑ j ∈ Finset.range 64, ThetaRationalQuadrature.upperMass 3 j) +
        1 / 40000000 < (0.00059935 : ℚ)) := by
  native_decide

/-- Generated rational quadrature discharges all five first-atom premises of the order-24
sixth-trace reduction.  No tabulated numerical value is assumed: every mass is computed from the
Taylor recurrences above and checked by the kernel. -/
theorem thetaCuspFirstAtom_highOrder_five_bounds :
    (0.4969488 : ℝ) < thetaCuspAtomRawEvenMoment 0 1 ∧
    (0.02297 : ℝ) < thetaCuspAtomRawEvenMoment 1 1 ∧
    thetaCuspAtomRawEvenMoment 1 1 < (0.0229718 : ℝ) ∧
    (0.0029627 : ℝ) < thetaCuspAtomRawEvenMoment 2 1 ∧
    thetaCuspAtomRawEvenMoment 3 1 < (0.00059935 : ℝ) := by
  have hq := thetaRationalQuadrature_firstAtom_bounds
  have h0q := hq.1
  have h1q := hq.2.1
  have h2q := hq.2.2.1
  have h1uq := hq.2.2.2.1
  have h3uq := hq.2.2.2.2
  have h0r : (0.4969488 : ℝ) <
      ∑ j ∈ Finset.range 64,
        thetaCuspFirstAtomHighOrderLowerIntervalMass64 0 j := by
    have hcast : (0.4969488 : ℝ) <
        ((∑ j ∈ Finset.range 64,
          ThetaRationalQuadrature.lowerMass 0 j : ℚ) : ℝ) := by
      simpa using (Rat.cast_lt (K := ℝ)).2 h0q
    simpa [thetaCuspFirstAtomHighOrderLowerIntervalMass64] using hcast
  have h1r : (0.02297 : ℝ) <
      ∑ j ∈ Finset.range 64,
        thetaCuspFirstAtomHighOrderLowerIntervalMass64 1 j := by
    have hcast : (0.02297 : ℝ) <
        ((∑ j ∈ Finset.range 64,
          ThetaRationalQuadrature.lowerMass 1 j : ℚ) : ℝ) := by
      simpa using (Rat.cast_lt (K := ℝ)).2 h1q
    simpa [thetaCuspFirstAtomHighOrderLowerIntervalMass64] using hcast
  have h2r : (0.0029627 : ℝ) <
      ∑ j ∈ Finset.range 64,
        thetaCuspFirstAtomHighOrderLowerIntervalMass64 2 j := by
    have hcast : (0.0029627 : ℝ) <
        ((∑ j ∈ Finset.range 64,
          ThetaRationalQuadrature.lowerMass 2 j : ℚ) : ℝ) := by
      simpa using (Rat.cast_lt (K := ℝ)).2 h2q
    simpa [thetaCuspFirstAtomHighOrderLowerIntervalMass64] using hcast
  have h1ur :
      (∑ j ∈ Finset.range 64,
          thetaCuspFirstAtomHighOrderUpperIntervalMass64 1 j) +
        1 / 40000000 < (0.0229718 : ℝ) := by
    have hcast :
        (((∑ j ∈ Finset.range 64,
          ThetaRationalQuadrature.upperMass 1 j : ℚ) : ℚ) : ℝ) +
            1 / 40000000 < (0.0229718 : ℝ) := by
      simpa using (Rat.cast_lt (K := ℝ)).2 h1uq
    simpa [thetaCuspFirstAtomHighOrderUpperIntervalMass64] using hcast
  have h3ur :
      (∑ j ∈ Finset.range 64,
          thetaCuspFirstAtomHighOrderUpperIntervalMass64 3 j) +
        1 / 40000000 < (0.00059935 : ℝ) := by
    have hcast :
        (((∑ j ∈ Finset.range 64,
          ThetaRationalQuadrature.upperMass 3 j : ℚ) : ℚ) : ℝ) +
            1 / 40000000 < (0.00059935 : ℝ) := by
      simpa using (Rat.cast_lt (K := ℝ)).2 h3uq
    simpa [thetaCuspFirstAtomHighOrderUpperIntervalMass64] using hcast
  have h0 := h0r.trans_le
    (sum_firstAtomHighOrderLowerMass64_le_thetaCuspAtomRawEvenMoment 0)
  have h1 := h1r.trans_le
    (sum_firstAtomHighOrderLowerMass64_le_thetaCuspAtomRawEvenMoment 1)
  have h2 := h2r.trans_le
    (sum_firstAtomHighOrderLowerMass64_le_thetaCuspAtomRawEvenMoment 2)
  have h1upper := thetaCuspAtomRawEvenMoment_le_sum_firstAtomHighOrderUpperMass64_add_tail 1
  have h3upper := thetaCuspAtomRawEvenMoment_le_sum_firstAtomHighOrderUpperMass64_add_tail 3
  have h1tail := thetaCuspFirstAtom_tail_evenMoment_lt_one_div_fortyMillion
    (r := 1) (by omega)
  have h3tail := thetaCuspFirstAtom_tail_evenMoment_lt_one_div_fortyMillion
    (r := 3) (by omega)
  refine ⟨h0, h1, ?_, h2, ?_⟩
  · have htailAdd :
        (∑ j ∈ Finset.range 64,
            thetaCuspFirstAtomHighOrderUpperIntervalMass64 1 j) +
            (∫ x in Ioi (1 : ℝ),
              2 * (x ^ (2 * 1) * thetaCuspSourceTerm x 1)) <
          (∑ j ∈ Finset.range 64,
            thetaCuspFirstAtomHighOrderUpperIntervalMass64 1 j) +
            1 / 40000000 := by
      simpa [add_comm] using
        add_lt_add_left h1tail
          (∑ j ∈ Finset.range 64,
            thetaCuspFirstAtomHighOrderUpperIntervalMass64 1 j)
    exact h1upper.trans_lt (htailAdd.trans h1ur)
  · have htailAdd :
        (∑ j ∈ Finset.range 64,
            thetaCuspFirstAtomHighOrderUpperIntervalMass64 3 j) +
            (∫ x in Ioi (1 : ℝ),
              2 * (x ^ (2 * 3) * thetaCuspSourceTerm x 1)) <
          (∑ j ∈ Finset.range 64,
            thetaCuspFirstAtomHighOrderUpperIntervalMass64 3 j) +
            1 / 40000000 := by
      simpa [add_comm] using
        add_lt_add_left h3tail
          (∑ j ∈ Finset.range 64,
            thetaCuspFirstAtomHighOrderUpperIntervalMass64 3 j)
    exact h3upper.trans_lt (htailAdd.trans h3ur)

end

end RHTower
