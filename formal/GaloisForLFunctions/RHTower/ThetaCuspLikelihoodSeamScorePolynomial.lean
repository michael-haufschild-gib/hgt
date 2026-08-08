import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodThermodynamicKL
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# All-order score orthogonality at the theta likelihood modular seam

Constructs exact channel-score polynomials, proves their degree and leading coefficient,
and closes every odd score against the normalized seam probability measure.
-/


open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

def thetaCuspLikelihoodScoreExpPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | m + 1 => C 2 * X *
      (derivative (thetaCuspLikelihoodScoreExpPolynomial m) -
        C Real.pi * thetaCuspLikelihoodScoreExpPolynomial m)

@[simp] theorem thetaCuspLikelihoodScoreExpPolynomial_zero :
    thetaCuspLikelihoodScoreExpPolynomial 0 = 1 := rfl

theorem thetaCuspLikelihoodScoreExpPolynomial_succ (m : ℕ) :
    thetaCuspLikelihoodScoreExpPolynomial (m + 1) = C 2 * X *
      (derivative (thetaCuspLikelihoodScoreExpPolynomial m) -
        C Real.pi * thetaCuspLikelihoodScoreExpPolynomial m) := rfl

theorem hasDerivAt_thetaCuspLikelihoodCoordinate_exp_sq (x : ℝ) :
    HasDerivAt thetaCuspLikelihoodCoordinate
      (2 * Real.pi * Real.exp x ^ 2) x := by
  have h := hasDerivAt_thetaCuspLikelihoodCoordinate x
  convert h using 1
  unfold thetaCuspSingleAtomReflectionScale
  simp only [Nat.cast_one, one_pow, mul_one]
  rw [show 2 * x = x + x by ring, Real.exp_add]
  ring

theorem iteratedDeriv_exp_neg_thetaCuspLikelihoodCoordinate_mul
    (m : ℕ) (t : ℝ) :
    iteratedDeriv m
        (fun y : ℝ => Real.exp (-thetaCuspLikelihoodCoordinate y * t)) =
      fun x => Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
        eval (t * Real.exp x ^ 2) (thetaCuspLikelihoodScoreExpPolynomial m) := by
  induction m with
  | zero => funext x; simp [thetaCuspLikelihoodScoreExpPolynomial]
  | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      let u : ℝ := t * Real.exp x ^ 2
      have hu : HasDerivAt (fun y : ℝ => t * Real.exp y ^ 2) (2 * u) x := by
        have h := ((Real.hasDerivAt_exp x).pow 2).const_mul t
        simpa only [Pi.pow_apply] using h.congr_deriv (by dsimp [u]; ring)
      have hE : HasDerivAt
          (fun y : ℝ => Real.exp (-thetaCuspLikelihoodCoordinate y * t))
          ((-2 * Real.pi * u) *
            Real.exp (-thetaCuspLikelihoodCoordinate x * t)) x := by
        have hinner :=
          (hasDerivAt_thetaCuspLikelihoodCoordinate_exp_sq x).neg.mul_const t
        have hcomp := (Real.hasDerivAt_exp
          (-thetaCuspLikelihoodCoordinate x * t)).comp x hinner
        exact hcomp.congr_deriv (by dsimp [u]; ring)
      have hP : HasDerivAt
          (fun y : ℝ => eval (t * Real.exp y ^ 2) (thetaCuspLikelihoodScoreExpPolynomial m))
          (eval u (derivative (thetaCuspLikelihoodScoreExpPolynomial m)) * (2 * u)) x := by
        exact ((thetaCuspLikelihoodScoreExpPolynomial m).hasDerivAt u).comp x hu
      have hmul := hE.mul hP
      change deriv (((fun y : ℝ => Real.exp
        (-thetaCuspLikelihoodCoordinate y * t)) *
          fun y => eval (t * Real.exp y ^ 2) (thetaCuspLikelihoodScoreExpPolynomial m))) x = _
      rw [hmul.deriv]
      rw [thetaCuspLikelihoodScoreExpPolynomial_succ]
      simp only [eval_mul, eval_C, eval_X, eval_sub]
      dsimp [u]
      ring

theorem iteratedDeriv_exp_neg_thetaCuspLikelihoodCoordinate_mul_apply
    (m : ℕ) (t x : ℝ) :
    iteratedDeriv m
        (fun y : ℝ => Real.exp (-thetaCuspLikelihoodCoordinate y * t)) x =
      Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
        eval (t * Real.exp x ^ 2) (thetaCuspLikelihoodScoreExpPolynomial m) :=
  congrFun (iteratedDeriv_exp_neg_thetaCuspLikelihoodCoordinate_mul m t) x

theorem thetaCuspLikelihoodScoreExpPolynomial_natDegree_le (m : ℕ) :
    (thetaCuspLikelihoodScoreExpPolynomial m).natDegree ≤ m := by
  induction m with
  | zero => simp [thetaCuspLikelihoodScoreExpPolynomial]
  | succ m ih =>
      rw [thetaCuspLikelihoodScoreExpPolynomial_succ]
      have hCX : (C (2 : ℝ) * X).natDegree ≤ 1 := by
        exact natDegree_mul_le.trans (by norm_num)
      have hd := natDegree_derivative_le (thetaCuspLikelihoodScoreExpPolynomial m)
      have hpi : (C Real.pi * thetaCuspLikelihoodScoreExpPolynomial m).natDegree ≤ m := by
        exact natDegree_mul_le.trans (by simpa using ih)
      have hd' : (derivative (thetaCuspLikelihoodScoreExpPolynomial m)).natDegree ≤ m := by
        omega
      have hsub :
          (derivative (thetaCuspLikelihoodScoreExpPolynomial m) -
            C Real.pi * thetaCuspLikelihoodScoreExpPolynomial m).natDegree ≤ m :=
        (natDegree_sub_le _ _).trans (max_le hd' hpi)
      exact natDegree_mul_le.trans ((Nat.add_le_add hCX hsub).trans_eq (by omega))

theorem thetaCuspLikelihoodScoreExpPolynomial_coeff_natDegree (m : ℕ) :
    (thetaCuspLikelihoodScoreExpPolynomial m).coeff m = (-2 * Real.pi) ^ m := by
  induction m with
  | zero => simp [thetaCuspLikelihoodScoreExpPolynomial]
  | succ m ih =>
      rw [thetaCuspLikelihoodScoreExpPolynomial_succ]
      have hzero : (thetaCuspLikelihoodScoreExpPolynomial m).coeff (m + 1) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        exact (thetaCuspLikelihoodScoreExpPolynomial_natDegree_le m).trans_lt (Nat.lt_succ_self m)
      rw [mul_assoc, coeff_C_mul, coeff_X_mul, coeff_sub, coeff_derivative,
        coeff_C_mul, hzero, ih]
      ring

theorem thetaCuspLikelihoodScoreExpPolynomial_natDegree (m : ℕ) :
    (thetaCuspLikelihoodScoreExpPolynomial m).natDegree = m := by
  apply le_antisymm (thetaCuspLikelihoodScoreExpPolynomial_natDegree_le m)
  apply le_natDegree_of_ne_zero
  rw [thetaCuspLikelihoodScoreExpPolynomial_coeff_natDegree]
  exact pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem thetaCuspLikelihoodScoreExpPolynomial_leadingCoeff (m : ℕ) :
    (thetaCuspLikelihoodScoreExpPolynomial m).leadingCoeff = (-2 * Real.pi) ^ m := by
  rw [leadingCoeff, thetaCuspLikelihoodScoreExpPolynomial_natDegree,
    thetaCuspLikelihoodScoreExpPolynomial_coeff_natDegree]

def thetaCuspLikelihoodSeamScorePolynomial (m : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (m + 1),
    C (((m.choose j : ℕ) : ℝ) *
      iteratedDeriv j (fun x : ℝ => thetaCuspSourceTerm x 1) 0 /
        thetaCuspSourceTerm 0 1) *
      thetaCuspLikelihoodScoreExpPolynomial (m - j)

theorem iteratedDeriv_thetaCuspLikelihoodSeamChannel_eq_score
    (m : ℕ) (t : ℝ) :
    iteratedDeriv m (fun x : ℝ => thetaCuspLikelihoodSeamChannel x t) 0 =
      thetaCuspLikelihoodSeamChannel 0 t * eval t (thetaCuspLikelihoodSeamScorePolynomial m) := by
  have hh : ContDiffAt ℝ m (fun x : ℝ => thetaCuspSourceTerm x 1) 0 := by
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hE : ContDiffAt ℝ m
      (fun x : ℝ => Real.exp (-thetaCuspLikelihoodCoordinate x * t)) 0 := by
    unfold thetaCuspLikelihoodCoordinate
    fun_prop
  unfold thetaCuspLikelihoodSeamChannel
  change iteratedDeriv m
    (((fun x : ℝ => thetaCuspSourceTerm x 1) *
      fun x => Real.exp (-thetaCuspLikelihoodCoordinate x * t))) 0 = _
  rw [iteratedDeriv_mul hh hE]
  simp_rw [iteratedDeriv_exp_neg_thetaCuspLikelihoodCoordinate_mul_apply]
  simp only [Real.exp_zero, one_pow, mul_one]
  unfold thetaCuspLikelihoodSeamScorePolynomial
  rw [Polynomial.eval_finsetSum]
  simp only [eval_mul, eval_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hsource : thetaCuspSourceTerm 0 1 ≠ 0 :=
    thetaCuspSourceTerm_one_zero_pos.ne'
  field_simp [hsource]

theorem thetaCuspLikelihoodSeamScorePolynomial_natDegree_le (m : ℕ) :
    (thetaCuspLikelihoodSeamScorePolynomial m).natDegree ≤ m := by
  unfold thetaCuspLikelihoodSeamScorePolynomial
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact natDegree_mul_le.trans (by
    simpa using (thetaCuspLikelihoodScoreExpPolynomial_natDegree_le (m - j)).trans (Nat.sub_le m j))

theorem thetaCuspLikelihoodSeamScorePolynomial_coeff_natDegree (m : ℕ) :
    (thetaCuspLikelihoodSeamScorePolynomial m).coeff m = (-2 * Real.pi) ^ m := by
  unfold thetaCuspLikelihoodSeamScorePolynomial
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · rw [coeff_C_mul]
    simp [thetaCuspSourceTerm_one_zero_pos.ne',
      thetaCuspLikelihoodScoreExpPolynomial_coeff_natDegree]
  · intro j hj hj0
    rw [coeff_C_mul]
    have hjlt : j < m + 1 := Finset.mem_range.mp hj
    have hjle : j ≤ m := by omega
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hlt : (thetaCuspLikelihoodScoreExpPolynomial (m - j)).natDegree < m :=
      (thetaCuspLikelihoodScoreExpPolynomial_natDegree_le (m - j)).trans_lt (Nat.sub_lt (by omega) hjpos)
    rw [coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
  · simp

theorem thetaCuspLikelihoodSeamScorePolynomial_natDegree (m : ℕ) :
    (thetaCuspLikelihoodSeamScorePolynomial m).natDegree = m := by
  apply le_antisymm (thetaCuspLikelihoodSeamScorePolynomial_natDegree_le m)
  apply le_natDegree_of_ne_zero
  rw [thetaCuspLikelihoodSeamScorePolynomial_coeff_natDegree]
  exact pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem thetaCuspLikelihoodSeamScorePolynomial_leadingCoeff (m : ℕ) :
    (thetaCuspLikelihoodSeamScorePolynomial m).leadingCoeff = (-2 * Real.pi) ^ m := by
  rw [leadingCoeff, thetaCuspLikelihoodSeamScorePolynomial_natDegree,
    thetaCuspLikelihoodSeamScorePolynomial_coeff_natDegree]

def thetaCuspLikelihoodSeamMoment (B : ℝ) (m : ℕ) : ℝ :=
  ∫ t : ℝ, t ^ m * Real.exp (-B * t) ∂thetaCuspLikelihoodSeamMeasure

theorem integrable_pow_mul_exp_neg_thetaCuspLikelihoodSeamMeasure
    (m : ℕ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => t ^ m * Real.exp (-B * t))
      thetaCuspLikelihoodSeamMeasure := by
  rw [thetaCuspLikelihoodSeamMeasure]
  exact Integrable.add_measure
    (integrable_dirac (by simp))
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure m hB)

theorem thetaCuspLikelihoodSeamMoment_zero
    {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodSeamMoment B 0 =
      thetaCuspLikelihoodPartition B := by
  have hdirac : Integrable (fun t : ℝ => t ^ 0 * Real.exp (-B * t))
      (Measure.dirac 0) := integrable_dirac (by simp)
  have hhigher : Integrable (fun t : ℝ => t ^ 0 * Real.exp (-B * t))
      thetaCuspHigherLikelihoodSpectralMeasure :=
    integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 0 hB
  rw [thetaCuspLikelihoodSeamMoment, thetaCuspLikelihoodSeamMeasure,
    integral_add_measure hdirac hhigher, integral_dirac]
  simp only [pow_zero, one_mul, mul_zero, Real.exp_zero]
  rw [integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB]
  simp [thetaCuspLikelihoodPartition]

theorem thetaCuspLikelihoodSeamMoment_succ
    (m : ℕ) {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodSeamMoment B (m + 1) =
      thetaCuspHigherLikelihoodSpectralMoment B (m + 1) := by
  have hdirac : Integrable
      (fun t : ℝ => t ^ (m + 1) * Real.exp (-B * t))
      (Measure.dirac 0) := integrable_dirac (by simp)
  have hhigher : Integrable
      (fun t : ℝ => t ^ (m + 1) * Real.exp (-B * t))
      thetaCuspHigherLikelihoodSpectralMeasure :=
    integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure (m + 1) hB
  rw [thetaCuspLikelihoodSeamMoment, thetaCuspLikelihoodSeamMeasure,
    integral_add_measure hdirac hhigher, integral_dirac]
  simp only [zero_pow (Nat.succ_ne_zero m), zero_mul, zero_add]
  exact (thetaCuspHigherLikelihoodSpectralMoment_eq_integral B (m + 1)).symm

theorem hasDerivAt_thetaCuspLikelihoodSeamMoment
    (m : ℕ) {B : ℝ} (hB : 0 < B) :
    HasDerivAt (fun q => thetaCuspLikelihoodSeamMoment q m)
      (-thetaCuspLikelihoodSeamMoment B (m + 1)) B := by
  have hevent : ∀ᶠ q in nhds B, 0 < q := Ioi_mem_nhds hB
  cases m with
  | zero =>
      have heq : (fun q => thetaCuspLikelihoodSeamMoment q 0) =ᶠ[nhds B]
          thetaCuspLikelihoodPartition := by
        filter_upwards [hevent] with q hq
        exact thetaCuspLikelihoodSeamMoment_zero hq
      have h := hasDerivAt_thetaCuspLikelihoodPartition hB
      rw [thetaCuspLikelihoodSeamMoment_succ 0 hB]
      exact h.congr_of_eventuallyEq heq
  | succ m =>
      have heq :
          (fun q => thetaCuspLikelihoodSeamMoment q (m + 1)) =ᶠ[nhds B]
            fun q => thetaCuspHigherLikelihoodSpectralMoment q (m + 1) := by
        filter_upwards [hevent] with q hq
        exact thetaCuspLikelihoodSeamMoment_succ m hq
      have h := hasDerivAt_thetaCuspHigherLikelihoodSpectralMoment (m + 1) hB
      rw [thetaCuspLikelihoodSeamMoment_succ (m + 1) hB]
      exact h.congr_of_eventuallyEq heq

def thetaCuspLikelihoodPolynomialLaplace (p : ℝ[X]) (x : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
    eval (t * Real.exp x ^ 2) p ∂thetaCuspLikelihoodSeamMeasure

theorem integrable_exp_mul_eval_thetaCuspLikelihoodSeamMeasure
    (p : ℝ[X]) {x : ℝ} (hBx : 0 < thetaCuspLikelihoodCoordinate x) :
    Integrable (fun t : ℝ =>
      Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
        eval (t * Real.exp x ^ 2) p)
      thetaCuspLikelihoodSeamMeasure := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      apply (hp.add hq).congr
      filter_upwards with t
      change
        Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
              eval (t * Real.exp x ^ 2) p +
            Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
              eval (t * Real.exp x ^ 2) q =
          Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
            eval (t * Real.exp x ^ 2) (p + q)
      rw [eval_add]
      ring
  | monomial n a =>
      have h :=
        (integrable_pow_mul_exp_neg_thetaCuspLikelihoodSeamMeasure n hBx).const_mul
          (a * (Real.exp x ^ 2) ^ n)
      apply h.congr
      filter_upwards with t
      simp [eval_monomial]
      ring

theorem thetaCuspLikelihoodPolynomialLaplace_monomial
    (n : ℕ) (a x : ℝ) :
    thetaCuspLikelihoodPolynomialLaplace (monomial n a) x =
      a * (Real.exp x ^ 2) ^ n *
        thetaCuspLikelihoodSeamMoment
          (thetaCuspLikelihoodCoordinate x) n := by
  unfold thetaCuspLikelihoodPolynomialLaplace
  rw [show (fun t : ℝ =>
      Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
        eval (t * Real.exp x ^ 2) (monomial n a)) =
      fun t => (a * (Real.exp x ^ 2) ^ n) *
        (t ^ n * Real.exp (-thetaCuspLikelihoodCoordinate x * t)) by
    funext t
    simp [eval_monomial]
    ring]
  rw [integral_const_mul]
  rfl

def thetaCuspLikelihoodScoreOperator (p : ℝ[X]) : ℝ[X] :=
  C 2 * X * (derivative p - C Real.pi * p)

theorem thetaCuspLikelihoodPolynomialLaplace_add
    (p q : ℝ[X]) {x : ℝ} (hBx : 0 < thetaCuspLikelihoodCoordinate x) :
    thetaCuspLikelihoodPolynomialLaplace (p + q) x =
      thetaCuspLikelihoodPolynomialLaplace p x +
        thetaCuspLikelihoodPolynomialLaplace q x := by
  unfold thetaCuspLikelihoodPolynomialLaplace
  have hp := integrable_exp_mul_eval_thetaCuspLikelihoodSeamMeasure p hBx
  have hq := integrable_exp_mul_eval_thetaCuspLikelihoodSeamMeasure q hBx
  rw [show (fun t : ℝ =>
      Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
        eval (t * Real.exp x ^ 2) (p + q)) =
      (fun t : ℝ => Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
        eval (t * Real.exp x ^ 2) p) +
      fun t : ℝ => Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
        eval (t * Real.exp x ^ 2) q by
    funext t
    simp only [Pi.add_apply, eval_add]
    ring]
  exact integral_add hp hq

theorem thetaCuspLikelihoodPolynomialLaplace_scoreOperator_monomial
    (n : ℕ) (a x : ℝ) (hBx : 0 < thetaCuspLikelihoodCoordinate x) :
    thetaCuspLikelihoodPolynomialLaplace
        (thetaCuspLikelihoodScoreOperator (monomial n a)) x =
      2 * (n : ℝ) * a * (Real.exp x ^ 2) ^ n *
          thetaCuspLikelihoodSeamMoment
            (thetaCuspLikelihoodCoordinate x) n -
        2 * Real.pi * a * (Real.exp x ^ 2) ^ (n + 1) *
          thetaCuspLikelihoodSeamMoment
            (thetaCuspLikelihoodCoordinate x) (n + 1) := by
  cases n with
  | zero =>
      rw [show thetaCuspLikelihoodScoreOperator (monomial 0 a) =
          monomial 1 (-2 * Real.pi * a) by
        simp only [← C_mul_X_pow_eq_monomial]
        simp [thetaCuspLikelihoodScoreOperator]
        ring]
      rw [thetaCuspLikelihoodPolynomialLaplace_monomial 1
        (-2 * Real.pi * a) x]
      norm_num
  | succ n =>
      rw [show thetaCuspLikelihoodScoreOperator (monomial (n + 1) a) =
          monomial (n + 1) (2 * (n + 1 : ℕ) * a) +
            monomial (n + 2) (-2 * Real.pi * a) by
        simp only [← C_mul_X_pow_eq_monomial]
        simp [thetaCuspLikelihoodScoreOperator, derivative_pow]
        ring]
      rw [thetaCuspLikelihoodPolynomialLaplace_add _ _ hBx,
        thetaCuspLikelihoodPolynomialLaplace_monomial (n + 1)
          (2 * (n + 1 : ℕ) * a) x,
        thetaCuspLikelihoodPolynomialLaplace_monomial (n + 2)
          (-2 * Real.pi * a) x]
      push_cast
      ring

theorem hasDerivAt_thetaCuspLikelihoodPolynomialLaplace_monomial
    (n : ℕ) (a : ℝ) {x : ℝ}
    (hBx : 0 < thetaCuspLikelihoodCoordinate x) :
    HasDerivAt
      (fun y => thetaCuspLikelihoodPolynomialLaplace (monomial n a) y)
      (thetaCuspLikelihoodPolynomialLaplace
        (thetaCuspLikelihoodScoreOperator (monomial n a)) x) x := by
  let u : ℝ := Real.exp x ^ 2
  let M : ℕ → ℝ := fun k =>
    thetaCuspLikelihoodSeamMoment (thetaCuspLikelihoodCoordinate x) k
  have hu : HasDerivAt (fun y : ℝ => Real.exp y ^ 2) (2 * u) x := by
    change HasDerivAt (Real.exp ^ (2 : ℕ)) (2 * u) x
    exact ((Real.hasDerivAt_exp x).pow 2).congr_deriv (by dsimp [u]; ring)
  have hB := hasDerivAt_thetaCuspLikelihoodCoordinate_exp_sq x
  have hM :=
    (hasDerivAt_thetaCuspLikelihoodSeamMoment n hBx).comp x hB
  have hcalc : HasDerivAt
      (fun y : ℝ => a * (Real.exp y ^ 2) ^ n *
        thetaCuspLikelihoodSeamMoment
          (thetaCuspLikelihoodCoordinate y) n)
      (2 * (n : ℝ) * a * u ^ n * M n -
        2 * Real.pi * a * u ^ (n + 1) * M (n + 1)) x := by
    have h := ((hu.pow n).mul hM).const_mul a
    have heqfun :
        (fun y : ℝ => a * (Real.exp y ^ 2) ^ n *
          thetaCuspLikelihoodSeamMoment
            (thetaCuspLikelihoodCoordinate y) n) =
        fun y => a *
          (((fun z : ℝ => Real.exp z ^ 2) ^ n *
            (fun q => thetaCuspLikelihoodSeamMoment q n) ∘
              thetaCuspLikelihoodCoordinate) y) := by
      funext y
      simp only [Pi.pow_apply, Pi.mul_apply, Function.comp_apply]
      ring
    rw [heqfun]
    apply h.congr_deriv
    cases n with
    | zero =>
        dsimp [u, M]
        ring
    | succ n =>
        dsimp [u, M]
        simp only [pow_succ]
        push_cast
        ring
  have hevent : ∀ᶠ y in nhds x, 0 < thetaCuspLikelihoodCoordinate y :=
    hB.continuousAt.tendsto (Ioi_mem_nhds hBx)
  have heq :
      (fun y => thetaCuspLikelihoodPolynomialLaplace (monomial n a) y) =ᶠ[nhds x]
        fun y => a * (Real.exp y ^ 2) ^ n *
          thetaCuspLikelihoodSeamMoment
            (thetaCuspLikelihoodCoordinate y) n := by
    filter_upwards [hevent] with y hy
    exact thetaCuspLikelihoodPolynomialLaplace_monomial n a y
  rw [thetaCuspLikelihoodPolynomialLaplace_scoreOperator_monomial n a x hBx]
  exact hcalc.congr_of_eventuallyEq heq

theorem hasDerivAt_thetaCuspLikelihoodPolynomialLaplace
    (p : ℝ[X]) {x : ℝ}
    (hBx : 0 < thetaCuspLikelihoodCoordinate x) :
    HasDerivAt
      (fun y => thetaCuspLikelihoodPolynomialLaplace p y)
      (thetaCuspLikelihoodPolynomialLaplace
        (thetaCuspLikelihoodScoreOperator p) x) x := by
  induction p using Polynomial.induction_on' generalizing x with
  | monomial n a =>
      exact hasDerivAt_thetaCuspLikelihoodPolynomialLaplace_monomial n a hBx
  | add p q hp hq =>
      have hsum := (hp hBx).add (hq hBx)
      have hop : thetaCuspLikelihoodScoreOperator (p + q) =
          thetaCuspLikelihoodScoreOperator p +
            thetaCuspLikelihoodScoreOperator q := by
        simp only [thetaCuspLikelihoodScoreOperator, derivative_add,
          mul_add, sub_eq_add_neg, neg_add_rev]
        ring
      rw [hop, thetaCuspLikelihoodPolynomialLaplace_add _ _ hBx]
      have hevent : ∀ᶠ y in nhds x, 0 < thetaCuspLikelihoodCoordinate y :=
        (hasDerivAt_thetaCuspLikelihoodCoordinate_exp_sq x).continuousAt.tendsto
          (Ioi_mem_nhds hBx)
      have heq :
          (fun y => thetaCuspLikelihoodPolynomialLaplace (p + q) y) =ᶠ[nhds x]
            fun y => thetaCuspLikelihoodPolynomialLaplace p y +
              thetaCuspLikelihoodPolynomialLaplace q y := by
        filter_upwards [hevent] with y hy
        exact thetaCuspLikelihoodPolynomialLaplace_add p q hy
      exact hsum.congr_of_eventuallyEq heq

theorem thetaCuspLikelihoodScoreExpPolynomial_eq_iterate_scoreOperator (m : ℕ) :
    thetaCuspLikelihoodScoreExpPolynomial (m + 1) =
      thetaCuspLikelihoodScoreOperator (thetaCuspLikelihoodScoreExpPolynomial m) := rfl

theorem iteratedDeriv_thetaCuspLikelihoodPolynomialLaplace_one
    (m : ℕ) {x : ℝ} (hBx : 0 < thetaCuspLikelihoodCoordinate x) :
    iteratedDeriv m
        (fun y => thetaCuspLikelihoodPolynomialLaplace 1 y) x =
      thetaCuspLikelihoodPolynomialLaplace
        (thetaCuspLikelihoodScoreExpPolynomial m) x := by
  induction m generalizing x with
  | zero => simp [thetaCuspLikelihoodScoreExpPolynomial]
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have hevent : ∀ᶠ y in nhds x, 0 < thetaCuspLikelihoodCoordinate y :=
        (hasDerivAt_thetaCuspLikelihoodCoordinate_exp_sq x).continuousAt.tendsto
          (Ioi_mem_nhds hBx)
      have heq :
          iteratedDeriv m
              (fun y => thetaCuspLikelihoodPolynomialLaplace 1 y) =ᶠ[nhds x]
            fun y => thetaCuspLikelihoodPolynomialLaplace
              (thetaCuspLikelihoodScoreExpPolynomial m) y := by
        filter_upwards [hevent] with y hy
        exact ih hy
      rw [heq.deriv_eq]
      rw [thetaCuspLikelihoodScoreExpPolynomial_eq_iterate_scoreOperator]
      exact (hasDerivAt_thetaCuspLikelihoodPolynomialLaplace
        (thetaCuspLikelihoodScoreExpPolynomial m) hBx).deriv

theorem thetaCuspLikelihoodPolynomialLaplace_C_mul
    (c : ℝ) (p : ℝ[X]) (x : ℝ) :
    thetaCuspLikelihoodPolynomialLaplace (C c * p) x =
      c * thetaCuspLikelihoodPolynomialLaplace p x := by
  unfold thetaCuspLikelihoodPolynomialLaplace
  rw [show (fun t : ℝ =>
      Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
        eval (t * Real.exp x ^ 2) (C c * p)) =
      fun t => c * (Real.exp (-thetaCuspLikelihoodCoordinate x * t) *
        eval (t * Real.exp x ^ 2) p) by
    funext t
    simp only [eval_mul, eval_C]
    ring]
  rw [integral_const_mul]

theorem thetaCuspLikelihoodPolynomialLaplace_finsetSum
    {ι : Type*} (s : Finset ι) (p : ι → ℝ[X])
    {x : ℝ} (hBx : 0 < thetaCuspLikelihoodCoordinate x) :
    thetaCuspLikelihoodPolynomialLaplace (∑ i ∈ s, p i) x =
      ∑ i ∈ s, thetaCuspLikelihoodPolynomialLaplace (p i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thetaCuspLikelihoodPolynomialLaplace]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [thetaCuspLikelihoodPolynomialLaplace_add _ _ hBx, ih]

theorem thetaCuspSourceTerm_zero_mul_polynomialLaplace_score
    (m : ℕ) :
    thetaCuspSourceTerm 0 1 *
        thetaCuspLikelihoodPolynomialLaplace
          (thetaCuspLikelihoodSeamScorePolynomial m) 0 =
      ∑ j ∈ Finset.range (m + 1),
        ((m.choose j : ℕ) : ℝ) *
          iteratedDeriv j (fun x : ℝ => thetaCuspSourceTerm x 1) 0 *
          thetaCuspLikelihoodPolynomialLaplace
            (thetaCuspLikelihoodScoreExpPolynomial (m - j)) 0 := by
  have hB0 : 0 < thetaCuspLikelihoodCoordinate 0 :=
    thetaCuspLikelihoodCoordinate_pos (by norm_num)
  rw [thetaCuspLikelihoodSeamScorePolynomial,
    thetaCuspLikelihoodPolynomialLaplace_finsetSum _ _ hB0]
  simp_rw [thetaCuspLikelihoodPolynomialLaplace_C_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hsource := thetaCuspSourceTerm_one_zero_pos.ne'
  field_simp [hsource]

theorem thetaCuspSourceTerm_zero_mul_polynomialLaplace_score_eq_fullJet
    (m : ℕ) :
    thetaCuspSourceTerm 0 1 *
        thetaCuspLikelihoodPolynomialLaplace
          (thetaCuspLikelihoodSeamScorePolynomial m) 0 =
      iteratedDeriv m thetaCuspFullSource 0 := by
  let h : ℝ → ℝ := fun y => thetaCuspSourceTerm y 1
  let F : ℝ → ℝ := fun y =>
    thetaCuspLikelihoodPolynomialLaplace 1 y
  have hB0 : 0 < thetaCuspLikelihoodCoordinate 0 :=
    thetaCuspLikelihoodCoordinate_pos (by norm_num)
  have hh : ContDiffAt ℝ m h 0 := by
    dsimp [h]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hfull : ContDiffAt ℝ m thetaCuspFullSource 0 :=
    contDiff_thetaCuspFullSource.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (show (m : ℕ∞) ≤ ⊤ from le_top))
  have hquot : ContDiffAt ℝ m (fun y => thetaCuspFullSource y / h y) 0 := by
    apply hfull.div hh
    exact thetaCuspSourceTerm_one_zero_pos.ne'
  have hevent : ∀ᶠ y in nhds 0, 0 < thetaCuspLikelihoodCoordinate y :=
    (hasDerivAt_thetaCuspLikelihoodCoordinate_exp_sq 0).continuousAt.tendsto
      (Ioi_mem_nhds hB0)
  have hFpartition : ∀ᶠ y in nhds 0,
      F y = thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate y) := by
    filter_upwards [hevent] with y hy
    have hmon := thetaCuspLikelihoodPolynomialLaplace_monomial 0 1 y
    have hone : (monomial 0 (1 : ℝ)) = 1 := by simp
    rw [hone] at hmon
    simpa [F, thetaCuspLikelihoodSeamMoment_zero hy] using hmon
  have hfactor : ∀ᶠ y in nhds 0,
      thetaCuspFullSource y = h y *
        thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate y) := by
    filter_upwards [hevent] with y hy
    have hfac :=
      thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral_of_coordinate_pos hy
    rw [integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hy] at hfac
    simpa [h, thetaCuspLikelihoodPartition] using hfac
  have hFeq : F =ᶠ[nhds 0] fun y => thetaCuspFullSource y / h y := by
    filter_upwards [hFpartition, hfactor, hevent] with y hpart hfac hy
    rw [hpart, hfac]
    have hhpos := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hy
    have hhy : h y ≠ 0 := by simpa [h] using hhpos.ne'
    field_simp [hhy]
  have hF : ContDiffAt ℝ m F 0 := hquot.congr_of_eventuallyEq hFeq
  calc
    thetaCuspSourceTerm 0 1 *
          thetaCuspLikelihoodPolynomialLaplace
            (thetaCuspLikelihoodSeamScorePolynomial m) 0 =
        ∑ j ∈ Finset.range (m + 1),
          ((m.choose j : ℕ) : ℝ) *
            iteratedDeriv j h 0 *
            thetaCuspLikelihoodPolynomialLaplace
              (thetaCuspLikelihoodScoreExpPolynomial (m - j)) 0 := by
      simpa [h] using thetaCuspSourceTerm_zero_mul_polynomialLaplace_score m
    _ = iteratedDeriv m (h * F) 0 := by
      rw [iteratedDeriv_mul hh hF]
      apply Finset.sum_congr rfl
      intro j hj
      rw [iteratedDeriv_thetaCuspLikelihoodPolynomialLaplace_one
        (m - j) hB0]
    _ = iteratedDeriv m thetaCuspFullSource 0 := by
      have heq : h * F =ᶠ[nhds 0] thetaCuspFullSource := by
        filter_upwards [hFpartition, hfactor] with y hpart hfac
        simp only [Pi.mul_apply]
        rw [hpart, ← hfac]
      exact heq.iteratedDeriv_eq m

theorem thetaCuspLikelihoodPolynomialLaplace_score_zero_of_odd
    {m : ℕ} (hm : Odd m) :
    thetaCuspLikelihoodPolynomialLaplace
      (thetaCuspLikelihoodSeamScorePolynomial m) 0 = 0 := by
  have hmain :=
    thetaCuspSourceTerm_zero_mul_polynomialLaplace_score_eq_fullJet m
  rw [iteratedDeriv_thetaCuspFullSource_zero_of_odd hm] at hmain
  exact (mul_eq_zero.mp hmain).resolve_left
    thetaCuspSourceTerm_one_zero_pos.ne'

theorem integral_eval_thetaCuspLikelihoodSeamScorePolynomial_probabilityMeasure_zero_of_odd
    {m : ℕ} (hm : Odd m) :
    (∫ t : ℝ, eval t (thetaCuspLikelihoodSeamScorePolynomial m)
      ∂thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate 0)) = 0 := by
  have hB0 : 0 < thetaCuspLikelihoodCoordinate 0 :=
    thetaCuspLikelihoodCoordinate_pos (by norm_num)
  rw [thetaCuspLikelihoodProbabilityMeasure_eq_tilted hB0, integral_tilted,
    integral_exp_neg_mul_thetaCuspLikelihoodSeamMeasure hB0]
  have hz := thetaCuspLikelihoodPolynomialLaplace_score_zero_of_odd hm
  unfold thetaCuspLikelihoodPolynomialLaplace at hz
  simp only [Real.exp_zero, one_pow, mul_one] at hz
  rw [show (fun t : ℝ =>
      (Real.exp (-thetaCuspLikelihoodCoordinate 0 * t) /
          thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate 0)) •
        eval t (thetaCuspLikelihoodSeamScorePolynomial m)) =
      fun t =>
        (thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate 0))⁻¹ *
          (Real.exp (-thetaCuspLikelihoodCoordinate 0 * t) *
            eval t (thetaCuspLikelihoodSeamScorePolynomial m)) by
    funext t
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring]
  rw [integral_const_mul, hz, mul_zero]


end
end RHTower
