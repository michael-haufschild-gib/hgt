import GaloisForLFunctions.RHTower.LaguerreInequality
import GaloisForLFunctions.RHTower.XiMassPolynomialVerticalResolvent

/-!
# Finite cross-frequency causal Schwarz all-pass no-go

This module kills the finite value-only cross-frequency producer proposed for the HB route.
For every nonempty finite symmetric real frequency set it constructs a nonconstant rational
multiplier which

* is holomorphic on the open upper half-plane;
* has unit modulus on the real axis;
* obeys the real-time Schwarz law `A(-conj z) = conj(A z)`;
* equals one at every sampled frequency; and
* has strictly positive boundary logarithmic phase clock everywhere.

The hard input proved here is a strict squarefree Laguerre law. For the finite root polynomial
`P_S = ∏_{a ∈ S} (X-a)`, `(P_S')²-P_S P_S''` is strictly positive on all of `ℝ`.
It both excludes boundary pole collisions and gives phase orientation. A Coulomb-sum identity
then excludes poles in the upper half-plane. Schwarz symmetrization preserves causality and adds
the two positive clocks.

Consequently finite cross-frequency values cannot identify physical all-pass phase. In the RH
chain this kills the first arrow

`finite sampled source values → FE/minimum-phase clock covariance → source-clock extinction
  → canonical left-branch covariance → Ward cancellation → RH`.

The positive survivor is sharp: an HB producer must use frequency derivatives, an infinite
uniqueness set, an external time-bilocal phase reference, or a source-derived global
minimum-phase/winding law.
-/

open Complex Real Polynomial
open scoped BigOperators

noncomputable section

namespace RHTower

def finiteAnchorPolynomial (s : Finset ℝ) : Polynomial ℝ :=
  ∏ a ∈ s, (X - C a)

theorem laguerreL1_finiteAnchorPolynomial_pos
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    0 < (laguerreL1 (finiteAnchorPolynomial s)).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hsempty : s = ∅
      · subst s
        change 0 < (laguerreL1 ((X - C a) * 1)).eval x
        rw [laguerreL1_linear_mul]
        simp [laguerreL1]
      · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsempty
        have ihx := ih hsne
        rw [finiteAnchorPolynomial, Finset.prod_insert ha,
          laguerreL1_linear_mul, eval_add, eval_pow, eval_mul, eval_pow]
        by_cases hq : (∏ b ∈ s, (X - C b)).eval x = 0
        · have hprod : ∏ b ∈ s, (x - b) = 0 := by
            rw [Polynomial.eval_prod] at hq
            simpa using hq
          obtain ⟨b, hb, hxb⟩ := Finset.prod_eq_zero_iff.mp hprod
          have hxa : x - a ≠ 0 := by
            intro hzero
            have hxeqa : x = a := sub_eq_zero.mp hzero
            have hxeqb : x = b := sub_eq_zero.mp hxb
            have hab : a = b := hxeqa.symm.trans hxeqb
            exact ha (by simpa [hab] using hb)
          have hsq : 0 < ((X - C a).eval x) ^ 2 := by
            simpa using sq_pos_of_ne_zero hxa
          exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hsq ihx)
        · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hq)
            (mul_nonneg (sq_nonneg _) ihx.le)

def finiteAnchorAllPassNumerator (s : Finset ℝ) : ℂ → ℂ :=
  -(evalRealPolynomial (finiteAnchorPolynomial s) -
    (fun _ : ℂ => I) * evalRealPolynomial (derivative (finiteAnchorPolynomial s)))

def finiteAnchorAllPassDenominator (s : Finset ℝ) : ℂ → ℂ :=
  evalRealPolynomial (finiteAnchorPolynomial s) +
    (fun _ : ℂ => I) * evalRealPolynomial (derivative (finiteAnchorPolynomial s))

def finiteAnchorAllPass (s : Finset ℝ) : ℂ → ℂ :=
  finiteAnchorAllPassNumerator s / finiteAnchorAllPassDenominator s

theorem finiteAnchorAllPass_den_ne_zero
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    evalRealPolynomial (finiteAnchorPolynomial s) (x : ℂ) +
        I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) (x : ℂ) ≠ 0 := by
  intro hzero
  rw [evalRealPolynomial_ofReal, evalRealPolynomial_ofReal] at hzero
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  norm_num at hre him
  have hpos := laguerreL1_finiteAnchorPolynomial_pos s hs x
  unfold laguerreL1 at hpos
  rw [eval_sub, eval_pow, eval_mul] at hpos
  rw [hre, him] at hpos
  norm_num at hpos

theorem norm_finiteAnchorAllPass
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    ‖finiteAnchorAllPass s (x : ℂ)‖ = 1 := by
  change ‖-(evalRealPolynomial (finiteAnchorPolynomial s) (x : ℂ) -
      I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) (x : ℂ)) /
    (evalRealPolynomial (finiteAnchorPolynomial s) (x : ℂ) +
      I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) (x : ℂ))‖ = 1
  rw [norm_div, norm_neg]
  have hconj :
      evalRealPolynomial (finiteAnchorPolynomial s) (x : ℂ) -
          I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) (x : ℂ) =
        star (evalRealPolynomial (finiteAnchorPolynomial s) (x : ℂ) +
          I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) (x : ℂ)) := by
    rw [evalRealPolynomial_ofReal, evalRealPolynomial_ofReal]
    simp
    ring
  rw [hconj, norm_star, div_self]
  exact norm_ne_zero_iff.mpr (finiteAnchorAllPass_den_ne_zero s hs x)

theorem finiteAnchorPolynomial_eval_eq_zero_iff
    (s : Finset ℝ) (x : ℝ) :
    (finiteAnchorPolynomial s).eval x = 0 ↔ x ∈ s := by
  classical
  rw [finiteAnchorPolynomial, Polynomial.eval_prod]
  constructor
  · intro h
    obtain ⟨a, ha, hxa⟩ := Finset.prod_eq_zero_iff.mp h
    have hxa' : x - a = 0 := by simpa using hxa
    exact (sub_eq_zero.mp hxa') ▸ ha
  · intro hx
    exact Finset.prod_eq_zero hx (by simp)

theorem finiteAnchorAllPass_eq_one_iff
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    finiteAnchorAllPass s (x : ℂ) = 1 ↔ x ∈ s := by
  rw [← finiteAnchorPolynomial_eval_eq_zero_iff]
  let P : ℂ := evalRealPolynomial (finiteAnchorPolynomial s) (x : ℂ)
  let Q : ℂ := evalRealPolynomial (derivative (finiteAnchorPolynomial s)) (x : ℂ)
  have hden : P + I * Q ≠ 0 := finiteAnchorAllPass_den_ne_zero s hs x
  change -(P - I * Q) / (P + I * Q) = 1 ↔ _
  rw [div_eq_iff hden]
  constructor
  · intro h
    have hP : P = 0 := by
      have hP2 : (2 : ℂ) * P = 0 := by linear_combination -h
      exact (mul_eq_zero.mp hP2).resolve_left (by norm_num)
    simpa [P, evalRealPolynomial_ofReal] using hP
  · intro h
    have hP : P = 0 := by simpa [P, evalRealPolynomial_ofReal] using h
    rw [hP]
    ring

@[simp] theorem evalRealPolynomial_add_local
    (p q : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial (p + q) z =
      evalRealPolynomial p z + evalRealPolynomial q z := by
  simp [evalRealPolynomial]

@[simp] theorem evalRealPolynomial_X_sub_C_real
    (a : ℝ) (z : ℂ) :
    evalRealPolynomial (X - C a) z = z - (a : ℂ) := by
  simp [evalRealPolynomial]

theorem finiteAnchorPolynomial_insert
    {s : Finset ℝ} {a : ℝ} (ha : a ∉ s) :
    finiteAnchorPolynomial (insert a s) =
      (X - C a) * finiteAnchorPolynomial s := by
  simp [finiteAnchorPolynomial, ha]

theorem finiteAnchorPolynomial_derivative_eval_eq_mul_sum
    (s : Finset ℝ) (z : ℂ)
    (hz : ∀ a ∈ s, z - (a : ℂ) ≠ 0) :
    evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z =
      evalRealPolynomial (finiteAnchorPolynomial s) z *
        ∑ a ∈ s, (z - (a : ℂ))⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteAnchorPolynomial, evalRealPolynomial]
  | @insert a s ha ih =>
      have hza : z - (a : ℂ) ≠ 0 := hz a (Finset.mem_insert_self a s)
      have hzs : ∀ b ∈ s, z - (b : ℂ) ≠ 0 :=
        fun b hb => hz b (Finset.mem_insert_of_mem hb)
      have ih' := ih hzs
      have hlin : derivative (X - C a) = (1 : Polynomial ℝ) := by simp
      rw [finiteAnchorPolynomial_insert ha, Polynomial.derivative_mul,
        hlin, one_mul, evalRealPolynomial_add_local]
      simp only [evalRealPolynomial_mul, evalRealPolynomial_X_sub_C_real]
      rw [ih', Finset.sum_insert ha]
      field_simp

theorem evalRealPolynomial_finiteAnchorPolynomial
    (s : Finset ℝ) (z : ℂ) :
    evalRealPolynomial (finiteAnchorPolynomial s) z =
      ∏ a ∈ s, (z - (a : ℂ)) := by
  classical
  simp [finiteAnchorPolynomial, evalRealPolynomial]

theorem im_inv_sub_real_lt_zero
    {z : ℂ} (hz : 0 < z.im) (a : ℝ) :
    ((z - (a : ℂ))⁻¹).im < 0 := by
  rw [Complex.inv_im]
  have hne : z - (a : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have hnorm : 0 < Complex.normSq (z - (a : ℂ)) :=
    Complex.normSq_pos.mpr hne
  have hnum : -z.im < 0 := neg_lt_zero.mpr hz
  simpa using div_neg_of_neg_of_pos hnum hnorm

theorem im_sum_inv_sub_real_lt_zero
    (s : Finset ℝ) (hs : s.Nonempty) {z : ℂ} (hz : 0 < z.im) :
    (∑ a ∈ s, (z - (a : ℂ))⁻¹).im < 0 := by
  have himsum :
      (∑ a ∈ s, (z - (a : ℂ))⁻¹).im =
        ∑ a ∈ s, ((z - (a : ℂ))⁻¹).im := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha]
  rw [himsum]
  exact Finset.sum_neg (fun a ha => im_inv_sub_real_lt_zero hz a) hs

theorem finiteAnchorAllPass_den_ne_zero_upper
    (s : Finset ℝ) (hs : s.Nonempty) {z : ℂ} (hz : 0 < z.im) :
    evalRealPolynomial (finiteAnchorPolynomial s) z +
        I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z ≠ 0 := by
  have hroot : ∀ a ∈ s, z - (a : ℂ) ≠ 0 := by
    intro a ha h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have hP : evalRealPolynomial (finiteAnchorPolynomial s) z ≠ 0 := by
    rw [evalRealPolynomial_finiteAnchorPolynomial]
    exact Finset.prod_ne_zero_iff.mpr hroot
  intro hden
  have hder := finiteAnchorPolynomial_derivative_eval_eq_mul_sum s z hroot
  have hID : I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z =
      -evalRealPolynomial (finiteAnchorPolynomial s) z := by
    linear_combination hden
  have hD : evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z =
      I * evalRealPolynomial (finiteAnchorPolynomial s) z := by
    calc
      evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z =
          -I * (I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z) := by
            rw [← mul_assoc, neg_mul, I_mul_I]
            simp
      _ = -I * (-evalRealPolynomial (finiteAnchorPolynomial s) z) := by rw [hID]
      _ = I * evalRealPolynomial (finiteAnchorPolynomial s) z := by ring
  have hratio : ∑ a ∈ s, (z - (a : ℂ))⁻¹ = I := by
    apply (mul_left_cancel₀ hP)
    rw [← hder]
    rw [hD]
    ring
  have himneg := im_sum_inv_sub_real_lt_zero s hs hz
  rw [hratio] at himneg
  norm_num at himneg

def finiteAnchorAllPassClock (s : Finset ℝ) (x : ℝ) : ℝ :=
  (logDeriv (finiteAnchorAllPass s) (x : ℂ)).im

theorem rationalAllPass_logDerivative_im (p q r : ℝ)
    (h : p ^ 2 + q ^ 2 ≠ 0) :
    ((((-(q : ℂ) + I * (r : ℂ)) * ((p : ℂ) + I * (q : ℂ)) -
        (-((p : ℂ) - I * (q : ℂ))) * ((q : ℂ) + I * (r : ℂ))) /
          ((p : ℂ) + I * (q : ℂ)) ^ 2) /
      (-((p : ℂ) - I * (q : ℂ)) /
        ((p : ℂ) + I * (q : ℂ)))).im =
      2 * (q ^ 2 - p * r) / (p ^ 2 + q ^ 2) := by
  have hden : (p : ℂ) + I * (q : ℂ) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    norm_num at hre him
    apply h
    rw [hre, him]
    norm_num
  have hnum : (p : ℂ) - I * (q : ℂ) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    norm_num at hre him
    apply h
    rw [hre, him]
    norm_num
  have hsumC : (p : ℂ) ^ 2 + (q : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast h
  have hprod :
      ((p : ℂ) + (q : ℂ) * I) * ((p : ℂ) - (q : ℂ) * I) =
        (p : ℂ) ^ 2 + (q : ℂ) ^ 2 := by
    apply Complex.ext <;> norm_num [pow_two] <;> ring
  have heq :
      (((-(q : ℂ) + I * (r : ℂ)) * ((p : ℂ) + I * (q : ℂ)) -
        (-((p : ℂ) - I * (q : ℂ))) * ((q : ℂ) + I * (r : ℂ))) /
          ((p : ℂ) + I * (q : ℂ)) ^ 2) /
      (-((p : ℂ) - I * (q : ℂ)) /
        ((p : ℂ) + I * (q : ℂ))) =
        (2 : ℂ) * I * ((q : ℂ) ^ 2 - (p : ℂ) * (r : ℂ)) /
          ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) := by
    field_simp [hden, hnum, hsumC]
    rw [hprod]
    field_simp [hsumC]
    apply Complex.ext <;> norm_num [pow_two] <;> ring
  have hcast :
      (2 : ℂ) * I * ((q : ℂ) ^ 2 - (p : ℂ) * (r : ℂ)) /
          ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) =
        ((2 * (q ^ 2 - p * r) / (p ^ 2 + q ^ 2) : ℝ) : ℂ) * I := by
    push_cast
    field_simp [h, hsumC]
  calc
    _ = (((2 * (q ^ 2 - p * r) / (p ^ 2 + q ^ 2) : ℝ) : ℂ) * I).im :=
      congrArg Complex.im (heq.trans hcast)
    _ = 2 * (q ^ 2 - p * r) / (p ^ 2 + q ^ 2) := by
      rw [Complex.mul_im]
      norm_num only [ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul, sub_zero,
        add_zero]

theorem hasDerivAt_finiteAnchorAllPass
    (s : Finset ℝ) {z : ℂ}
    (hden : evalRealPolynomial (finiteAnchorPolynomial s) z +
      I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z ≠ 0) :
    HasDerivAt (finiteAnchorAllPass s)
      ((-(evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z -
          I * evalRealPolynomial (derivative (derivative (finiteAnchorPolynomial s))) z) *
          (evalRealPolynomial (finiteAnchorPolynomial s) z +
            I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z) -
        (-(evalRealPolynomial (finiteAnchorPolynomial s) z -
          I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z)) *
          (evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z +
            I * evalRealPolynomial (derivative (derivative (finiteAnchorPolynomial s))) z)) /
        (evalRealPolynomial (finiteAnchorPolynomial s) z +
          I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z) ^ 2) z := by
  have hP := hasDerivAt_evalRealPolynomial (finiteAnchorPolynomial s) z
  have hQ := hasDerivAt_evalRealPolynomial (derivative (finiteAnchorPolynomial s)) z
  have hnum := (hP.sub ((hasDerivAt_const z I).mul hQ)).neg
  have hden' := hP.add ((hasDerivAt_const z I).mul hQ)
  simpa [finiteAnchorAllPass, finiteAnchorAllPassNumerator,
    finiteAnchorAllPassDenominator] using hnum.div hden' hden

theorem finiteAnchorAllPassClock_eq_laguerre
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    finiteAnchorAllPassClock s x =
      2 * (laguerreL1 (finiteAnchorPolynomial s)).eval x /
        ((finiteAnchorPolynomial s).eval x ^ 2 +
          (derivative (finiteAnchorPolynomial s)).eval x ^ 2) := by
  let p : ℝ := (finiteAnchorPolynomial s).eval x
  let q : ℝ := (derivative (finiteAnchorPolynomial s)).eval x
  let r : ℝ := (derivative (derivative (finiteAnchorPolynomial s))).eval x
  have hden := finiteAnchorAllPass_den_ne_zero s hs x
  have hsq : p ^ 2 + q ^ 2 ≠ 0 := by
    intro hzero
    have hp : p = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq : q = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    apply hden
    simp [p, q, evalRealPolynomial_ofReal, hp, hq]
  have hA := hasDerivAt_finiteAnchorAllPass s hden
  unfold finiteAnchorAllPassClock
  rw [logDeriv_apply, hA.deriv]
  have h := rationalAllPass_logDerivative_im p q r hsq
  simp [finiteAnchorAllPass, finiteAnchorAllPassNumerator,
    finiteAnchorAllPassDenominator, evalRealPolynomial_ofReal, laguerreL1,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul, p, q, r] at h ⊢
  convert h using 1 <;> ring

theorem finiteAnchorAllPassClock_pos
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    0 < finiteAnchorAllPassClock s x := by
  rw [finiteAnchorAllPassClock_eq_laguerre s hs x]
  apply div_pos
  · exact mul_pos (by norm_num) (laguerreL1_finiteAnchorPolynomial_pos s hs x)
  · have hden := finiteAnchorAllPass_den_ne_zero s hs x
    have hne : (finiteAnchorPolynomial s).eval x ^ 2 +
        (derivative (finiteAnchorPolynomial s)).eval x ^ 2 ≠ 0 := by
      intro hzero
      have hp : (finiteAnchorPolynomial s).eval x = 0 := by
        nlinarith [sq_nonneg ((finiteAnchorPolynomial s).eval x),
          sq_nonneg ((derivative (finiteAnchorPolynomial s)).eval x)]
      have hq : (derivative (finiteAnchorPolynomial s)).eval x = 0 := by
        nlinarith [sq_nonneg ((finiteAnchorPolynomial s).eval x),
          sq_nonneg ((derivative (finiteAnchorPolynomial s)).eval x)]
      apply hden
      simp [evalRealPolynomial_ofReal, hp, hq]
    exact lt_of_le_of_ne
      (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hne)

def finiteAnchorNegSchwarzReflect (s : Finset ℝ) : ℂ → ℂ :=
  (starRingEnd ℂ) ∘ (finiteAnchorAllPass s ∘ Neg.neg) ∘ (starRingEnd ℂ)

def finiteAnchorSchwarzAllPass (s : Finset ℝ) : ℂ → ℂ :=
  finiteAnchorAllPass s * finiteAnchorNegSchwarzReflect s

def finiteAnchorSchwarzAllPassClock (s : Finset ℝ) (x : ℝ) : ℝ :=
  (logDeriv (finiteAnchorSchwarzAllPass s) (x : ℂ)).im

theorem hasDerivAt_finiteAnchorNegSchwarzReflect
    (s : Finset ℝ) {z : ℂ}
    (hden : evalRealPolynomial (finiteAnchorPolynomial s) (-star z) +
      I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) (-star z) ≠ 0) :
    HasDerivAt (finiteAnchorNegSchwarzReflect s)
      (star (-(deriv (finiteAnchorAllPass s) (-star z)))) z := by
  have hH := hasDerivAt_finiteAnchorAllPass s hden
  have hneg := hH.comp (star z) (hasDerivAt_neg (star z))
  rw [← hH.deriv] at hneg
  have h := hneg.conj_conj
  simpa [finiteAnchorNegSchwarzReflect, Function.comp_def] using h

theorem finiteAnchorSchwarzAllPass_neg_star (s : Finset ℝ) (z : ℂ) :
    finiteAnchorSchwarzAllPass s (-star z) =
      star (finiteAnchorSchwarzAllPass s z) := by
  simp [finiteAnchorSchwarzAllPass, finiteAnchorNegSchwarzReflect,
    Function.comp_def, mul_comm]

theorem norm_finiteAnchorSchwarzAllPass
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    ‖finiteAnchorSchwarzAllPass s (x : ℂ)‖ = 1 := by
  change ‖finiteAnchorAllPass s (x : ℂ) *
    star (finiteAnchorAllPass s (-star (x : ℂ)))‖ = 1
  rw [norm_mul, norm_star, norm_finiteAnchorAllPass s hs x]
  have hneg : -star (x : ℂ) = ((-x : ℝ) : ℂ) := by norm_num
  rw [hneg, norm_finiteAnchorAllPass s hs (-x)]
  norm_num

theorem finiteAnchorSchwarzAllPass_eq_one_of_mem
    (s : Finset ℝ) (hs : s.Nonempty)
    (hsym : ∀ x ∈ s, -x ∈ s) {x : ℝ} (hx : x ∈ s) :
    finiteAnchorSchwarzAllPass s (x : ℂ) = 1 := by
  have hx1 := (finiteAnchorAllPass_eq_one_iff s hs x).2 hx
  have hneg1 := (finiteAnchorAllPass_eq_one_iff s hs (-x)).2 (hsym x hx)
  change finiteAnchorAllPass s (x : ℂ) *
    star (finiteAnchorAllPass s (-star (x : ℂ))) = 1
  rw [hx1]
  have hneg : -star (x : ℂ) = ((-x : ℝ) : ℂ) := by norm_num
  rw [hneg, hneg1]
  norm_num

theorem differentiableOn_finiteAnchorSchwarzAllPass_upper
    (s : Finset ℝ) (hs : s.Nonempty) :
    DifferentiableOn ℂ (finiteAnchorSchwarzAllPass s) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz' : 0 < (-star z).im := by simpa using hz
  have hden := finiteAnchorAllPass_den_ne_zero_upper s hs hz
  have hden' := finiteAnchorAllPass_den_ne_zero_upper s hs hz'
  exact ((hasDerivAt_finiteAnchorAllPass s hden).mul
    (hasDerivAt_finiteAnchorNegSchwarzReflect s hden')).differentiableAt.differentiableWithinAt

theorem finiteAnchorNegSchwarzReflect_apply_real
    (s : Finset ℝ) (x : ℝ) :
    finiteAnchorNegSchwarzReflect s (x : ℂ) =
      star (finiteAnchorAllPass s ((-x : ℝ) : ℂ)) := by
  simp [finiteAnchorNegSchwarzReflect, Function.comp_def]

theorem logDeriv_finiteAnchorNegSchwarzReflect_real
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    logDeriv (finiteAnchorNegSchwarzReflect s) (x : ℂ) =
      -star (logDeriv (finiteAnchorAllPass s) ((-x : ℝ) : ℂ)) := by
  have hdenH := finiteAnchorAllPass_den_ne_zero s hs (-x)
  have hneg : -star (x : ℂ) = ((-x : ℝ) : ℂ) := by norm_num
  have hdenK : evalRealPolynomial (finiteAnchorPolynomial s) (-star (x : ℂ)) +
      I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) (-star (x : ℂ)) ≠ 0 := by
    simpa [hneg] using hdenH
  have hK := hasDerivAt_finiteAnchorNegSchwarzReflect s hdenK
  rw [logDeriv_apply, hK.deriv, logDeriv_apply,
    finiteAnchorNegSchwarzReflect_apply_real]
  rw [hneg]
  simp
  ring

theorem finiteAnchorSchwarzAllPassClock_eq_add
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    finiteAnchorSchwarzAllPassClock s x =
      finiteAnchorAllPassClock s x + finiteAnchorAllPassClock s (-x) := by
  have hnormH := norm_finiteAnchorAllPass s hs x
  have hHne : finiteAnchorAllPass s (x : ℂ) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hnormH]
    norm_num
  have hnormK : ‖finiteAnchorNegSchwarzReflect s (x : ℂ)‖ = 1 := by
    rw [finiteAnchorNegSchwarzReflect_apply_real, norm_star,
      norm_finiteAnchorAllPass s hs (-x)]
  have hKne : finiteAnchorNegSchwarzReflect s (x : ℂ) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hnormK]
    norm_num
  have hdenH := finiteAnchorAllPass_den_ne_zero s hs x
  have hneg : -star (x : ℂ) = ((-x : ℝ) : ℂ) := by norm_num
  have hdenK0 := finiteAnchorAllPass_den_ne_zero s hs (-x)
  have hdenK : evalRealPolynomial (finiteAnchorPolynomial s) (-star (x : ℂ)) +
      I * evalRealPolynomial (derivative (finiteAnchorPolynomial s)) (-star (x : ℂ)) ≠ 0 := by
    simpa [hneg] using hdenK0
  have hdiffH := (hasDerivAt_finiteAnchorAllPass s hdenH).differentiableAt
  have hdiffK := (hasDerivAt_finiteAnchorNegSchwarzReflect s hdenK).differentiableAt
  have hmul := logDeriv_mul (x := (x : ℂ)) hHne hKne hdiffH hdiffK
  have himul := congrArg Complex.im hmul
  rw [logDeriv_finiteAnchorNegSchwarzReflect_real s hs x] at himul
  have hfun : finiteAnchorSchwarzAllPass s =
      (fun z => finiteAnchorAllPass s z * finiteAnchorNegSchwarzReflect s z) := by
    funext z
    rfl
  rw [finiteAnchorSchwarzAllPassClock, hfun]
  simpa [finiteAnchorAllPassClock] using himul

theorem finiteAnchorSchwarzAllPassClock_pos
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    0 < finiteAnchorSchwarzAllPassClock s x := by
  rw [finiteAnchorSchwarzAllPassClock_eq_add s hs x]
  exact add_pos (finiteAnchorAllPassClock_pos s hs x)
    (finiteAnchorAllPassClock_pos s hs (-x))

theorem finiteAnchorSchwarzAllPass_ne_one
    (s : Finset ℝ) (hs : s.Nonempty) :
    finiteAnchorSchwarzAllPass s ≠ (fun _ : ℂ => 1) := by
  intro hone
  have hpos := finiteAnchorSchwarzAllPassClock_pos s hs 0
  rw [finiteAnchorSchwarzAllPassClock, hone] at hpos
  simp [logDeriv_apply] at hpos

/-- Finite value-only all-pass identifiability asserted by the killed HB producer class. -/
def HBFiniteCrossFrequencyValueAllPassUnique (s : Finset ℝ) : Prop :=
  ∀ A : ℂ → ℂ,
    DifferentiableOn ℂ A {z : ℂ | 0 < z.im} →
    (∀ x : ℝ, ‖A (x : ℂ)‖ = 1) →
    (∀ z : ℂ, A (-star z) = star (A z)) →
    (∀ x : ℝ, x ∈ s → A (x : ℂ) = 1) →
    A = (fun _ : ℂ => 1)

/-- Strong positive obstruction: a causal Schwarz-real, positive-clock all-pass witness invisible
at every finite symmetric sample. -/
theorem exists_finiteAnchorSchwarzCausalAllPass_sampleBlind
    (s : Finset ℝ) (hs : s.Nonempty) (hsym : ∀ x ∈ s, -x ∈ s) :
    ∃ A : ℂ → ℂ,
      DifferentiableOn ℂ A {z : ℂ | 0 < z.im} ∧
      (∀ x : ℝ, ‖A (x : ℂ)‖ = 1) ∧
      (∀ z : ℂ, A (-star z) = star (A z)) ∧
      (∀ x : ℝ, x ∈ s → A (x : ℂ) = 1) ∧
      (∀ x : ℝ, 0 < (logDeriv A (x : ℂ)).im) ∧
      A ≠ (fun _ : ℂ => 1) := by
  refine ⟨finiteAnchorSchwarzAllPass s,
    differentiableOn_finiteAnchorSchwarzAllPass_upper s hs,
    norm_finiteAnchorSchwarzAllPass s hs,
    finiteAnchorSchwarzAllPass_neg_star s, ?_, ?_,
    finiteAnchorSchwarzAllPass_ne_one s hs⟩
  · exact fun x hx => finiteAnchorSchwarzAllPass_eq_one_of_mem s hs hsym hx
  · exact finiteAnchorSchwarzAllPassClock_pos s hs

/-- No nonempty symmetric finite sample set identifies causal Schwarz all-pass phase. -/
theorem not_hbFiniteCrossFrequencyValueAllPassUnique
    (s : Finset ℝ) (hs : s.Nonempty) (hsym : ∀ x ∈ s, -x ∈ s) :
    ¬ HBFiniteCrossFrequencyValueAllPassUnique s := by
  obtain ⟨A, hcausal, hallpass, hschwarz, hsamples, hclock, hne⟩ :=
    exists_finiteAnchorSchwarzCausalAllPass_sampleBlind s hs hsym
  intro hunique
  exact hne (hunique A hcausal hallpass hschwarz hsamples)


end RHTower
