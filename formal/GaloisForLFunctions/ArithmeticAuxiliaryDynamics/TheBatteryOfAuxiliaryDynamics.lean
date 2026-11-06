import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheForcedJumpsOfAProducer
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.CurvesCalibrateThePrecisionExponent

/-!
# The battery of auxiliary dynamics

The field must obey two tests on fakes, and both can be stated exactly.

* **The golden fake obeys transport and fails construction.** Its `L`-function
  `1 − 5·5^{-s} + 5·5^{-2s}` is periodic in `Im s`, so every zero returns exactly, along a full arithmetic
  progression of shifts. It has a zero with `½ < Re s < 1`, and it fails the square-root count. So
  transport alone proves nothing about purity.
* **A continuous count fails construction by construction.** Replacing `⌊r/k⌋` by `r/k` makes the
  multiplicity of every balanced stencil vanish identically. All multiplicity lives in the
  fractional parts, so a statement proved through multiplicity is false for continuous systems.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The golden `L`-function: `P(5^{-s})` for `P(X) = 1 − 5X + 5X²`. -/
def goldenL (s : ℂ) : ℂ := 1 - 5 * ((5 : ℝ) : ℂ) ^ (-s) + 5 * (((5 : ℝ) : ℂ) ^ (-s)) ^ 2

/-- The vertical period of the golden `L`-function. -/
def goldenPeriod : ℝ := 2 * Real.pi / Real.log 5

private lemma log5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)

/-- A vertical shift by a multiple of the period leaves `5^{-s}` fixed. -/
theorem cpow_shift (s : ℂ) (k : ℤ) :
    ((5 : ℝ) : ℂ) ^ (-(s + (k : ℂ) * (goldenPeriod : ℂ) * I)) = ((5 : ℝ) : ℂ) ^ (-s) := by
  have h5 : ((5 : ℝ) : ℂ) ≠ 0 := by norm_num
  have hlog : Complex.log ((5 : ℝ) : ℂ) = (Real.log 5 : ℂ) :=
    (Complex.ofReal_log (by norm_num)).symm
  have hne : (Real.log 5 : ℂ) ≠ 0 := by exact_mod_cast log5_pos.ne'
  rw [Complex.cpow_def_of_ne_zero h5, Complex.cpow_def_of_ne_zero h5, hlog]
  have hsplit : (Real.log 5 : ℂ) * -(s + (k : ℂ) * (goldenPeriod : ℂ) * I) =
      (Real.log 5 : ℂ) * -s + ((-k : ℤ) : ℂ) * (2 * Real.pi * I) := by
    rw [goldenPeriod]
    push_cast
    field_simp
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The golden fake obeys transport.** Every vertical shift by a multiple of the period is an exact
return, at every point. -/
theorem goldenL_shift (s : ℂ) (k : ℤ) :
    goldenL (s + (k : ℂ) * (goldenPeriod : ℂ) * I) = goldenL s := by
  rw [goldenL, goldenL, cpow_shift]

/-- The real part of the deep golden zero. -/
def goldenDeepZero : ℝ := -Real.log ((5 - √5) / 10) / Real.log 5

private lemma sqrt5_bounds : (2 : ℝ) < √5 ∧ √5 < 3 := by
  constructor
  · refine Real.lt_sqrt_of_sq_lt ?_
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- **The golden fake has a zero right of the line.** -/
theorem goldenL_deepZero :
    goldenL (goldenDeepZero : ℂ) = 0 ∧ 1 / 2 < goldenDeepZero ∧ goldenDeepZero < 1 := by
  obtain ⟨h2, h3⟩ := sqrt5_bounds
  have hlog := log5_pos
  have hX0 : 0 < (5 - √5) / 10 := by linarith
  have hsq : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hval : (5 : ℝ) ^ (-goldenDeepZero) = (5 - √5) / 10 := by
    rw [goldenDeepZero, neg_div, neg_neg, Real.rpow_def_of_pos (by norm_num),
      mul_div_cancel₀ _ hlog.ne', Real.exp_log hX0]
  refine ⟨?_, ?_, ?_⟩
  · have hc : ((5 : ℝ) : ℂ) ^ (-(goldenDeepZero : ℂ)) = (((5 - √5) / 10 : ℝ) : ℂ) := by
      rw [← hval, Complex.ofReal_cpow (by norm_num)]
      push_cast
      rfl
    rw [goldenL, hc]
    have hreal : (1 : ℝ) - 5 * ((5 - √5) / 10) + 5 * ((5 - √5) / 10) ^ 2 = 0 := by
      nlinarith
    have := congrArg (fun x : ℝ => (x : ℂ)) hreal
    simpa using this
  · -- `X < 5^{-1/2}`, that is `X² < 1/5`.
    rw [goldenDeepZero, lt_div_iff₀ hlog]
    have hX : Real.log ((5 - √5) / 10) < -(1 / 2 * Real.log 5) := by
      have h1 : (-(1 / 2 * Real.log 5)) = Real.log (Real.exp (-(1 / 2 * Real.log 5))) :=
        (Real.log_exp _).symm
      rw [h1]
      refine Real.log_lt_log hX0 ?_
      have hexp : Real.exp (-(1 / 2 * Real.log 5)) = 1 / √5 := by
        rw [Real.exp_neg, one_div]
        congr 1
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num)]
        congr 1
        ring
      rw [hexp, lt_div_iff₀ (by linarith)]
      nlinarith
    linarith
  · -- `X > 1/5`.
    rw [goldenDeepZero, div_lt_one hlog]
    have hX : Real.log (1 / 5) < Real.log ((5 - √5) / 10) :=
      Real.log_lt_log (by norm_num) (by linarith)
    rw [one_div, Real.log_inv] at hX
    linarith

/-- **The golden fake fails construction.** It fails the square-root count. -/
theorem golden_fails_count :
    ¬ ArithmeticOfSquareRootPrecision.CountAtPrecision
      ArithmeticCastelnuovoSeveri.goldenDatum (1 / 2) :=
  ArithmeticOfSquareRootPrecision.golden_not_countAtPrecision_half

/-- **A continuous count has no multiplicity.** Replacing `⌊r/k⌋` by `r/k`, every balanced stencil
has multiplicity zero. -/
theorem continuous_multiplicity_eq_zero {c : ℕ →₀ ℤ}
    (hbal : ArithmeticKreinLangerTheory.IsBalanced c) (x : ℝ) :
    ∑ k ∈ c.support, (c k : ℝ) * (x / k) = 0 := by
  have h : ∑ k ∈ c.support, (c k : ℝ) * (x / k) = x * ∑ k ∈ c.support, (c k : ℝ) / k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h, show ∑ k ∈ c.support, (c k : ℝ) / k = 0 from hbal, mul_zero]

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
