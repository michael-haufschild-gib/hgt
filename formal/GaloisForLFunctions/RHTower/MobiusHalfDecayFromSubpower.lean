import GaloisForLFunctions.RHTower.MixedConvolutionSubpowerAbelBound
import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier

/-!
# A subpower coefficient bound gives the half-power source decay

The corpus carries the `O(x^{-1/2})` decay of the Möbius--Laplace source as a packaged proposition
`MobiusDiscreteLaplaceHalfDecay`, and derives from it the analyticity of the Mellin transform on the
right half-plane.  The radial bound of `MixedConvolutionSubpowerAbelBound` discharges that
proposition from a bound on the Hermitian mixed convolution coefficients alone: if

```
Re R_k(N) ≤ C (N+1)^α    with   α + 1 ≤ k,
```

then `‖A(x)‖ ≤ C' x^{-(α+1)/(2k)} ≤ C' x^{-1/2}` for `0 < x < 1`, because the exponent
`(α+1)/(2k)` is at most `1/2` and `1/x ≥ 1`.

The packaged hypothesis is thereby replaced by an explicit coefficient condition.
-/

open Complex
open scoped BigOperators

namespace RHTower

/-- The Möbius coefficients as a complex sequence. -/
def mobiusCoeff : ℕ → ℂ := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)

theorem norm_mobiusCoeff_le_one (n : ℕ) : ‖mobiusCoeff n‖ ≤ 1 := by
  rw [mobiusCoeff, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- The Laplace term is the Möbius coefficient against the `n`-th power of the radius `e^{-x}`. -/
theorem mobiusDiscreteLaplaceTerm_eq_coeff_mul_pow (x : ℝ) (n : ℕ) :
    mobiusDiscreteLaplaceTerm x n = mobiusCoeff n * ((Real.exp (-x) : ℝ) : ℂ) ^ n := by
  rw [mobiusDiscreteLaplaceTerm, mobiusCoeff, ← Complex.ofReal_pow, exp_neg_pow,
    Complex.ofReal_exp]
  push_cast
  ring

theorem mobiusDiscreteLaplaceTransform_eq_tsum (x : ℝ) :
    mobiusDiscreteLaplaceTransform x =
      ∑' n : ℕ, mobiusCoeff n * ((Real.exp (-x) : ℝ) : ℂ) ^ n := by
  rw [mobiusDiscreteLaplaceTransform]
  exact tsum_congr (mobiusDiscreteLaplaceTerm_eq_coeff_mul_pow x)

theorem summable_norm_mobiusCoeff_mul_pow {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => ‖mobiusCoeff n * ((Real.exp (-x) : ℝ) : ℂ) ^ n‖ := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one hr0 hr1)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hpow : (0 : ℝ) ≤ Real.exp (-x) ^ n := pow_nonneg hr0 n
  simpa using mul_le_mul_of_nonneg_right (norm_mobiusCoeff_le_one n) hpow

/-- **The packaged half-power decay follows from a subpower coefficient bound.**  The exponent
condition `α + 1 ≤ k` is exactly what makes the radial exponent `(α+1)/(2k)` at most `1/2`. -/
theorem mobiusDiscreteLaplaceHalfDecay_of_subpower
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (hαk : α + 1 ≤ (k : ℝ))
    (hupper : ∀ N : ℕ,
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re ≤ C * ((N : ℝ) + 1) ^ α) :
    MobiusDiscreteLaplaceHalfDecay := by
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hAbel : 0 ≤ mixedSubpowerAbelConstant α := mixedSubpowerAbelConstant_nonneg hα
  refine ⟨(C * mixedSubpowerAbelConstant α) ^ ((2 * (k : ℝ))⁻¹), 1, ?_, one_pos, ?_⟩
  · exact Real.rpow_nonneg (mul_nonneg hC hAbel) _
  · intro x hx hx1
    have hxle : x ≤ 1 := hx1.le
    have hbound := norm_tsum_le_of_mixedAdditiveConvolutionPower_subpower
      hk hα hC hx hxle (summable_norm_mobiusCoeff_mul_pow hx) hupper
    rw [mobiusDiscreteLaplaceTransform_eq_tsum]
    refine hbound.trans ?_
    have hone : (1 : ℝ) ≤ 1 / x := (one_le_div hx).2 hxle
    have hexp : (α + 1) / (2 * (k : ℝ)) ≤ 1 / 2 := by
      have h2k : (0 : ℝ) < 2 * (k : ℝ) := by linarith
      rw [div_le_iff₀ h2k]
      linarith
    have hmono : (1 / x) ^ ((α + 1) / (2 * (k : ℝ))) ≤ (1 / x) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hone hexp
    have hrewrite : (1 / x) ^ ((1 : ℝ) / 2) = x ^ (-(1 / 2 : ℝ)) := by
      rw [one_div x, ← Real.rpow_neg_one x, ← Real.rpow_mul hx.le]
      congr 1
      ring
    rw [← hrewrite]
    exact mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg (mul_nonneg hC hAbel) _)

end RHTower
