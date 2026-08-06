import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.RHTower.PrimeZetaLogAsymptotic
import Mathlib.NumberTheory.AbelSummation

/-!
# The Abel representation of the prime zeta function

For `δ > 0` improper Abel summation of `∑_p p^(-1-δ)` against the prime reciprocal sum gives

```text
P(1 + δ) = δ ∫_1^∞ t^(-δ-1) (∑_{p ≤ t} 1/p) dt.
```

The two inputs are the elementary bound `∑_{p ≤ N} 1/p ≤ (log N + C)/log 2`, obtained from
Mertens' first theorem alone, and the decay `N^(-δ) log N → 0`.
-/

open Filter Topology MeasureTheory Set Asymptotics
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## An elementary bound on the prime reciprocal sum -/

theorem primeRecipSum_le (N : ℕ) :
    primeRecipSum N ≤ mertensPrimeWeightSum N / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [primeRecipSum, mertensPrimeWeightSum, Finset.sum_div]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [primeRecipWeight, mertensPrimeWeight]
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogn : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * Real.log 2),
      show (n : ℝ)⁻¹ * ((n : ℝ) * Real.log 2) = Real.log 2 by field_simp]
    exact hlogn
  · rw [if_neg hp, if_neg hp]
    simp

theorem primeRecipSum_le_log {N : ℕ} (hN : 1 ≤ N) :
    primeRecipSum N ≤ (Real.log N + mertensPrimeWindowBound) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine (primeRecipSum_le N).trans ?_
  gcongr
  exact mertensPrimeWeightSum_le N hN

theorem primeRecipSum_nonneg (N : ℕ) : 0 ≤ primeRecipSum N := by
  refine Finset.sum_nonneg fun n _ => ?_
  rw [primeRecipWeight]
  split_ifs
  · positivity
  · exact le_rfl

/-! ## The Abel representation -/

private def rpowNeg (δ : ℝ) (t : ℝ) : ℝ := t ^ (-δ)

private theorem hasDerivAt_rpowNeg {δ t : ℝ} (ht : 0 < t) :
    HasDerivAt (rpowNeg δ) (-δ * t ^ (-δ - 1)) t := by
  have h := Real.hasDerivAt_rpow_const (x := t) (p := -δ) (Or.inl ht.ne')
  exact h

private theorem deriv_rpowNeg {δ t : ℝ} (ht : 0 < t) :
    deriv (rpowNeg δ) t = -δ * t ^ (-δ - 1) := (hasDerivAt_rpowNeg ht).deriv

private theorem continuousOn_derivRpowNeg (δ : ℝ) :
    ContinuousOn (fun t : ℝ => -δ * t ^ (-δ - 1)) (Ici (1 : ℝ)) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have : ContinuousAt (fun x : ℝ => -δ * x ^ (-δ - 1)) t := by
    refine continuousAt_const.mul ?_
    exact (Real.continuousAt_rpow_const t (-δ - 1) (Or.inl ht0.ne'))
  exact this.continuousWithinAt

theorem tendsto_rpow_neg_mul_log {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => t ^ (-δ) * (Real.log t + mertensPrimeWindowBound)) atTop (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log t / t ^ δ) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have h2 : Tendsto (fun t : ℝ => mertensPrimeWindowBound / t ^ δ) atTop (nhds 0) := by
    refine Tendsto.div_atTop tendsto_const_nhds ?_
    exact tendsto_rpow_atTop hδ
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_neg ht.le]
  have hne : (t : ℝ) ^ δ ≠ 0 := by positivity
  field_simp

end

end RHTower
