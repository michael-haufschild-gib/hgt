import GaloisForLFunctions.HTGeometry.FactorialGrowthBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Gamma function outgrows every exponential

Taking logarithms in the exponential-series bound `n^n e^{-n} ≤ n!` gives

```
n (log n - 1) ≤ log n!,
```

so `log Γ(n+1) / n → ∞`: the Gamma function is of order one but *maximal type*, and no bound of the
form `log |f| = O(|s|)` can hold for a function that dominates it along the naturals.

This is the growth seed behind the classical fact that the completed zeta function is not of
exponential type, hence that its zero divisor is not summable in the first power.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Logarithmic form of the exponential-series factorial bound. -/
theorem natMul_log_sub_one_le_log_factorial (n : ℕ) :
    (n : ℝ) * (Real.log n - 1) ≤ Real.log n.factorial := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ n * Real.exp (-(n : ℝ)) := by positivity
  have hbound := _root_.HTGeometry.pow_mul_exp_neg_le_factorial n
  have hlog := Real.log_le_log hpos hbound
  have hval : Real.log ((n : ℝ) ^ n * Real.exp (-(n : ℝ)))
      = (n : ℝ) * (Real.log n - 1) := by
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    ring
  rwa [hval] at hlog

/-- The same bound for `Real.Gamma` at the naturals. -/
theorem natMul_log_sub_one_le_log_Gamma (n : ℕ) :
    (n : ℝ) * (Real.log n - 1) ≤ Real.log (Real.Gamma ((n : ℝ) + 1)) := by
  rw [Real.Gamma_nat_eq_factorial]
  exact natMul_log_sub_one_le_log_factorial n

/-- Beyond `e²` the crude half of the leading term already dominates. -/
theorem eventually_half_natMul_log_le_log_factorial :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) * Real.log n / 2 ≤ Real.log n.factorial := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp hnat).eventually_ge_atTop (2 : ℝ)
  filter_upwards [hlog, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbase := natMul_log_sub_one_le_log_factorial n
  nlinarith [hbase, hn0, hn]

/-- **Maximal type.**  `log n! / n → ∞`: the factorial, hence `Γ`, outgrows every exponential. -/
theorem tendsto_log_factorial_div_atTop :
    Tendsto (fun n : ℕ => Real.log n.factorial / (n : ℝ)) atTop atTop := by
  have hlow : ∀ᶠ n : ℕ in atTop, Real.log n - 1 ≤ Real.log n.factorial / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn0]
    have := natMul_log_sub_one_le_log_factorial n
    linarith [this]
  refine tendsto_atTop_mono' atTop hlow ?_
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  simpa using tendsto_atTop_add_const_right atTop (-1 : ℝ) hlog

/-- **No exponential majorant.**  For every constant `C` the factorial eventually exceeds `e^{C n}`,
so `Γ` admits no bound of the form `log Γ(n+1) ≤ C n`. -/
theorem eventually_lt_log_factorial (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) < Real.log n.factorial := by
  have hdiv := tendsto_log_factorial_div_atTop.eventually_gt_atTop C
  filter_upwards [hdiv, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [lt_div_iff₀ hn0] at hn
  linarith

/-- **Super-linear growth along the real ray.**  For every slope `A` the Gamma function exceeds
`exp (A σ)` at some real `σ ≥ 1`.  This is the hypothesis shape consumed by the zero-existence
criterion `exists_zero_of_superlinear_ray_growth`. -/
theorem exists_one_le_lt_log_Gamma (A : ℝ) :
    ∃ σ : ℝ, 1 ≤ σ ∧ A * σ < Real.log (Real.Gamma σ) := by
  obtain ⟨n, hfact, hbig⟩ :=
    ((eventually_lt_log_factorial (A + 1)).and (eventually_gt_atTop ⌈|A|⌉₊)).exists
  have hnA : |A| < (n : ℝ) := by
    have h1 : (⌈|A|⌉₊ : ℝ) < (n : ℝ) := by exact_mod_cast hbig
    exact lt_of_le_of_lt (Nat.le_ceil _) h1
  have hAle : A ≤ (n : ℝ) := le_trans (le_abs_self A) hnA.le
  refine ⟨(n : ℝ) + 1, by linarith [Nat.cast_nonneg (α := ℝ) n], ?_⟩
  have hGamma : Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n
  rw [hGamma]
  nlinarith [hfact, hAle]

end GaloisForLFunctions.HTGeometry
