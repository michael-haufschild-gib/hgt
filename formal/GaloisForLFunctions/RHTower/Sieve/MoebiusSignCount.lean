import GaloisForLFunctions.RHTower.Sieve.MoebiusEulerDamping

/-!
# Counting the two Möbius signs in a window

Since `μ` takes only the values `0, 1, -1`,

`μ(n) = [μ(n)=1] - [μ(n)=-1]`  and  `μ(n)² = [μ(n)=1] + [μ(n)=-1]`,

so over any window the two sign counts are recovered from the two summatory functions:

`#{n ∈ (t, t+L] : μ(n) = 1}  = (Q + M)/2`,
`#{n ∈ (t, t+L] : μ(n) = -1} = (Q - M)/2`,

with `M = ∑ μ(n)` and `Q = ∑ μ²(n)` the squarefree count.  A lower bound for `Q` together with an
upper bound for `|M|` therefore bounds *both* sign counts from below at once — which is how a
mean-square estimate for `M` is converted into the existence of many integers of each sign.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The Möbius function takes only the values `0, 1, -1`. -/
theorem moebius_trichotomy (n : ℕ) : moebius n = 0 ∨ moebius n = 1 ∨ moebius n = -1 := by
  rcases eq_or_ne (moebius n) 0 with h | h
  · exact Or.inl h
  · exact Or.inr (moebius_ne_zero_iff_eq_or.mp h)

/-- `μ` is the difference of the two sign indicators. -/
theorem moebius_eq_sub_indicator (n : ℕ) :
    ((moebius n : ℤ) : ℝ)
      = (if moebius n = 1 then 1 else 0) - (if moebius n = -1 then 1 else 0) := by
  rcases moebius_trichotomy n with h | h | h <;> rw [h] <;> norm_num

/-- `μ²` is the sum of the two sign indicators. -/
theorem moebius_sq_eq_add_indicator (n : ℕ) :
    ((moebius n : ℤ) : ℝ) ^ 2
      = (if moebius n = 1 then 1 else 0) + (if moebius n = -1 then 1 else 0) := by
  rcases moebius_trichotomy n with h | h | h <;> rw [h] <;> norm_num

/-- **The positive sign count.** -/
theorem two_mul_card_moebius_eq_one (t L : ℕ) :
    2 * (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
      = ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2
        + ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) := by
  classical
  have h1 : ∑ n ∈ Finset.Ioc t (t + L), (if moebius n = 1 then (1 : ℝ) else 0)
      = (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : ∑ n ∈ Finset.Ioc t (t + L), (if moebius n = -1 then (1 : ℝ) else 0)
      = (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun n _ => moebius_sq_eq_add_indicator n,
    Finset.sum_congr rfl fun n _ => moebius_eq_sub_indicator n,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2]
  ring

/-- **The negative sign count.** -/
theorem two_mul_card_moebius_eq_neg_one (t L : ℕ) :
    2 * (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ)
      = ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2
        - ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) := by
  classical
  have h1 : ∑ n ∈ Finset.Ioc t (t + L), (if moebius n = 1 then (1 : ℝ) else 0)
      = (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : ∑ n ∈ Finset.Ioc t (t + L), (if moebius n = -1 then (1 : ℝ) else 0)
      = (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun n _ => moebius_sq_eq_add_indicator n,
    Finset.sum_congr rfl fun n _ => moebius_eq_sub_indicator n,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2]
  ring

end RHTower.Sieve
