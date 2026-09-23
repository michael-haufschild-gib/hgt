import GaloisForLFunctions.RHTower.Sieve.JointCongruenceClass
import GaloisForLFunctions.RHTower.Sieve.SquarefreeCount

/-!
# The truncated squarefree pair sum as a weighted joint count

Expanding the truncated squarefree identity on both `n` and `n + h` and exchanging the order of
summation:

`∑_{n ∈ (t,t+L]} (∑_{d ≤ R, d² ∣ n} μ(d)) (∑_{e ≤ R, e² ∣ n+h} μ(e))
   = ∑_{d,e ≤ R} μ(d)μ(e) · #{n ∈ (t,t+L] : d² ∣ n ∧ e² ∣ n+h}`.

This is exact — no truncation error is incurred by the exchange itself.  Each joint count is then
supplied by `abs_card_joint_sub_lt` for coprime `d, e`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **The truncated pair sum is a weighted sum of joint counts.** -/
theorem sum_truncated_pair_eq (t L R h : ℕ) :
    ∑ n ∈ Finset.Ioc t (t + L),
        (∑ d ∈ {d ∈ Finset.Icc 1 R | d ^ (2 : ℕ) ∣ n}, ((moebius d : ℤ) : ℝ))
          * (∑ e ∈ {e ∈ Finset.Icc 1 R | e ^ (2 : ℕ) ∣ (n + h)}, ((moebius e : ℤ) : ℝ))
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          ((moebius d : ℤ) : ℝ) * ((moebius e : ℤ) : ℝ)
            * ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n ∧ e ^ (2 : ℕ) ∣ (n + h)} : ℕ) : ℝ) := by
  classical
  have hterm : ∀ n ∈ Finset.Ioc t (t + L),
      (∑ d ∈ {d ∈ Finset.Icc 1 R | d ^ (2 : ℕ) ∣ n}, ((moebius d : ℤ) : ℝ))
          * (∑ e ∈ {e ∈ Finset.Icc 1 R | e ^ (2 : ℕ) ∣ (n + h)}, ((moebius e : ℤ) : ℝ))
        = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
            (if d ^ (2 : ℕ) ∣ n ∧ e ^ (2 : ℕ) ∣ (n + h) then
              ((moebius d : ℤ) : ℝ) * ((moebius e : ℤ) : ℝ) else 0) := by
    intro n _
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    by_cases h1 : d ^ (2 : ℕ) ∣ n
    · by_cases h2 : e ^ (2 : ℕ) ∣ (n + h)
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg h2, mul_zero, if_neg (fun hc => h2 hc.2)]
    · rw [if_neg h1, zero_mul, if_neg (fun hc => h1 hc.1)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

end RHTower.Sieve
