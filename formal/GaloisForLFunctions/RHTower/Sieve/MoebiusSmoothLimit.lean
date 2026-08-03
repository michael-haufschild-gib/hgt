import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothCancellation

/-!
# The Möbius sum over squarefree smooth numbers vanishes in the limit

The prime harmonic sum diverges, so the explicit rate `exp(2 - ∑_{p ∈ P} 1/p)` tends to zero as `P`
exhausts the primes:

`‖∑_{n squarefree, p ∣ n ⇒ p < N} μ(n)/n‖ → 0`.

This is the limit form of the cancellation bound — unconditional, with the divergence of `∑ 1/p`
supplying the whole of the decay.
-/

namespace RHTower.Sieve

open Finset Filter

/-- **The prime harmonic sum diverges.** -/
theorem tendsto_sum_primesBelow_inv_atTop :
    Tendsto (fun N => ∑ p ∈ Nat.primesBelow N, 1 / (p : ℝ)) atTop atTop := by
  classical
  have hnn : ∀ n : ℕ, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun m : ℕ => (1 : ℝ) / m) n :=
    fun n => Set.indicator_nonneg (fun m _ => by positivity) n
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp not_summable_one_div_on_primes
  refine h.congr fun N => ?_
  have hite : ∑ i ∈ Finset.range N, Set.indicator {p : ℕ | p.Prime} (fun m : ℕ => (1 : ℝ) / m) i
      = ∑ i ∈ Finset.range N, (if i.Prime then (1 : ℝ) / i else 0) :=
    Finset.sum_congr rfl fun i _ => by simp [Set.indicator_apply]
  rw [hite, ← Finset.sum_filter]
  rfl

/-- `exp(2 - u)` vanishes along a divergent `u`. -/
theorem tendsto_exp_two_sub {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) :
    Tendsto (fun N => Real.exp (2 - u N)) atTop (nhds 0) := by
  have hnegu : Tendsto (fun N => -u N) atTop atBot := tendsto_neg_atTop_atBot.comp hu
  have hsub : Tendsto (fun N => 2 - u N) atTop atBot := by
    simpa [sub_eq_add_neg] using tendsto_atBot_add_const_left atTop (2 : ℝ) hnegu
  exact Real.tendsto_exp_atBot.comp hsub

/-- **The Möbius sum over squarefree smooth numbers tends to zero.** -/
theorem tendsto_norm_sum_moebius_smooth_zero :
    Tendsto (fun N => ‖∑ n ∈ (Nat.primesBelow N).powerset.image (fun T => ∏ p ∈ T, p),
        ((1 / (n : ℝ) : ℝ) : ℂ) * moebiusC n‖) atTop (nhds 0) := by
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
    (tendsto_exp_two_sub tendsto_sum_primesBelow_inv_atTop)
  exact norm_sum_moebius_smooth_zero_le fun p hp => Nat.prime_of_mem_primesBelow hp

end RHTower.Sieve
