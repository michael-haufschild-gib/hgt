import GaloisForLFunctions.RHTower.Sieve.CesaroLogWeightBound
import GaloisForLFunctions.RHTower.Sieve.LiouvilleChain

/-!
# The Cesàro chain, damped and instantiated at the Liouville function

The distance enters the Cesàro route in exactly one place: the pointwise bound on the truncated series.
No mean square, no sieve level, no dyadic split, no logarithmic recursion — the second-order kernel is
absolutely integrable, so its vertical integral is controlled by the pointwise size alone.

`‖∑_{n ≤ N} f(n)log(x/n)‖ ≤ ∑_{n ≤ N} E(σ,T,x/n) + (1/2π)·dampedSize σ δ z N·x^σ·π/σ`

for every bounded multiplicative `f` at distance at least `δ` from the characters `n^{it}`, `|t| ≤ T`.
At the Liouville function `δ` comes from the zero-free strip, so nothing is left open but the parameters.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- **The logarithmically weighted partial sum with the damped factor.** -/
theorem norm_sum_Icc_mul_log_div_le_cesaro_damped {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {σ T δ x : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) (hδ : 0 ≤ δ)
    {z : ℕ} (hz : 1 ≤ z) (hxN : (N : ℝ) ≤ x)
    (hunif : ∀ t : ℝ, |t| ≤ T →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    ‖∑ n ∈ Finset.Icc 1 N, truncSeq f N n * ((Real.log (x / n) : ℝ) : ℂ)‖
      ≤ (∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
        + (1 / (2 * Real.pi)) * (dampedSize σ δ z N * x ^ σ * (Real.pi / σ)) :=
  norm_sum_Icc_mul_log_div_le_cesaro hbdd hN hσ1.le hσ2 hT (dampedSize_nonneg hσ1 z N) hxN
    (fun _ ht => norm_LSeries_truncSeq_line_le_damped hf1 hmul hbdd hσ1 hz hδ hunif hN ht)

/-- **The Liouville logarithmically weighted partial sum through the Cesàro kernel.**  Every hypothesis
is discharged: complete multiplicativity by `liouvilleC_mul`, the distance by the zero-free strip, and the
analytic side by the integrable second-order decay of `x^s/s²`.  Only the parameters remain free. -/
theorem exists_norm_sum_Icc_liouvilleC_mul_log_div_le_cesaro :
    ∃ C : ℝ, ∀ (N z : ℕ) (σ T x : ℝ), 1 ≤ N → 3 ≤ z → 1 < σ → σ ≤ 2 → 1 ≤ T → 9 ≤ T →
      (N : ℝ) ≤ x → 1 / Real.log z ≤ zetaLowerA / Real.log T ^ (9 : ℕ) →
      ‖∑ n ∈ Finset.Icc 1 N, truncSeq liouvilleC N n * ((Real.log (x / n) : ℝ) : ℂ)‖
        ≤ (∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
          + (1 / (2 * Real.pi))
            * (dampedSize σ (liouvilleDelta C z T) z N * x ^ σ * (Real.pi / σ)) := by
  obtain ⟨C, hC⟩ := exists_liouvilleC_mulDistSqPair_ge_uniform
  refine ⟨C, fun N z σ T x hN hz hσ1 hσ2 hT hT9 hxN hzt => ?_⟩
  have hz1 : 1 ≤ z := by omega
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → liouvilleC (m * n) = liouvilleC m * liouvilleC n :=
    fun {m n} _ => liouvilleC_mul m n
  have hunif : ∀ t : ℝ, |t| ≤ T →
      liouvilleDelta C z T ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
    intro t ht
    rw [liouvilleDelta]
    exact Real.sqrt_le_sqrt (hC z T t hz hT9 ht hzt)
  exact norm_sum_Icc_mul_log_div_le_cesaro_damped liouvilleC_one hmul norm_liouvilleC_le hN hσ1
    hσ2 hT (Real.sqrt_nonneg _) hz1 hxN hunif

end RHTower.Sieve
end
