import GaloisForLFunctions.RHTower.Sieve.LogWeightVonMangoldtPair
import GaloisForLFunctions.RHTower.Sieve.LiouvilleChain

/-!
# The pair-convolution chain, damped and instantiated at the Liouville function

Substituting the damped size of the truncated factor into the pair bound gives a Halász-type mean value
theorem whose entire content is: the identity `f·log = (f·Λ) ⍟ f`, the cost `≤ N` of replacing `log n`
by `log N`, the near-diagonal Perron truncation error, the general affine mean square of the
`Λ`-weighted factor, and the damped Euler bound `e^{−δ²}` for the factor `f`.

No prime sieve, no logarithmic recursion, no primality anywhere.  At the Liouville function the distance
`δ` is supplied by the zero-free strip, so nothing is left open but the choice of parameters.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- **A Halász-type mean value bound through the pair convolution, with the damped factor.** -/
theorem norm_sum_Icc_mul_log_le_pair_damped {f : ℕ → ℂ} (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (hf1 : f 1 = 1) {N : ℕ} (hN : 1 ≤ N)
    {σ t₀ δ : ℝ} (hσ : 1 < σ) (ht₀ : 1 ≤ t₀) (hδ : 0 ≤ δ) {z : ℕ} (hz : 1 ≤ z) (K : ℕ)
    (hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
      ≤ (N : ℝ)
        + (Real.log ((N * N : ℕ) : ℝ) * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N * N : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
            + (1 / (2 * Real.pi))
              * perronVerticalPairBound σ ((N : ℝ) + 1 / 2) t₀ (dampedSize σ δ z N)
                  (generalMeanSquareConst (vonMangoldtSeq (truncSeq f N)) (Finset.Icc 1 N) σ)
                  (generalMeanSquareRate (vonMangoldtSeq (truncSeq f N)) (Finset.Icc 1 N) σ) K) := by
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := fun {m n} _ => hf m n
  exact norm_sum_Icc_mul_log_le_pair_general hf hbdd hN (dampedSize_nonneg hσ z N) hσ.le ht₀ K
    (fun _ ht => norm_LSeries_truncSeq_line_le_damped hf1 hmul hbdd hσ hz hδ hunif hN ht)

/-- **The Liouville partial sum through the pair-convolution chain.**  Every hypothesis is discharged:
complete multiplicativity by `liouvilleC_mul`, the distance by the zero-free strip, the analytic side by
the near-diagonal Perron error and the general affine mean square.  Only the parameters remain free. -/
theorem exists_norm_sum_Icc_liouvilleC_mul_log_pair_le :
    ∃ C : ℝ, ∀ (N z K : ℕ) (σ t₀ : ℝ), 1 ≤ N → 3 ≤ z → 1 < σ → 1 ≤ t₀ →
      9 ≤ t₀ * 2 ^ K → 1 / Real.log z ≤ zetaLowerA / Real.log (t₀ * 2 ^ K) ^ 9 →
      ‖∑ n ∈ Finset.Icc 1 N, liouvilleC n‖ * Real.log (N : ℝ)
        ≤ (N : ℝ)
          + (Real.log ((N * N : ℕ) : ℝ) * (((N : ℝ) + 1 / 2)) ^ σ
                * (5 * (1 + Real.log ((N * N : ℕ) : ℝ)) + 4 * (1 + Real.log N))
                / (Real.pi * (t₀ * 2 ^ K))
              + (1 / (2 * Real.pi))
                * perronVerticalPairBound σ ((N : ℝ) + 1 / 2) t₀
                    (dampedSize σ (liouvilleDelta C z (t₀ * 2 ^ K)) z N)
                    (generalMeanSquareConst (vonMangoldtSeq (truncSeq liouvilleC N))
                      (Finset.Icc 1 N) σ)
                    (generalMeanSquareRate (vonMangoldtSeq (truncSeq liouvilleC N))
                      (Finset.Icc 1 N) σ) K) := by
  obtain ⟨C, hC⟩ := exists_liouvilleC_mulDistSqPair_ge_uniform
  refine ⟨C, fun N z K σ t₀ hN hz hσ ht₀ hT hzt => ?_⟩
  have hz1 : 1 ≤ z := by omega
  have hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      liouvilleDelta C z (t₀ * 2 ^ K)
        ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
    intro t ht
    rw [liouvilleDelta]
    exact Real.sqrt_le_sqrt (hC z (t₀ * 2 ^ K) t hz hT ht hzt)
  exact norm_sum_Icc_mul_log_le_pair_damped liouvilleC_mul norm_liouvilleC_le liouvilleC_one hN hσ
    ht₀ (Real.sqrt_nonneg _) hz1 K hunif

end RHTower.Sieve
end
