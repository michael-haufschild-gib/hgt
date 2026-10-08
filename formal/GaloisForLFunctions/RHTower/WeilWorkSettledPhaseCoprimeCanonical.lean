import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeMasks
import GaloisForLFunctions.RHTower.WeilPrimeDeficitSetRigidity

/-!
# The canonical contribution excluded by a finite coprime mask

The proper prime powers have a summable harmonic weight. Among primes, only
divisors of the fixed modulus can be excluded.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

def nonCoprimePart (Q : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n.Coprime Q then 0 else f n

theorem nonCoprimePart_eq_sub (Q : ℕ) (f : ℕ → ℂ) :
    nonCoprimePart Q f = f - coprimePart Q f := by
  funext n
  by_cases hc : n.Coprime Q
  · simp only [nonCoprimePart, coprimePart, coprimeMask, Pi.sub_apply, if_pos hc,
      Complex.ofReal_one, one_mul, sub_self]
  · simp only [nonCoprimePart, coprimePart, coprimeMask, Pi.sub_apply, if_neg hc,
      Complex.ofReal_zero, zero_mul, sub_zero]

theorem summable_nonCoprimePart (Q : ℕ) {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (nonCoprimePart Q f) s := by
  rw [nonCoprimePart_eq_sub]
  exact hf.sub (summable_coprimePart Q hf)

private theorem summable_nonCoprime_vonMangoldt_div (Q : ℕ) [NeZero Q] :
    Summable (fun n : ℕ => if n.Coprime Q then 0 else
      (ArithmeticFunction.vonMangoldt n : ℝ) / n) := by
  have hhead : Summable (fun n : ℕ => if n ∈ Q.divisors then
      (ArithmeticFunction.vonMangoldt n : ℝ) / n else 0) :=
    summable_of_ne_finset_zero (s := Q.divisors) fun _ hn => if_neg hn
  have hs := WeilPrimeDeficit.summable_nonprime_vonMangoldt_div.add hhead
  refine hs.of_nonneg_of_le (fun n => by split_ifs <;> positivity) fun n => ?_
  by_cases hc : n.Coprime Q
  · simp only [if_pos hc]
    positivity
  · by_cases hp : n.Prime
    · have hd : n ∣ Q := not_not.mp (fun h => hc (hp.coprime_iff_not_dvd.mpr h))
      have hm : n ∈ Q.divisors := Nat.mem_divisors.mpr ⟨hd, NeZero.ne Q⟩
      simp only [if_neg hc, if_pos hp, if_pos hm, zero_add, le_refl]
    · simp only [if_neg hc, if_neg hp]
      apply le_add_of_nonneg_right
      split_ifs <;> positivity

/-- The canonical logarithmic derivative excluded by any finite prime deletion
is absolutely convergent at one. -/
theorem LSeriesSummable_nonCoprime_vonMangoldt_one (Q : ℕ) [NeZero Q] :
    LSeriesSummable (nonCoprimePart Q
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) 1 := by
  apply Summable.of_norm
  refine (summable_nonCoprime_vonMangoldt_div Q).congr fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [if_neg hn, Complex.one_re, Real.rpow_one]
    by_cases hc : n.Coprime Q
    · simp only [nonCoprimePart, if_pos hc, norm_zero, zero_div]
    · simp only [nonCoprimePart, if_neg hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

theorem exists_norm_nonCoprime_vonMangoldt_le (Q : ℕ) [NeZero Q] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 ≤ σ →
      ‖LSeries (nonCoprimePart Q
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (σ : ℂ)‖ ≤ C := by
  let f := nonCoprimePart Q (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  have hs : LSeriesSummable f 1 := LSeriesSummable_nonCoprime_vonMangoldt_one Q
  refine ⟨∑' n, ‖LSeries.term f 1 n‖, tsum_nonneg (fun _ => norm_nonneg _), fun σ hσ => ?_⟩
  have hs' : LSeriesSummable f (σ : ℂ) := hs.of_re_le_re (by simpa using hσ)
  exact (norm_tsum_le_tsum_norm hs'.norm).trans
    (hs'.norm.tsum_le_tsum (fun n =>
      LSeries.norm_term_le_of_re_le_re f (by simpa using hσ) n) hs.norm)

end RHTower.WeilSingularArithmetic
