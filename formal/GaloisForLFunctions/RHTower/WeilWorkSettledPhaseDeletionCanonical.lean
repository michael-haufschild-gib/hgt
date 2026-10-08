import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionMasks
import GaloisForLFunctions.RHTower.WeilPrimeDeficitSetRigidity
/-!
# The canonical even logarithmic derivative at one

Proper prime powers are harmonically summable. The even restriction adds
only the single prime two, giving a uniform bound on the closed half-line.
-/

open Complex Filter Topology Set
noncomputable section
namespace RHTower.WeilWorkSettledPhase

private theorem summable_even_vonMangoldt_div :
    Summable (fun n : ℕ => if 2 ∣ n then (ArithmeticFunction.vonMangoldt n : ℝ)/n else 0) := by
  have hd : Summable (fun n : ℕ => if n=2 then Real.log 2/2 else 0) :=
    summable_of_ne_finset_zero (s := {2}) fun n hn => by
      simp only [Finset.mem_singleton] at hn
      simp [hn]
  have hlog : 0 ≤ Real.log (2 : ℝ)/2 :=
    div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hs := WeilPrimeDeficit.summable_nonprime_vonMangoldt_div.add hd
  refine hs.of_nonneg_of_le (fun n => by split_ifs <;> positivity) fun n => ?_
  by_cases hp : n.Prime
  · by_cases he : 2 ∣ n
    · have hn : n=2 := by
        rcases (Nat.dvd_prime hp).mp he with h | h
        · norm_num at h
        · exact h.symm
      subst n
      simp [Nat.prime_two,ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    · simp only [hp,he,if_true,if_false,zero_add]
      split_ifs <;> linarith
  · by_cases he : 2 ∣ n
    · simp only [hp,he,if_false,if_true]
      apply le_add_of_nonneg_right
      split_ifs <;> linarith
    · simp only [hp,he,if_false]
      split_ifs <;> positivity

/-- The even restriction of the canonical logarithmic derivative is absolutely
convergent at one. -/
theorem LSeriesSummable_even_vonMangoldt_one :
    LSeriesSummable (evenPart (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) 1 := by
  apply Summable.of_norm
  refine summable_even_vonMangoldt_div.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hn : n=0
  · subst n
    simp
  · by_cases he : 2 ∣ n <;>
      simp [hn,he,evenPart,Complex.norm_real,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- A uniform bound down to the pole for the even canonical logarithmic derivative. -/
theorem exists_norm_even_vonMangoldt_le :
    ∃ C : ℝ, 0≤C ∧ ∀ σ : ℝ, 1≤σ →
      ‖LSeries (evenPart (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (σ : ℂ)‖≤C := by
  let f := evenPart (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  have hs : LSeriesSummable f 1 := LSeriesSummable_even_vonMangoldt_one
  refine ⟨∑' n, ‖LSeries.term f 1 n‖,tsum_nonneg fun _ => norm_nonneg _,fun σ hσ => ?_⟩
  have hs' : LSeriesSummable f (σ : ℂ) := hs.of_re_le_re (by simpa using hσ)
  exact (norm_tsum_le_tsum_norm hs'.norm).trans
    (hs'.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re f (by simpa using hσ) n) hs.norm)

end RHTower.WeilWorkSettledPhase

