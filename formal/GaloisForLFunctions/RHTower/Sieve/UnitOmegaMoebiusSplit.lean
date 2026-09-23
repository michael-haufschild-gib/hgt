import GaloisForLFunctions.RHTower.Sieve.FibreNonRoughSpectral

/-!
# Restricting to exactly one designated prime factor

`Sieve/OmegaBudgetLadderTail.omegaBudget_le_ladder_final` consumes a sup bound for the cofactor
polynomial of the **plain** Möbius coefficient, which is what `Sieve/CofactorLowFreqBound` supplies.
The exact Ramaré identity produces the damped cofactor `μ(m)/(ω_P(m)+1)` instead, for which no such
bound exists in the corpus.

Restricting to the integers with *exactly one* designated prime factor removes the damping: there
the Ramaré weight is `1`, so the cofactor is a plain Möbius polynomial and the ladder's hypothesis
applies verbatim.  The price is a second discard — the integers with two or more designated prime
factors — which, like the rough integers, enters the fibre mean square squared.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The Möbius function restricted to integers with exactly one designated prime factor. -/
def unitOmegaMoebius (P : Finset ℕ) (n : ℕ) : ℝ :=
  if (primeFactorsIn P n).card = 1 then ((moebius n : ℤ) : ℝ) else 0

theorem abs_unitOmegaMoebius_le_one (P : Finset ℕ) (n : ℕ) : |unitOmegaMoebius P n| ≤ 1 := by
  rw [unitOmegaMoebius]
  split
  · exact abs_moebius_real_le_one n
  · simp

/-- **The two discards.**  Restricting to exactly one designated prime factor costs the rough
integers and the integers carrying two or more. -/
theorem abs_sum_sub_unitOmega_le (P S : Finset ℕ) :
    |∑ b ∈ S, ((moebius b : ℤ) : ℝ) - ∑ b ∈ S, unitOmegaMoebius P b|
      ≤ ((({b ∈ S | (primeFactorsIn P b).card = 0}).card : ℕ) : ℝ)
        + ((({b ∈ S | 2 ≤ (primeFactorsIn P b).card}).card : ℕ) : ℝ) := by
  classical
  have hsum : ∑ b ∈ S, unitOmegaMoebius P b
      = ∑ b ∈ {b ∈ S | (primeFactorsIn P b).card = 1}, ((moebius b : ℤ) : ℝ) := by
    rw [Finset.sum_filter]
    rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun b => (primeFactorsIn P b).card = 1) (fun b => ((moebius b : ℤ) : ℝ))
  have hdiff : ∑ b ∈ S, ((moebius b : ℤ) : ℝ) - ∑ b ∈ S, unitOmegaMoebius P b
      = ∑ b ∈ {b ∈ S | ¬ ((primeFactorsIn P b).card = 1)}, ((moebius b : ℤ) : ℝ) := by
    rw [hsum]
    linarith [hsplit]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun n _ => abs_moebius_real_le_one n)) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : {b ∈ S | ¬ ((primeFactorsIn P b).card = 1)}
      ⊆ {b ∈ S | (primeFactorsIn P b).card = 0} ∪ {b ∈ S | 2 ≤ (primeFactorsIn P b).card} := by
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases Nat.lt_or_ge (primeFactorsIn P b).card 1 with hlt | hge
    · exact Or.inl ⟨hb.1, by omega⟩
    · exact Or.inr ⟨hb.1, by omega⟩
  have hcard : ({b ∈ S | ¬ ((primeFactorsIn P b).card = 1)}).card
      ≤ ({b ∈ S | (primeFactorsIn P b).card = 0}).card
        + ({b ∈ S | 2 ≤ (primeFactorsIn P b).card}).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  exact_mod_cast hcard

/-- **The fibre mean square through the unit-`ω_P` restriction.**  Both discards enter squared. -/
theorem sum_sq_fibreSum_moebius_le_unitOmega {x h : ℝ} {P : Finset ℕ} {E : ℝ} (hE : 0 ≤ E)
    (hbd : ∀ a ∈ outerBlock x h,
      ((({b ∈ innerFibre x h a | (primeFactorsIn P b).card = 0}).card : ℕ) : ℝ)
        + ((({b ∈ innerFibre x h a | 2 ≤ (primeFactorsIn P b).card}).card : ℕ) : ℝ) ≤ E) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ (2 : ℕ)
      ≤ 2 * ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, unitOmegaMoebius P b) ^ (2 : ℕ)
        + 2 * ((outerBlock x h).card : ℝ) * E ^ (2 : ℕ) := by
  classical
  have hterm : ∀ a ∈ outerBlock x h,
      (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ (2 : ℕ)
        ≤ 2 * (∑ b ∈ innerFibre x h a, unitOmegaMoebius P b) ^ (2 : ℕ) + 2 * E ^ (2 : ℕ) := by
    intro a ha
    set A : ℝ := ∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ) with hAdef
    set G : ℝ := ∑ b ∈ innerFibre x h a, unitOmegaMoebius P b with hGdef
    have hdef : |A - G| ≤ E := by
      refine le_trans (abs_sum_sub_unitOmega_le P (innerFibre x h a)) (hbd a ha)
    have hsq : (A - G) ^ (2 : ℕ) ≤ E ^ (2 : ℕ) := by
      nlinarith [abs_nonneg (A - G), sq_abs (A - G), hdef, hE]
    nlinarith [hsq, sq_nonneg (A - 2 * G)]
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

end

end RHTower.Sieve
