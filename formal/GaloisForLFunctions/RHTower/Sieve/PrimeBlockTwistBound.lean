import GaloisForLFunctions.RHTower.Sieve.LadderBlockMeanSquare
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPrimeEnvelope

/-!
# The prime polynomial of a range is a twisted prime sum

The prime polynomial of a ladder step is, up to a sign, the twisted prime sum `∑_{p ∈ (a,b]} p^{2πiw}`
— the difference of two initial twisted prime sums.  So the Route-T (Vinogradov--Korobov) envelope
bounds it directly, and the analytic input of the short-interval argument enters exactly here.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The Gallagher phase at a positive integer is the complex power. -/
theorem unitLogPhase_eq_cpow {n : ℕ} (hn : 0 < n) (w : ℝ) :
    unitLogPhase w n = (n : ℂ) ^ (((2 * Real.pi * w : ℝ) : ℂ) * Complex.I) := by
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    rw [show (((n : ℕ)) : ℂ) = (((n : ℕ) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hnR.le).symm
  rw [Complex.cpow_def_of_ne_zero hn0, hlog, unitLogPhase]
  congr 1
  push_cast
  ring

/-- The Route-T twisted prime coefficient is the Gallagher phase at a prime. -/
theorem primeTwist_eq_unitLogPhase {p : ℕ} (hp : p.Prime) (w : ℝ) :
    primeTwist (-(2 * Real.pi * w)) p = unitLogPhase w p := by
  rw [primeTwist, if_pos hp, unitLogPhase_eq_cpow hp.pos w]
  congr 1
  push_cast
  ring

/-- The Möbius phase at a prime is minus the twisted prime coefficient. -/
theorem moebiusPhase_prime_eq_neg_primeTwist {p : ℕ} (hp : p.Prime) (w : ℝ) :
    moebiusPhase w p = -primeTwist (-(2 * Real.pi * w)) p := by
  rw [moebiusPhase, primeTwist_eq_unitLogPhase hp w,
    ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

/-- **The prime polynomial of a block is minus the twisted prime sum over it.** -/
theorem primeBlockPoly_eq_neg_sum {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (w : ℝ) :
    primeBlockPoly B w = -∑ p ∈ B, primeTwist (-(2 * Real.pi * w)) p := by
  rw [primeBlockPoly, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p hp => moebiusPhase_prime_eq_neg_primeTwist (hB p hp) w

/-- **The twisted prime sum over a range is a difference of initial sums.** -/
theorem sum_primeTwist_range_eq {B : Finset ℕ} {a b : ℕ} (hab : a ≤ b)
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b)) (τ : ℝ) :
    ∑ p ∈ B, primeTwist τ p
      = (∑ n ∈ Finset.range (b + 1), primeTwist τ n)
        - ∑ n ∈ Finset.range (a + 1), primeTwist τ n := by
  classical
  have hsub : Finset.range (a + 1) ⊆ Finset.range (b + 1) := by
    intro n hn
    rw [Finset.mem_range] at hn ⊢
    omega
  rw [← Finset.sum_sdiff_eq_sub hsub]
  have hset : Finset.range (b + 1) \ Finset.range (a + 1) = Finset.Ico (a + 1) (b + 1) := by
    ext n
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    rw [hB] at hp
    rw [Finset.mem_Ico]
    omega
  · intro n hn hnB
    rw [Finset.mem_Ico] at hn
    by_cases hprime : n.Prime
    · exact absurd ((hB n).2 ⟨hprime, by omega, by omega⟩) hnB
    · rw [primeTwist, if_neg hprime]

/-- **The prime polynomial of a range, bounded by two initial twisted prime sums.** -/
theorem norm_primeBlockPoly_le_of_range {B : Finset ℕ} {a b : ℕ} (hab : a ≤ b)
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b)) (w : ℝ) :
    ‖primeBlockPoly B w‖
      ≤ ‖∑ n ∈ Finset.range (b + 1), primeTwist (-(2 * Real.pi * w)) n‖
        + ‖∑ n ∈ Finset.range (a + 1), primeTwist (-(2 * Real.pi * w)) n‖ := by
  have hBp : ∀ p ∈ B, p.Prime := fun p hp => ((hB p).1 hp).1
  rw [primeBlockPoly_eq_neg_sum hBp w, norm_neg,
    sum_primeTwist_range_eq hab hB (-(2 * Real.pi * w))]
  exact norm_sub_le _ _

/-- **The Route-T bound for the prime polynomial of a ladder step.**  This is the single analytic
input of the short-interval argument: cancellation in `∑_{p ∈ (a,b]} p^{2πiw}`. -/
theorem exists_norm_primeBlockPoly_routeT_le :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (B : Finset ℕ) (a b : ℕ), a ≤ b → (∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b)) →
      ∀ w : ℝ, ‖primeBlockPoly B w‖
        ≤ (routeTTwistEnvelope A delta C (-(2 * Real.pi * w)) (max (b : ℝ) 1) + 7 * Real.exp 9)
              * (1 / Real.log 2 + 1 / Real.log ((b + 1 : ℕ) : ℝ))
          + (routeTTwistEnvelope A delta C (-(2 * Real.pi * w)) (max (a : ℝ) 1) + 7 * Real.exp 9)
              * (1 / Real.log 2 + 1 / Real.log ((a + 1 : ℕ) : ℝ)) := by
  obtain ⟨A, delta, C, hdelta, hC, hbound⟩ := exists_norm_sum_primeTwist_routeT_le
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro B a b hab hB w
  refine (norm_primeBlockPoly_le_of_range hab hB w).trans ?_
  exact add_le_add (hbound b (-(2 * Real.pi * w))) (hbound a (-(2 * Real.pi * w)))

end

end RHTower.Sieve
