import GaloisForLFunctions.RHTower.PrimeMobiusLoschmidtPurity
import GaloisForLFunctions.HTGeometry.GreedyBumpFactorialCumulants

/-!
# Greedy-bump cumulants in squarefree Loschmidt purity

At each prime, squarefree occupation is Bernoulli.  The local Loschmidt purity is the probability
that two independent occupations agree, hence the void probability of their mismatch event.
The all-order factorial-cumulant expansion from arXiv:2609.03581 therefore reconstructs the log
purity of every finite-prime quantum return state.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive inverse temperature, carried as data. -/
abbrev GreedyBumpPositivePrimeTemperature := {σ : ℝ // 0 < σ}

/-- Squarefree occupation probability at one prime. -/
def greedyBumpPrimeOccupationProbability
    (σ : GreedyBumpPositivePrimeTemperature) (p : Nat.Primes) : ℝ :=
  primeSchurWeight σ p / (1 + primeSchurWeight σ p)

/-- Probability that two independent prime occupations disagree. -/
def greedyBumpPrimeMismatchProbability
    (σ : GreedyBumpPositivePrimeTemperature) (p : Nat.Primes) : ℝ :=
  2 * greedyBumpPrimeOccupationProbability σ p *
    (1 - greedyBumpPrimeOccupationProbability σ p)

/-- Prime mismatch is a strict hard-exclusion parameter. -/
def greedyBumpPrimeMismatchParameter
    (σ : GreedyBumpPositivePrimeTemperature) (p : Nat.Primes) :
    GaloisForLFunctions.HTGeometry.StrictProbabilityParameter := by
  let q := primeSchurWeight σ p
  have hq : 0 < q := primeSchurWeight_pos σ p
  have hp : 0 < q / (1 + q) := div_pos hq (by positivity)
  have hp1 : q / (1 + q) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  refine ⟨greedyBumpPrimeMismatchProbability σ p, ?_, ?_⟩
  · unfold greedyBumpPrimeMismatchProbability greedyBumpPrimeOccupationProbability
    positivity
  · have hsquare : 0 ≤ (2 * (q / (1 + q)) - 1) ^ 2 := sq_nonneg _
    unfold greedyBumpPrimeMismatchProbability greedyBumpPrimeOccupationProbability
    change 2 * (q / (1 + q)) * (1 - q / (1 + q)) < 1
    nlinarith

/-- One-prime collision purity is exactly the void mass of the mismatch exclusion event. -/
theorem greedyBumpPrimeMismatch_void_eq_collisionFactor
    (σ : GreedyBumpPositivePrimeTemperature) (p : Nat.Primes) :
    1 - greedyBumpPrimeMismatchProbability σ p =
      (1 + primeSchurWeight σ p ^ 2) /
        (1 + primeSchurWeight σ p) ^ 2 := by
  have hq : 0 < primeSchurWeight σ p := primeSchurWeight_pos σ p
  unfold greedyBumpPrimeMismatchProbability greedyBumpPrimeOccupationProbability
  field_simp
  ring

/-- Complete connected mismatch hierarchy reconstructs one-prime collision purity. -/
theorem greedyBumpPrimeMismatch_logPuritySeries_hasSum
    (σ : GreedyBumpPositivePrimeTemperature) (p : Nat.Primes) :
    HasSum
      (GaloisForLFunctions.HTGeometry.greedyBumpBernoulliLogVoidContribution
        (greedyBumpPrimeMismatchParameter σ p))
      (Real.log ((1 + primeSchurWeight σ p ^ 2) /
        (1 + primeSchurWeight σ p) ^ 2)) := by
  have h := GaloisForLFunctions.HTGeometry.greedyBumpBernoulli_logVoidSeries_hasSum
    (greedyBumpPrimeMismatchParameter σ p)
  change HasSum
    (GaloisForLFunctions.HTGeometry.greedyBumpBernoulliLogVoidContribution
      (greedyBumpPrimeMismatchParameter σ p))
    (Real.log (1 - greedyBumpPrimeMismatchProbability σ p)) at h
  rw [greedyBumpPrimeMismatch_void_eq_collisionFactor σ p] at h
  exact h

/-- Sum of all primewise connected corrections is log finite-prime Loschmidt purity. -/
theorem greedyBumpFinitePrimeLoschmidt_totalCumulantSeries_eq_log_purity
    (S : Finset Nat.Primes) (σ : GreedyBumpPositivePrimeTemperature) :
    (∑ p ∈ S, ∑' k : ℕ,
      GaloisForLFunctions.HTGeometry.greedyBumpBernoulliLogVoidContribution
        (greedyBumpPrimeMismatchParameter σ p) k) =
      Real.log (finitePrimeSquarefreeLoschmidtPurity S σ) := by
  rw [finitePrimeSquarefreeLoschmidtPurity_eq_prod]
  calc
    (∑ p ∈ S, ∑' k : ℕ,
        GaloisForLFunctions.HTGeometry.greedyBumpBernoulliLogVoidContribution
          (greedyBumpPrimeMismatchParameter σ p) k) =
        ∑ p ∈ S, Real.log ((1 + primeSchurWeight σ p ^ 2) /
          (1 + primeSchurWeight σ p) ^ 2) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (greedyBumpPrimeMismatch_logPuritySeries_hasSum σ p).tsum_eq
    _ = Real.log (∏ p ∈ S, (1 + primeSchurWeight σ p ^ 2) /
          (1 + primeSchurWeight σ p) ^ 2) := by
      symm
      apply Real.log_prod
      intro p hp
      have hq : 0 < primeSchurWeight σ p := primeSchurWeight_pos σ p
      exact div_ne_zero (by positivity) (pow_ne_zero 2 (by positivity))

/-- Exponentiating connected mismatch corrections recovers exact quantum return purity. -/
theorem greedyBumpFinitePrimeLoschmidt_exp_totalCumulantSeries_eq_purity
    (S : Finset Nat.Primes) (σ : GreedyBumpPositivePrimeTemperature) :
    Real.exp (∑ p ∈ S, ∑' k : ℕ,
      GaloisForLFunctions.HTGeometry.greedyBumpBernoulliLogVoidContribution
        (greedyBumpPrimeMismatchParameter σ p) k) =
      finitePrimeSquarefreeLoschmidtPurity S σ := by
  rw [greedyBumpFinitePrimeLoschmidt_totalCumulantSeries_eq_log_purity]
  exact Real.exp_log (finitePrimeSquarefreeLoschmidtPurity_pos S σ)

end

end RHTower
