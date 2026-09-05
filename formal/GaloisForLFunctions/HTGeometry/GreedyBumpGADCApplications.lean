import GaloisForLFunctions.HTGeometry.GADCTreePopulationRG
import GaloisForLFunctions.HTGeometry.GreedyBumpFactorialCumulants

/-!
# Greedy-bump cumulants for generalized-amplitude-damping branches

Physical GADC transition probabilities are Bernoulli events.  Packaging strict damping and bath
ranges turns both channel branches into one-point exclusion laws carrying the complete void
expansion of arXiv:2609.03581.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Strictly interior rational GADC parameters. -/
structure GreedyBumpGADCParameters where
  damping : ℚ
  bathPopulation : ℚ
  damping_pos : 0 < damping
  damping_lt_one : damping < 1
  bathPopulation_pos : 0 < bathPopulation
  bathPopulation_lt_one : bathPopulation < 1

/-- Positive-input transition probability as a strict real Bernoulli parameter. -/
def GreedyBumpGADCParameters.positiveOutputProbability
    (P : GreedyBumpGADCParameters) : StrictProbabilityParameter := by
  have hprodPos : 0 < P.damping * P.bathPopulation :=
    mul_pos P.damping_pos P.bathPopulation_pos
  have hprodLt : P.damping * P.bathPopulation < 1 := by
    calc
      P.damping * P.bathPopulation < 1 * P.bathPopulation :=
        mul_lt_mul_of_pos_right P.damping_lt_one P.bathPopulation_pos
      _ < 1 := by simpa using P.bathPopulation_lt_one
  exact ⟨(gadcPositiveOutputProbability P.damping P.bathPopulation : ℚ),
    by
      exact_mod_cast (sub_nonneg.mpr hprodLt.le :
        (0 : ℚ) ≤ 1 - P.damping * P.bathPopulation),
    by
      have h : (1 - P.damping * P.bathPopulation : ℚ) < 1 := by linarith
      exact_mod_cast h⟩

/-- Negative-input transition probability as a strict real Bernoulli parameter. -/
def GreedyBumpGADCParameters.negativeOutputProbability
    (P : GreedyBumpGADCParameters) : StrictProbabilityParameter := by
  have hbathVoid : 0 < 1 - P.bathPopulation := sub_pos.mpr P.bathPopulation_lt_one
  have hprobPos : 0 < P.damping * (1 - P.bathPopulation) :=
    mul_pos P.damping_pos hbathVoid
  have hprobLt : P.damping * (1 - P.bathPopulation) < 1 := by
    calc
      P.damping * (1 - P.bathPopulation) < 1 * (1 - P.bathPopulation) :=
        mul_lt_mul_of_pos_right P.damping_lt_one hbathVoid
      _ < 1 := by linarith [P.bathPopulation_pos]
  exact ⟨(gadcNegativeOutputProbability P.damping P.bathPopulation : ℚ),
    by exact_mod_cast hprobPos.le,
    by exact_mod_cast hprobLt⟩

/-- Complete plus-output connected correction series. -/
def GreedyBumpGADCParameters.positiveOutputCumulantSeries
    (P : GreedyBumpGADCParameters) : ℝ :=
  ∑' k : ℕ, greedyBumpBernoulliLogVoidContribution P.positiveOutputProbability k

/-- Complete minus-output connected correction series. -/
def GreedyBumpGADCParameters.negativeOutputCumulantSeries
    (P : GreedyBumpGADCParameters) : ℝ :=
  ∑' k : ℕ, greedyBumpBernoulliLogVoidContribution P.negativeOutputProbability k

/-- Absence of positive output has probability `damping * bathPopulation`. -/
theorem GreedyBumpGADCParameters.positiveOutputCumulantSeries_eq
    (P : GreedyBumpGADCParameters) :
    P.positiveOutputCumulantSeries =
      Real.log (((P.damping * P.bathPopulation : ℚ) : ℝ)) := by
  rw [GreedyBumpGADCParameters.positiveOutputCumulantSeries]
  rw [(greedyBumpBernoulli_logVoidSeries_hasSum
    P.positiveOutputProbability).tsum_eq]
  congr 1
  change 1 - (((1 - P.damping * P.bathPopulation : ℚ) : ℝ)) =
    (((P.damping * P.bathPopulation : ℚ) : ℝ))
  push_cast
  ring

/-- Absence of positive output from a negative input is the complementary thermal branch. -/
theorem GreedyBumpGADCParameters.negativeOutputCumulantSeries_eq
    (P : GreedyBumpGADCParameters) :
    P.negativeOutputCumulantSeries =
      Real.log (1 - (((P.damping * (1 - P.bathPopulation) : ℚ) : ℝ))) := by
  rw [GreedyBumpGADCParameters.negativeOutputCumulantSeries]
  rw [(greedyBumpBernoulli_logVoidSeries_hasSum
    P.negativeOutputProbability).tsum_eq]
  congr 2

/-- Difference of branchwise connected corrections is the log void-likelihood ratio of the GADC
population channel. -/
theorem GreedyBumpGADCParameters.cumulantSeries_gap
    (P : GreedyBumpGADCParameters) :
    P.positiveOutputCumulantSeries - P.negativeOutputCumulantSeries =
      Real.log (((P.damping * P.bathPopulation : ℚ) : ℝ)) -
        Real.log (1 - (((P.damping * (1 - P.bathPopulation) : ℚ) : ℝ))) := by
  rw [P.positiveOutputCumulantSeries_eq, P.negativeOutputCumulantSeries_eq]

end

end GaloisForLFunctions.HTGeometry
