import GaloisForLFunctions.HTGeometry.BiasedWalshInteractionMechanics
import GaloisForLFunctions.HTGeometry.GreedyBumpFactorialCumulants

/-!
# Greedy-bump cumulants in finite Boolean Gibbs sources

The product Bernoulli source underlying biased Walsh mechanics is a finite collection of
one-point exclusion laws.  Summing the all-order void corrections of arXiv:2609.03581 over its
coordinates reconstructs the empty-configuration weight and its vacuum Walsh coefficient.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open HTGeometry.ConstraintFrameRelativity

noncomputable section

/-- Finite Boolean source with strict coordinate void probabilities, carried as data. -/
structure GreedyBumpBooleanSource (I : Type*) [Fintype I] where
  probability : I → ℝ
  probability_nonneg : ∀ i, 0 ≤ probability i
  probability_lt_one : ∀ i, probability i < 1

/-- Strict Bernoulli parameter at one Boolean coordinate. -/
def GreedyBumpBooleanSource.coordinate
    {I : Type*} [Fintype I] (source : GreedyBumpBooleanSource I) (i : I) :
    StrictProbabilityParameter :=
  ⟨source.probability i, source.probability_nonneg i, source.probability_lt_one i⟩

/-- Paper's complete connected correction series at one Boolean coordinate. -/
theorem GreedyBumpBooleanSource.coordinate_logVoidSeries_hasSum
    {I : Type*} [Fintype I] (source : GreedyBumpBooleanSource I) (i : I) :
    HasSum (greedyBumpBernoulliLogVoidContribution (source.coordinate i))
      (Real.log (1 - source.probability i)) := by
  simpa [GreedyBumpBooleanSource.coordinate] using
    greedyBumpBernoulli_logVoidSeries_hasSum (source.coordinate i)

/-- Empty-configuration observable on the Boolean cube. -/
def greedyBumpBooleanVacuumObservable
    {I : Type*} [Fintype I] [DecidableEq I] (X : Finset I) : ℝ :=
  if X = ∅ then 1 else 0

/-- The vacuum observable's empty-support Walsh coefficient is the empty-configuration weight. -/
theorem GreedyBumpBooleanSource.biasedWalshCoefficient_vacuum
    {I : Type*} [Fintype I] [DecidableEq I] (source : GreedyBumpBooleanSource I) :
    biasedWalshCoefficient source.probability greedyBumpBooleanVacuumObservable ∅ =
      bernoulliWeight source.probability ∅ := by
  rw [biasedWalshCoefficient_empty]
  simp [bernoulliExp, greedyBumpBooleanVacuumObservable]

/-- Coordinatewise all-order cumulants reconstruct the Boolean source's log vacuum weight. -/
theorem GreedyBumpBooleanSource.totalCumulantSeries_eq_log_vacuumWeight
    {I : Type*} [Fintype I] [DecidableEq I] (source : GreedyBumpBooleanSource I) :
    (∑ i : I, ∑' k : ℕ,
      greedyBumpBernoulliLogVoidContribution (source.coordinate i) k) =
      Real.log (bernoulliWeight source.probability ∅) := by
  calc
    (∑ i : I, ∑' k : ℕ,
        greedyBumpBernoulliLogVoidContribution (source.coordinate i) k) =
        ∑ i : I, Real.log (1 - source.probability i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (source.coordinate_logVoidSeries_hasSum i).tsum_eq
    _ = Real.log (∏ i : I, (1 - source.probability i)) := by
      symm
      rw [Real.log_prod]
      intro i hi
      exact ne_of_gt (sub_pos.mpr (source.probability_lt_one i))
    _ = Real.log (bernoulliWeight source.probability ∅) := by
      simp [bernoulliWeight]

/-- Total connected correction is also the log vacuum coefficient in biased Walsh mechanics. -/
theorem GreedyBumpBooleanSource.totalCumulantSeries_eq_log_vacuumWalshCoefficient
    {I : Type*} [Fintype I] [DecidableEq I] (source : GreedyBumpBooleanSource I) :
    (∑ i : I, ∑' k : ℕ,
      greedyBumpBernoulliLogVoidContribution (source.coordinate i) k) =
      Real.log
        (biasedWalshCoefficient source.probability greedyBumpBooleanVacuumObservable ∅) := by
  rw [source.biasedWalshCoefficient_vacuum]
  exact source.totalCumulantSeries_eq_log_vacuumWeight

/-- Exponentiating all coordinatewise connected corrections recovers the Boolean vacuum weight. -/
theorem GreedyBumpBooleanSource.exp_totalCumulantSeries_eq_vacuumWeight
    {I : Type*} [Fintype I] [DecidableEq I] (source : GreedyBumpBooleanSource I) :
    Real.exp (∑ i : I, ∑' k : ℕ,
      greedyBumpBernoulliLogVoidContribution (source.coordinate i) k) =
      bernoulliWeight source.probability ∅ := by
  rw [source.totalCumulantSeries_eq_log_vacuumWeight]
  apply Real.exp_log
  simp only [bernoulliWeight, Finset.prod_empty, Finset.compl_empty, one_mul]
  exact Finset.prod_pos fun i hi => sub_pos.mpr (source.probability_lt_one i)

end

end GaloisForLFunctions.HTGeometry
