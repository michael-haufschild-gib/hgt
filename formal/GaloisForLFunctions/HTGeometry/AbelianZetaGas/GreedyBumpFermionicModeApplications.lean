import GaloisForLFunctions.HTGeometry.AbelianZetaGas.FermionicModeFan
import GaloisForLFunctions.HTGeometry.GreedyBumpFactorialCumulants

/-!
# Greedy-bump factorial cumulants for fermionic zeta-gas modes

Each fermionic mode is a literal one-point exclusion law.  The all-order void expansion from
arXiv:2609.03581 therefore identifies its connected occupation hierarchy with the logarithm of
the local fermionic partition factor.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace AbelianZetaParameters

/-- Fermionic activity is strictly below one, including boundary activities `ratio = 1`. -/
theorem fermionicActivity_lt_one (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.fermionicActivity m < 1 := by
  rw [fermionicActivity]
  have hden : 0 < 1 + θ.ratio m := by linarith [θ.ratio_nonneg m]
  exact (div_lt_one hden).2 (by linarith)

/-- Strict Bernoulli parameter underlying a fermionic zeta-gas mode. -/
def fermionicModeStrictProbability
    (θ : AbelianZetaParameters) (m : AbelianZetaMode) : StrictProbabilityParameter :=
  ⟨θ.fermionicActivity m, θ.fermionicActivity_nonneg m, θ.fermionicActivity_lt_one m⟩

/-- Finite point-count realization of one fermionic mode. -/
def greedyBumpFermionicModeCount
    (θ : AbelianZetaParameters) (m : AbelianZetaMode) : FinitePointCountLaw Bool :=
  greedyBumpBernoulliExclusion (fermionicModeStrictProbability θ m).toProbabilityParameter

/-- First connected occupation coefficient of a fermionic mode. -/
theorem greedyBumpFermionicMode_factorialCumulantOne
    (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    (θ.greedyBumpFermionicModeCount m).factorialCumulantOne = θ.fermionicActivity m := by
  simpa [greedyBumpFermionicModeCount, fermionicModeStrictProbability,
    StrictProbabilityParameter.toProbabilityParameter] using
    greedyBumpBernoulli_factorialCumulantOne
      (fermionicModeStrictProbability θ m).toProbabilityParameter

/-- Second connected occupation coefficient is negative. -/
theorem greedyBumpFermionicMode_factorialCumulantTwo
    (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    (θ.greedyBumpFermionicModeCount m).factorialCumulantTwo =
      -(θ.fermionicActivity m) ^ 2 := by
  simpa [greedyBumpFermionicModeCount, fermionicModeStrictProbability,
    StrictProbabilityParameter.toProbabilityParameter] using
    greedyBumpBernoulli_factorialCumulantTwo
      (fermionicModeStrictProbability θ m).toProbabilityParameter

/-- Third connected occupation coefficient is positive. -/
theorem greedyBumpFermionicMode_factorialCumulantThree
    (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    (θ.greedyBumpFermionicModeCount m).factorialCumulantThree =
      2 * (θ.fermionicActivity m) ^ 3 := by
  simpa [greedyBumpFermionicModeCount, fermionicModeStrictProbability,
    StrictProbabilityParameter.toProbabilityParameter] using
    greedyBumpBernoulli_factorialCumulantThree
      (fermionicModeStrictProbability θ m).toProbabilityParameter

/-- All-order alternating sign law for a fermionic mode. -/
theorem greedyBumpFermionicMode_signed_factorialCumulantSucc_nonneg
    (θ : AbelianZetaParameters) (m : AbelianZetaMode) (k : ℕ) :
    0 ≤ (-1 : ℝ) ^ k * greedyBumpBernoulliFactorialCumulantSucc
      (fermionicModeStrictProbability θ m) k := by
  exact greedyBumpBernoulli_signed_factorialCumulantSucc_nonneg
    (fermionicModeStrictProbability θ m) k

/-- Complete connected correction series equals minus the local fermionic free energy. -/
theorem greedyBumpFermionicMode_cumulantSeries_eq_neg_log_partitionFactor
    (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    (∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
      (fermionicModeStrictProbability θ m) k) =
      -Real.log (1 + θ.ratio m) := by
  rw [(greedyBumpBernoulli_logVoidSeries_hasSum
    (fermionicModeStrictProbability θ m)).tsum_eq]
  change Real.log (1 - θ.ratio m / (1 + θ.ratio m)) = _
  have hden : 0 < 1 + θ.ratio m := by linarith [θ.ratio_nonneg m]
  rw [show 1 - θ.ratio m / (1 + θ.ratio m) = (1 + θ.ratio m)⁻¹ by
    field_simp [ne_of_gt hden]
    ring]
  rw [Real.log_inv]

/-- The zero-occupation atom of the measure-valued fermionic law. -/
theorem fermionicModeLaw_void
    (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.fermionicModeLaw m {0} = ENNReal.ofReal (1 - θ.fermionicActivity m) := by
  rw [fermionicModeLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

/-- Exponentiating the complete cumulant series recovers the actual measure's void atom. -/
theorem fermionicModeLaw_void_eq_exp_cumulantSeries
    (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    θ.fermionicModeLaw m {0} = ENNReal.ofReal
      (Real.exp (∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
        (fermionicModeStrictProbability θ m) k)) := by
  rw [θ.fermionicModeLaw_void]
  rw [(greedyBumpBernoulli_logVoidSeries_hasSum
    (fermionicModeStrictProbability θ m)).tsum_eq]
  change ENNReal.ofReal (1 - θ.fermionicActivity m) =
    ENNReal.ofReal (Real.exp (Real.log (1 - θ.fermionicActivity m)))
  rw [Real.exp_log (sub_pos.mpr (θ.fermionicActivity_lt_one m))]

/-- On a finite mode set, total connected correction is minus log of the finite fermionic
partition product. -/
theorem greedyBumpFermionicModes_cumulantSeries_eq_neg_log_partitionProduct
    (θ : AbelianZetaParameters) (S : Finset AbelianZetaMode) :
    (∑ m ∈ S, ∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
      (fermionicModeStrictProbability θ m) k) =
      -Real.log (∏ m ∈ S, (1 + θ.ratio m)) := by
  calc
    (∑ m ∈ S, ∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
        (fermionicModeStrictProbability θ m) k) =
        ∑ m ∈ S, -Real.log (1 + θ.ratio m) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact θ.greedyBumpFermionicMode_cumulantSeries_eq_neg_log_partitionFactor m
    _ = -(∑ m ∈ S, Real.log (1 + θ.ratio m)) := by
      rw [Finset.sum_neg_distrib]
    _ = -Real.log (∏ m ∈ S, (1 + θ.ratio m)) := by
      rw [Real.log_prod]
      intro m hm
      exact ne_of_gt (by linarith [θ.ratio_nonneg m])

end AbelianZetaParameters

end

end GaloisForLFunctions.HTGeometry
