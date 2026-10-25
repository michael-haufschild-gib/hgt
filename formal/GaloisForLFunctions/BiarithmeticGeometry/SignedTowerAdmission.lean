import GaloisForLFunctions.BiarithmeticGeometry.PrimeFivePaymentCriterion
import GaloisForLFunctions.BiarithmeticGeometry.PronicEnergyDomain
import GaloisForLFunctions.BiarithmeticGeometry.PaidSourcePerturbations

/-!
# The exact admission radius of signed geometric towers

The actual centered tower is a nonzero scalar multiple of its signed digit
row. Digit variance identifies its energy domain with the geometric series
of ratio `a^2/5`, including negative parameters and both critical endpoints.
-/

noncomputable section
open Finset
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Every real mean-summable tower is paid exactly inside the square-root radius. -/
theorem receiverBounded_fiveTower_abs_iff (a : ℝ) (ha : |a| < 5) :
    ReceiverBounded (localFactorInverse 5 a) ↔ |a| < Real.sqrt 5 := by
  by_cases ha0 : a = 0
  · subst a
    have hs : |(0 : ℝ)| < Real.sqrt 5 := by
      rw [abs_zero]
      exact Real.sqrt_pos.mpr (by norm_num)
    exact iff_of_true
      (receiverBounded_of_criticalWiener _
        ((criticalWiener_localFactorInverse_iff (by norm_num : Nat.Prime 5) 0).mpr hs)) hs
  · have ha5 : a < 5 := (le_abs_self a).trans_lt ha
    have hscalar : -(a / (5 - a)) ≠ 0 :=
      neg_ne_zero.mpr (div_ne_zero ha0 (sub_pos.mpr ha5).ne')
    have hrow : weightCenteredPrefix (localFactorInverse 5 a)
        (∑' d : ℕ, localFactorInverse 5 a d / d) =
        fun n => -(a / (5 - a)) * fiveWeightedDigitRow (fun l => a ^ l) n := by
      funext n
      rw [fiveTower_actualPrefix_eq_digitRow a ha, fiveWeightedDigitRow_geometric]
    rw [receiverBounded_iff_summable_pronicCellEnergy,
      ← bounded_pronicNorm_iff_summable, hrow, bounded_pronicNorm_smul_iff _ hscalar,
      bounded_fiveWeightedDigitRow_pronicNorm_iff]
    have he (l : ℕ) : (a ^ l) ^ 2 / (5 : ℝ) ^ l = (a ^ 2 / 5) ^ l := by
      rw [div_pow, ← pow_mul, Nat.mul_comm l 2, pow_mul]
    simp only [he]
    rw [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ a ^ 2 / 5), div_lt_one (by norm_num : (0 : ℝ) < 5)]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hp := Real.sqrt_nonneg (5 : ℝ)
    constructor
    · intro h
      by_contra hn
      have hle := le_of_not_gt hn
      nlinarith only [h, hle, hs, hp, sq_abs a, abs_nonneg a]
    · intro h
      nlinarith only [h, hs, hp, sq_abs a, abs_nonneg a]

/-- Flipping the single-prime sign preserves admission on the full mean-convergence interval. -/
theorem receiverBounded_fiveTower_neg_iff (a : ℝ) (ha : |a| < 5) :
    ReceiverBounded (localFactorInverse 5 (-a)) ↔ ReceiverBounded (localFactorInverse 5 a) := by
  rw [receiverBounded_fiveTower_abs_iff (-a) (by simpa only [abs_neg] using ha),
    receiverBounded_fiveTower_abs_iff a ha, abs_neg]

/-- The negative critical tower is unpaid, just as the positive critical tower is. -/
theorem not_receiverBounded_negative_critical_fiveTower :
    ¬ ReceiverBounded (localFactorInverse 5 (-Real.sqrt 5)) := by
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have ha : |-Real.sqrt 5| < 5 := by
    rw [abs_neg, abs_of_pos hs]
    nlinarith only [hs, hs2]
  rw [receiverBounded_fiveTower_abs_iff _ ha, abs_neg, abs_of_pos hs]
  exact lt_irrefl _

end GaloisForLFunctions.BiarithmeticGeometry
