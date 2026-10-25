import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheExactPronicCostOfACappedRow
import GaloisForLFunctions.ArithmeticDefectRigidity.WienerCovariancesFollowTheCommonCofactorLimit

/-!
# Origin steps have the max kernel

Resetting the constant row at zero turns its integer dilates into steps.
Telescoping pronic mass gives their exact limiting covariance 1/max(j,k).
-/

section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The constant positive row with its arithmetic origin reset to zero. -/
def originStep (n : ℕ) : ℝ := if n = 0 then 0 else 1

theorem rowDilate_originStep (j : ℕ+) (n : ℕ) :
    rowDilate j originStep n = if (j : ℕ) ≤ n then 1 else 0 := by
  unfold rowDilate originStep
  by_cases hj : (j : ℕ) ≤ n
  · rw [if_pos hj, if_neg (Nat.ne_of_gt (Nat.div_pos hj j.property))]
  · rw [if_neg hj, Nat.div_eq_of_lt (lt_of_not_ge hj), if_pos rfl]

/-- Step-cofactor pairing is precisely a pronic tail. -/
theorem pronicPairing_originSteps (T : ℕ) (j k : ℕ+) :
    pronicPairing T (rowDilate j originStep) (rowDilate k originStep) =
      ∑ n ∈ Icc (max (j : ℕ) (k : ℕ)) T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hcell (n : ℕ) :
      rowDilate j originStep n * rowDilate k originStep n =
        if max (j : ℕ) (k : ℕ) ≤ n then 1 else 0 := by
    rw [rowDilate_originStep, rowDilate_originStep]
    by_cases hj : (j : ℕ) ≤ n <;> by_cases hk : (k : ℕ) ≤ n <;>
      simp only [max_le_iff, hj, hk, and_self, and_false, false_and, if_true, if_false,
        one_mul, zero_mul, mul_zero]
  simp only [pronicPairing, hcell, ite_div, zero_div]
  rw [← sum_filter]
  have hset : {n ∈ Icc 1 T | max (j : ℕ) (k : ℕ) ≤ n} =
      Icc (max (j : ℕ) (k : ℕ)) T := by
    ext n
    simp only [mem_filter, mem_Icc, max_le_iff]
    have hj : 1 ≤ (j : ℕ) := j.property
    omega
  rw [hset]

/-- The origin-step Gram is the Nyman–Beurling max kernel. -/
theorem pronicPairing_originSteps_tendsto (j k : ℕ+) :
    Tendsto (fun T => pronicPairing T (rowDilate j originStep) (rowDilate k originStep))
      atTop (𝓝 (1 / ((max (j : ℕ) (k : ℕ) : ℕ) : ℝ))) := by
  have hinv : Tendsto (fun T : ℕ => 1 / ((T : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_mono (fun (T : ℕ) => (by linarith only : (T : ℝ) ≤ (T : ℝ) + 1))
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlim := (tendsto_const_nhds (x := 1 / ((max (j : ℕ) (k : ℕ) : ℕ) : ℝ))).sub hinv
  rw [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (max (j : ℕ) (k : ℕ))] with T hT
  have hj : 1 ≤ (j : ℕ) := j.property
  rw [pronicPairing_originSteps, sum_Icc_pronic_tail_mass
    (hj.trans (le_max_left _ _)) (hT.trans (Nat.le_succ T))]

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.pronicPairing_originSteps_tendsto
end
end
