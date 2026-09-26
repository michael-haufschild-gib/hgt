import GaloisForLFunctions.HTGeometry.RelativeGapCurvature
import GaloisForLFunctions.HTGeometry.ConstitutiveMutationalGenesis
import GaloisForLFunctions.HTGeometry.QuadraticResponseHierarchy

/-!
# Opposite relative-gap directions in two exact recurrence families

The rank-two mutational lineage has strictly increasing relative steps. A positive
geometric-sum quadratic response has strictly decreasing relative steps. Their
Cassini invariants give the exact accelerations at every depth.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators

theorem mutationalLineage_real_pos (n : ℕ) : 0 < (mutationalLineage n : ℝ) := by
  cases n with
  | zero => simp
  | succ n => exact_mod_cast (mutationalLineage_positive_increasing n).1

/-- The expansion signal of the mutational lineage has an exact positive amplitude. -/
theorem mutationalLineage_relativeStep_difference (n : ℕ) :
    relativeStep (mutationalLineage (n + 1)) (mutationalLineage (n + 2)) -
      relativeStep (mutationalLineage n) (mutationalLineage (n + 1)) =
        1 / ((mutationalLineage n : ℝ) * (mutationalLineage (n + 1) : ℝ)) := by
  have hc : (mutationalLineage (n + 2) : ℝ) * (mutationalLineage n : ℝ) -
      (mutationalLineage (n + 1) : ℝ) ^ (2 : ℕ) = 1 := by
    exact_mod_cast mutationalLineage_cassini n
  unfold relativeStep
  field_simp [(mutationalLineage_real_pos n).ne',
    (mutationalLineage_real_pos (n + 1)).ne']
  nlinarith [hc]

theorem mutationalLineage_relativeStep_strictMono :
    StrictMono (fun n => relativeStep (mutationalLineage n) (mutationalLineage (n + 1))) := by
  apply strictMono_nat_of_lt_succ
  intro n
  apply sub_pos.mp
  rw [show n + 1 + 1 = n + 2 by omega, mutationalLineage_relativeStep_difference]
  exact one_div_pos.mpr (mul_pos (mutationalLineage_real_pos n)
    (mutationalLineage_real_pos (n + 1)))

/-- The positive two-root quadratic response is a finite geometric sum. -/
theorem quadraticResponseCoeff_geometric_sum (r : ℝ) (n : ℕ) :
    quadraticResponseCoeff (-(1 + r)) r n = ∑ k ∈ Finset.range (n + 1), r ^ k := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Finset.sum_range_succ]
  | more n h0 h1 =>
    rw [quadraticResponseCoeff_add_two, h0, h1]
    simp only [Finset.sum_range_succ, pow_succ]
    ring

theorem quadraticResponseCoeff_exp_pos (t : ℝ) (n : ℕ) :
    0 < quadraticResponseCoeff (-(1 + Real.exp t)) (Real.exp t) n := by
  rw [quadraticResponseCoeff_geometric_sum]
  exact Finset.sum_pos (fun _ _ => pow_pos (Real.exp_pos t) _)
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n))

/-- A positive quadratic-response hierarchy contracts at every adjacent relative step. -/
theorem quadraticResponseCoeff_exp_relativeStep_difference (t : ℝ) (n : ℕ) :
    let q := quadraticResponseCoeff (-(1 + Real.exp t)) (Real.exp t)
    relativeStep (q (n + 1)) (q (n + 2)) - relativeStep (q n) (q (n + 1)) =
      -(Real.exp t ^ (n + 1)) / (q n * q (n + 1)) := by
  dsimp only
  have hc := quadraticResponseCoeff_cassini (-(1 + Real.exp t)) (Real.exp t) n
  unfold relativeStep
  rw [div_sub_div _ _ (quadraticResponseCoeff_exp_pos t (n + 1)).ne'
    (quadraticResponseCoeff_exp_pos t n).ne']
  congr 1 <;> nlinarith [hc]

theorem quadraticResponseCoeff_exp_relativeStep_strictAnti (t : ℝ) :
    StrictAnti (fun n => relativeStep
      (quadraticResponseCoeff (-(1 + Real.exp t)) (Real.exp t) n)
      (quadraticResponseCoeff (-(1 + Real.exp t)) (Real.exp t) (n + 1))) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  apply sub_neg.mp
  rw [show n + 1 + 1 = n + 2 by omega, quadraticResponseCoeff_exp_relativeStep_difference]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (pow_pos (Real.exp_pos t) _))
    (mul_pos (quadraticResponseCoeff_exp_pos t n) (quadraticResponseCoeff_exp_pos t (n + 1)))

end
end GaloisForLFunctions.HTGeometry
