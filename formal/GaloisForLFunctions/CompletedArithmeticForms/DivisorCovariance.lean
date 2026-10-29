import GaloisForLFunctions.CompletedArithmeticForms.CyclotomicCoercivity
import GaloisForLFunctions.RHTower.EulerDeletionAveragedDivisorCovariance

/-!
# Cyclotomic coercivity of accumulated divisor errors

Dividing the coefficient at `j` by `j` identifies the completed cyclotomic Gram with
the exact maximum-index covariance of accumulation. Its positive remainder gives a
simultaneous bound for the weighted coefficient square mass and weighted total mass.
The Euler-deletion specialization keeps the complete drift and infinite tail.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open RHTower.DeletionAveragedDivisor RHTower.DeletionCutoffAverage

private theorem Ico_one_succ (T : ℕ) : Ico 1 (T + 1) = Icc 1 T := by
  ext i
  simp only [mem_Ico, mem_Icc]
  omega

/-- Accumulation is exactly the normalized divisor-conductor completion. -/
theorem divisorGramEnergy_eq_cumulativeEnergy (c : ℕ → ℝ) (T : ℕ) :
    divisorGramEnergy (T + 1) (fun j => c j / j) =
      ((T : ℝ) + 1) * cumulativeEnergy c T := by
  rw [divisorGramEnergy_eq_bridge (Nat.succ_pos T), Ico_one_succ,
    cumulativeEnergy_eq_covariance, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hj0 : (j : ℝ) ≠ 0 := by
    exact_mod_cast (show j ≠ 0 by have := (mem_Icc.mp hj).1; omega)
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 by have := (mem_Icc.mp hk).1; omega)
  have hT0 : (T : ℝ) + 1 ≠ 0 := by positivity
  unfold cumulativeKernel
  rcases le_total j k with hjk | hkj
  · rw [min_eq_left (by exact_mod_cast hjk), max_eq_right hjk]
    push_cast
    field_simp
    ring
  · rw [min_eq_right (by exact_mod_cast hkj), max_eq_left hkj]
    push_cast
    field_simp
    ring

/-- The exact accumulated energy includes a positive cyclic remainder. -/
theorem cumulativeEnergy_completion (c : ℕ → ℝ) (T : ℕ) :
    4 * cumulativeEnergy c T =
      (∑ j ∈ Icc 1 T, c j / j) ^ 2 + (∑ j ∈ Icc 1 T, (c j / j) ^ 2) +
        cyclotomicRemainder (T + 1) (fun j => c j / j) / ((T : ℝ) + 1) := by
  have h := divisorGramEnergy_completion (Nat.succ_pos T) (fun j => c j / j)
  rw [divisorGramEnergy_eq_cumulativeEnergy, Ico_one_succ] at h
  push_cast at h
  have hT0 : (T : ℝ) + 1 ≠ 0 := by positivity
  apply (eq_div_iff hT0).mp
  field_simp
  nlinarith only [h]

/-- Accumulation controls both weighted coefficient mass and weighted square mass. -/
theorem cumulativeEnergy_coercive (c : ℕ → ℝ) (T : ℕ) :
    (∑ j ∈ Icc 1 T, c j / j) ^ 2 + (∑ j ∈ Icc 1 T, (c j / j) ^ 2) ≤
      4 * cumulativeEnergy c T := by
  rw [cumulativeEnergy_completion]
  exact le_add_of_nonneg_right
    (div_nonneg (cyclotomicRemainder_nonneg _ _) (by positivity))

/-- The full Euler-deletion energy retains the completed finite arithmetic Gram and its tail. -/
theorem fullErrorEnergy_eq_cyclotomic_add_tail {X M : ℕ}
    (hX : 1 ≤ X) (hXM : X < M) (T : ℕ) :
    fullErrorEnergy X M =
      divisorGramEnergy (T + 1) (fun j => errorIncrement X M j / j) / ((T : ℝ) + 1) +
      ∑' i : ℕ, (1 - modular X M (i + T + 1)) ^ 2 /
        ((((i + T : ℕ) : ℝ) + 1) * (((i + T : ℕ) : ℝ) + 2)) := by
  rw [divisorGramEnergy_eq_cumulativeEnergy, mul_div_cancel_left₀ _ (by positivity),
    cumulativeEnergy_eq_covariance]
  exact fullErrorEnergy_eq_covariance_add_tail hX hXM T

/-- Every finite weighted increment packet is controlled by the actual full error energy. -/
theorem errorIncrement_mass_le_fullErrorEnergy {X M : ℕ}
    (hX : 1 ≤ X) (hXM : X < M) (T : ℕ) :
    (∑ j ∈ Icc 1 T, errorIncrement X M j / j) ^ 2 +
      (∑ j ∈ Icc 1 T, (errorIncrement X M j / j) ^ 2) ≤
        4 * fullErrorEnergy X M := by
  have hfinite := cumulativeEnergy_coercive (errorIncrement X M) T
  have htail : (0 : ℝ) ≤ ∑' i : ℕ, (1 - modular X M (i + T + 1)) ^ 2 /
      ((((i + T : ℕ) : ℝ) + 1) * (((i + T : ℕ) : ℝ) + 2)) :=
    tsum_nonneg fun i => div_nonneg (sq_nonneg _) (by positivity)
  have hsplit := fullErrorEnergy_eq_covariance_add_tail hX hXM T
  rw [← cumulativeEnergy_eq_covariance] at hsplit
  linarith only [hfinite, htail, hsplit]

#print axioms cumulativeEnergy_completion
#print axioms fullErrorEnergy_eq_cyclotomic_add_tail
#print axioms errorIncrement_mass_le_fullErrorEnergy

end GaloisForLFunctions.CompletedArithmeticForms
