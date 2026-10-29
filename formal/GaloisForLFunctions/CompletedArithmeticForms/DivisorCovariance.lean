import GaloisForLFunctions.CompletedArithmeticForms.DirichletSchurCost
import GaloisForLFunctions.RHTower.EulerDeletionAveragedDivisorCovariance

/-!
# Cyclotomic coercivity of accumulated divisor errors

Dividing the coefficient at `j` by `j` identifies the completed cyclotomic Gram with
the exact maximum-index covariance of accumulation. Its positive remainder gives a
simultaneous bound for the weighted coefficient square mass and weighted total mass.
The Euler-deletion specialization keeps the complete drift and infinite tail.
-/

noncomputable section

open Finset Filter Topology

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
  · rw [min_eq_right (by exact_mod_cast hkj), max_eq_left hkj]
    push_cast
    field_simp

/-- The exact accumulated energy includes a positive cyclic remainder. -/
theorem cumulativeEnergy_completion (c : ℕ → ℝ) (T : ℕ) :
    4 * cumulativeEnergy c T =
      (∑ j ∈ Icc 1 T, c j / j) ^ 2 + (∑ j ∈ Icc 1 T, (c j / j) ^ 2) +
        cyclotomicRemainder (T + 1) (fun j => c j / j) / ((T : ℝ) + 1) := by
  have h := divisorGramEnergy_completion (Nat.succ_pos T) (fun j => c j / j)
  rw [divisorGramEnergy_eq_cumulativeEnergy, Ico_one_succ] at h
  push_cast at h
  have hT0 : (T : ℝ) + 1 ≠ 0 := by positivity
  apply mul_right_cancel₀ hT0
  rw [add_mul, div_mul_cancel₀ _ hT0]
  nlinarith only [h]

/-- Accumulation controls both weighted coefficient mass and weighted square mass. -/
theorem cumulativeEnergy_coercive (c : ℕ → ℝ) (T : ℕ) :
    (∑ j ∈ Icc 1 T, c j / j) ^ 2 + (∑ j ∈ Icc 1 T, (c j / j) ^ 2) ≤
      4 * cumulativeEnergy c T := by
  rw [cumulativeEnergy_completion]
  exact le_add_of_nonneg_right
    (div_nonneg (cyclotomicRemainder_nonneg _ _) (by positivity))

/-- The dual cost of temporal covariance is local variation of the weighted coupling. -/
theorem cumulativeEnergy_schur_bound (c b : ℕ → ℝ) (T : ℕ) :
    2 * (∑ j ∈ Icc 1 T, c j * b j) - cumulativeEnergy c T ≤
      dirichletEnergy (T + 1) (interiorExtension (T + 1) (fun j => (j : ℝ) * b j)) := by
  have hQ : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have h := bridgeSchur_bound (Nat.succ_pos T) (fun j => c j / j)
    (fun j => ((T : ℝ) + 1) * ((j : ℝ) * b j))
  rw [divisorGramEnergy_eq_cumulativeEnergy, Ico_one_succ, bridgeSchurCost_mul] at h
  have hpair : (∑ j ∈ Icc 1 T, (c j / j) * (((T : ℝ) + 1) * ((j : ℝ) * b j))) =
      ((T : ℝ) + 1) * ∑ j ∈ Icc 1 T, c j * b j := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hj0 : (j : ℝ) ≠ 0 := by
      exact_mod_cast (show j ≠ 0 by have := (mem_Icc.mp hj).1; omega)
    field_simp
  rw [hpair, bridgeSchurCost] at h
  push_cast at h
  have hcost (D : ℝ) : ((T : ℝ) + 1) ^ 2 * (D / ((T : ℝ) + 1)) =
      ((T : ℝ) + 1) * D := by field_simp
  rw [hcost] at h
  by_contra hn
  have hp := mul_pos hQ (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [h, hp]

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

private theorem hasSum_carrier_tail (T : ℕ) :
    HasSum (fun i : ℕ => 1 / (((i : ℝ) + T + 1) * ((i : ℝ) + T + 2)))
      (1 / ((T : ℝ) + 1)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  have hden : Tendsto (fun i : ℕ => (i : ℝ) + T + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun i : ℕ => ((i : ℝ) + T + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hlim : Tendsto (fun i : ℕ => 1 / ((T : ℝ) + 1) - ((i : ℝ) + T + 1)⁻¹)
      atTop (𝓝 (1 / ((T : ℝ) + 1) - 0)) := tendsto_const_nhds.sub hinv
  convert hlim using 1
  · funext N
    have hstep (i : ℕ) : 1 / (((i : ℝ) + T + 1) * ((i : ℝ) + T + 2)) =
        1 / ((i : ℝ) + T + 1) - 1 / (((i + 1 : ℕ) : ℝ) + T + 1) := by
      have h0 : (i : ℝ) + T + 1 ≠ 0 := by positivity
      have h1 : (i : ℝ) + T + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    simp_rw [hstep]
    rw [Finset.sum_range_sub']
    simp only [Nat.cast_zero, zero_add, one_div]
  · simp

private theorem averaged_error_abs_le {X M : ℕ} (hX : 1 ≤ X) (hXM : X < M) (n : ℕ) :
    |1 - modular X M n| ≤ (M : ℝ) + 1 := by
  have h := (abs_sub (1 : ℝ) (modular X M n)).trans
    (add_le_add le_rfl (abs_modular_le hX hXM n))
  simpa only [abs_one, add_comm] using h

/-- The literal omitted coordinate tail has a uniform cutoff-dependent allowance. -/
theorem fullErrorEnergy_tail_le {X M : ℕ} (hX : 1 ≤ X) (hXM : X < M) (T : ℕ) :
    (∑' i : ℕ, (1 - modular X M (i + T + 1)) ^ 2 /
      ((((i + T : ℕ) : ℝ) + 1) * (((i + T : ℕ) : ℝ) + 2))) ≤
        ((M : ℝ) + 1) ^ 2 / ((T : ℝ) + 1) := by
  have htail : Summable (fun i : ℕ => (1 - modular X M (i + T + 1)) ^ 2 /
      ((((i + T : ℕ) : ℝ) + 1) * (((i + T : ℕ) : ℝ) + 2))) :=
    (hasSum_fullErrorEnergy hX hXM).summable.comp_injective
      (show Function.Injective (fun i : ℕ => i + T) from fun _ _ h => Nat.add_right_cancel h)
  have hmajor := (hasSum_carrier_tail T).mul_left (((M : ℝ) + 1) ^ 2)
  have hpoint (i : ℕ) : (1 - modular X M (i + T + 1)) ^ 2 /
      ((((i + T : ℕ) : ℝ) + 1) * (((i + T : ℕ) : ℝ) + 2)) ≤
      ((M : ℝ) + 1) ^ 2 * (1 / (((i : ℝ) + T + 1) * ((i : ℝ) + T + 2))) := by
    have hsq : (1 - modular X M (i + T + 1)) ^ 2 ≤ ((M : ℝ) + 1) ^ 2 := by
      simpa only [sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) (averaged_error_abs_le hX hXM (i + T + 1)) 2
    simpa only [Nat.cast_add, div_eq_mul_inv, one_mul] using
      div_le_div_of_nonneg_right hsq
        (show (0 : ℝ) ≤ (((i + T : ℕ) : ℝ) + 1) * (((i + T : ℕ) : ℝ) + 2) by positivity)
  have h := Summable.tsum_le_tsum hpoint htail hmajor.summable
  rw [hmajor.tsum_eq] at h
  simpa only [mul_one_div] using h

/-- Finite covariance approximates the complete actual energy with an explicit joint horizon error. -/
theorem fullErrorEnergy_truncation_bounds {X M : ℕ}
    (hX : 1 ≤ X) (hXM : X < M) (T : ℕ) :
    0 ≤ fullErrorEnergy X M - cumulativeEnergy (errorIncrement X M) T ∧
      fullErrorEnergy X M - cumulativeEnergy (errorIncrement X M) T ≤
        ((M : ℝ) + 1) ^ 2 / ((T : ℝ) + 1) := by
  have hsplit := fullErrorEnergy_eq_covariance_add_tail hX hXM T
  rw [← cumulativeEnergy_eq_covariance] at hsplit
  have hnonneg : (0 : ℝ) ≤ ∑' i : ℕ, (1 - modular X M (i + T + 1)) ^ 2 /
      ((((i + T : ℕ) : ℝ) + 1) * (((i + T : ℕ) : ℝ) + 2)) :=
    tsum_nonneg fun i => div_nonneg (sq_nonneg _) (by positivity)
  have hupper := fullErrorEnergy_tail_le hX hXM T
  constructor <;> linarith only [hsplit, hnonneg, hupper]

#print axioms cumulativeEnergy_completion
#print axioms cumulativeEnergy_schur_bound
#print axioms fullErrorEnergy_eq_cyclotomic_add_tail
#print axioms errorIncrement_mass_le_fullErrorEnergy
#print axioms fullErrorEnergy_truncation_bounds

end GaloisForLFunctions.CompletedArithmeticForms
