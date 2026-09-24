import GaloisForLFunctions.RHTower.MobiusGammaHankelMovingRowAbel

open Finset

namespace RHTower

private def halfBlock (M : ℕ) : Finset ℕ := Finset.Ico M (2 * M)

private def halfBlockCoeff (M i : ℕ) : ℝ :=
  if i ∈ halfBlock M then 1 else 0

private theorem halfBlock_card (M : ℕ) : (halfBlock M).card = M := by
  simp [halfBlock]
  omega

private theorem halfBlock_subset_range (M : ℕ) :
    halfBlock M ⊆ Finset.range (2 * M) := by
  intro i hi
  exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2

private theorem halfBlock_harmonicPrefix_le_one (M k : ℕ) :
    (∑ i ∈ Finset.range k,
      halfBlockCoeff M i / (((i + 1 : ℕ) : ℝ))) ≤ 1 := by
  let S := (Finset.range k).filter (fun i => i ∈ halfBlock M)
  have hSsub : S ⊆ halfBlock M := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hcard : S.card ≤ M := by
    rw [← halfBlock_card M]
    exact Finset.card_le_card hSsub
  have hden (i : ℕ) (hi : i ∈ S) :
      (1 : ℝ) / (((i + 1 : ℕ) : ℝ)) ≤ 1 / ((M + 1 : ℕ) : ℝ) := by
    have hMi : M ≤ i := (Finset.mem_Ico.mp (hSsub hi)).1
    have hMiR : (((M + 1 : ℕ) : ℝ)) ≤ (((i + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.add_le_add_right hMi 1
    exact one_div_le_one_div_of_le (by positivity) hMiR
  have hsum :
      (∑ i ∈ Finset.range k,
        halfBlockCoeff M i / (((i + 1 : ℕ) : ℝ))) =
      ∑ i ∈ S, (1 : ℝ) / (((i + 1 : ℕ) : ℝ)) := by
    simp only [S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i ∈ halfBlock M <;> simp [halfBlockCoeff, h]
  rw [hsum]
  calc
    (∑ i ∈ S, (1 : ℝ) / (((i + 1 : ℕ) : ℝ))) ≤
        ∑ _i ∈ S, (1 : ℝ) / (((M + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hden i hi
    _ = (S.card : ℝ) / (((M + 1 : ℕ) : ℝ)) := by simp [div_eq_mul_inv]
    _ ≤ (M : ℝ) / (((M + 1 : ℕ) : ℝ)) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.le_succ M

private theorem halfBlock_harmonicPrefix_abs_le_one (M k : ℕ) :
    |∑ i ∈ Finset.range k,
      halfBlockCoeff M i / (((i + 1 : ℕ) : ℝ))| ≤ 1 := by
  rw [abs_of_nonneg]
  · exact halfBlock_harmonicPrefix_le_one M k
  · apply Finset.sum_nonneg
    intro i hi
    unfold halfBlockCoeff
    split_ifs <;> positivity

private theorem halfBlock_energy_eq (M : ℕ) :
    finiteGammaHankelEnergy (halfBlockCoeff M) (2 * M) 1 =
      ∑ i ∈ halfBlock M, ∑ j ∈ halfBlock M,
        (1 : ℝ) / (((i + j + 2 : ℕ) : ℝ)) := by
  unfold finiteGammaHankelEnergy
  simp only [Real.Gamma_one, Real.rpow_one, one_mul]
  have hfilt : (Finset.range (2 * M)).filter (fun i => i ∈ halfBlock M) =
      halfBlock M := by
    ext i
    simp [halfBlock_subset_range M]
  have hpoint (i j : ℕ) :
      halfBlockCoeff M i * halfBlockCoeff M j /
          (((i + j + 2 : ℕ) : ℝ)) =
        if i ∈ halfBlock M then
          (if j ∈ halfBlock M then (1 : ℝ) / (((i + j + 2 : ℕ) : ℝ)) else 0)
        else 0 := by
    by_cases hi : i ∈ halfBlock M <;>
      by_cases hj : j ∈ halfBlock M <;>
      simp [halfBlockCoeff, hi, hj]
  simp_rw [hpoint]
  calc
    (∑ i ∈ Finset.range (2 * M), ∑ j ∈ Finset.range (2 * M),
        if i ∈ halfBlock M then
          (if j ∈ halfBlock M then (1 : ℝ) / (((i + j + 2 : ℕ) : ℝ)) else 0)
        else 0) =
      ∑ i ∈ Finset.range (2 * M), if i ∈ halfBlock M then
        (∑ j ∈ Finset.range (2 * M),
          if j ∈ halfBlock M then (1 : ℝ) / (((i + j + 2 : ℕ) : ℝ)) else 0)
        else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases his : i ∈ halfBlock M <;> simp [his]
    _ = ∑ i ∈ Finset.range (2 * M), if i ∈ halfBlock M then
        (∑ j ∈ (Finset.range (2 * M)).filter (fun j => j ∈ halfBlock M),
          (1 : ℝ) / (((i + j + 2 : ℕ) : ℝ)))
        else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases his : i ∈ halfBlock M <;> simp [his, Finset.sum_filter]
    _ = ∑ i ∈ (Finset.range (2 * M)).filter (fun i => i ∈ halfBlock M),
          ∑ j ∈ (Finset.range (2 * M)).filter (fun j => j ∈ halfBlock M),
            (1 : ℝ) / (((i + j + 2 : ℕ) : ℝ)) := by
          rw [Finset.sum_filter]
    _ = _ := by rw [hfilt]

private theorem halfBlock_energy_ge (M : ℕ) (hM : 0 < M) :
    (M : ℝ) / 4 ≤
      ∑ i ∈ halfBlock M, ∑ j ∈ halfBlock M,
        (1 : ℝ) / (((i + j + 2 : ℕ) : ℝ)) := by
  have hterm (i j : ℕ) (hi : i ∈ halfBlock M) (hj : j ∈ halfBlock M) :
      (1 : ℝ) / ((4 * M : ℕ) : ℝ) ≤
        1 / (((i + j + 2 : ℕ) : ℝ)) := by
    have hib := (Finset.mem_Ico.mp hi).2
    have hjb := (Finset.mem_Ico.mp hj).2
    have hden : i + j + 2 ≤ 4 * M := by omega
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hden)
  have hconst :
      (∑ _i ∈ halfBlock M, ∑ _j ∈ halfBlock M,
        (1 : ℝ) / ((4 * M : ℕ) : ℝ)) = (M : ℝ) / 4 := by
    simp [halfBlock_card]
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    field_simp
  rw [← hconst]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact hterm i j hi hj

private theorem exists_unit_harmonic_prefix_linear_gamma_energy_pos
    (M : ℕ) (hM : 0 < M) :
    ∃ a : ℕ → ℝ,
      (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧
      (∀ k, |∑ i ∈ Finset.range k, a i / (((i + 1 : ℕ) : ℝ))| ≤ 1) ∧
      (M : ℝ) / 4 ≤ finiteGammaHankelEnergy a (2 * M) 1 := by
  refine ⟨halfBlockCoeff M, ?_, halfBlock_harmonicPrefix_abs_le_one M, ?_⟩
  · intro i
    unfold halfBlockCoeff
    split_ifs <;> norm_num
  · rw [halfBlock_energy_eq]
    exact halfBlock_energy_ge M hM

/-- A unit harmonic-prefix budget does not give a sublinear Gamma--Hankel
energy ceiling, even for coefficients in `{0,1}`. -/
theorem exists_unit_harmonic_prefix_linear_gamma_energy (M : ℕ) :
    ∃ a : ℕ → ℝ,
      (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧
      (∀ k, |∑ i ∈ Finset.range k, a i / (((i + 1 : ℕ) : ℝ))| ≤ 1) ∧
      (((M + 1 : ℕ) : ℝ)) / 4 ≤
        finiteGammaHankelEnergy a (2 * (M + 1)) 1 := by
  exact exists_unit_harmonic_prefix_linear_gamma_energy_pos
    (M + 1) (Nat.succ_pos M)

end RHTower
