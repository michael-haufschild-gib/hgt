import GaloisForLFunctions.RHTower.ZetaChiNegativeGradeStationary

open Complex MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Explicit main value for a signed nonzero chi grade. -/
def chiGradeStationaryMain (k : ℤ) (a : ℝ) : ℂ :=
  ((|(k : ℝ)|⁻¹ * Real.sqrt (2 * Real.pi * (|(k : ℝ)| * a)) : ℝ) : ℂ) *
    bourgainOscillation ((k : ℝ) * a +
      ((k : ℝ) - (k : ℝ) / |(k : ℝ)|) * (Real.pi / 4))

/-- Full signed-grade stationary remainder, with no coefficient cost suppressed. -/
def chiGradeStationaryError (k : ℤ) (a h : ℝ) : ℝ :=
  78 * |(k : ℝ)| + 4 * |(k : ℝ)| * h ^ 4 / a ^ 2 + 40 * a / (|(k : ℝ)| * h)

theorem norm_integral_zetaChi_signed_grade_stationary_le {k : ℤ} (hk : k ≠ 0)
    {a h l u : ℝ} (ha : 8 ≤ a) (hh : 0 < h) (hha : h ≤ a / 2)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a) :
    ‖(∫ t in l..u, zetaChi (linePt t) ^ k *
        bourgainOscillation ((k : ℝ) * t * Real.log (a / (2 * Real.pi)))) -
      chiGradeStationaryMain k a‖ ≤ chiGradeStationaryError k a h := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · have hn : 0 < n := by omega
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simpa only [chiGradeStationaryMain, chiGradeStationaryError, Int.cast_natCast,
      zpow_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n), div_self hnR] using
      norm_integral_zetaChi_positive_grade_stationary_le n hn ha hh hha hl hlh hhu hu
  · have hn : 0 < n := by omega
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have he : -(n : ℝ) * a + (-(n : ℝ) - -1) * (Real.pi / 4) =
        -((n : ℝ) * a + ((n : ℝ) - 1) * (Real.pi / 4)) := by ring
    simpa only [chiGradeStationaryMain, chiGradeStationaryError, Int.cast_neg,
      Int.cast_natCast, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n), neg_div,
      div_self hnR, he] using
      norm_integral_zetaChi_negative_grade_stationary_le n hn ha hh hha hl hlh hhu hu

private theorem continuous_chi_signed_saddle (k : ℤ) (a : ℝ) :
    Continuous (fun t : ℝ => zetaChi (linePt t) ^ k *
      bourgainOscillation ((k : ℝ) * t * Real.log (a / (2 * Real.pi)))) := by
  simp_rw [zetaChi_line_eq_exp_neg_two_theta, ← Complex.exp_int_mul]
  unfold bourgainOscillation
  have hθ : Continuous gammaHardyTheta := differentiable_gammaHardyTheta.continuous
  fun_prop

private theorem integral_chi_signed_finite_sum {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (k : ι → ℤ) (a : ι → ℝ) (l u : ℝ) :
    (∫ t in l..u, ∑ j ∈ S, c j * (zetaChi (linePt t) ^ k j *
      bourgainOscillation ((k j : ℝ) * t * Real.log (a j / (2 * Real.pi))))) =
      ∑ j ∈ S, c j * ∫ t in l..u, zetaChi (linePt t) ^ k j *
        bourgainOscillation ((k j : ℝ) * t * Real.log (a j / (2 * Real.pi))) := by
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    ((continuous_chi_signed_saddle (k j) (a j)).const_mul (c j)).intervalIntegrable l u)]
  simp_rw [intervalIntegral.integral_const_mul]

/-- Finite mixed positive and negative chi grades retain their signed
stationary main values and every coefficient-weighted error. -/
theorem norm_integral_zetaChi_mixed_grade_stationary_transform_le {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (k : ι → ℤ) (a h : ι → ℝ) (l u : ℝ)
    (hS : ∀ j ∈ S, k j ≠ 0 ∧ 8 ≤ a j ∧ 0 < h j ∧ h j ≤ a j / 2 ∧
      a j / 2 ≤ l ∧ l ≤ a j - h j ∧ a j + h j ≤ u ∧ u ≤ 2 * a j) :
    ‖(∫ t in l..u, ∑ j ∈ S, c j * (zetaChi (linePt t) ^ k j *
        bourgainOscillation ((k j : ℝ) * t * Real.log (a j / (2 * Real.pi))))) -
      ∑ j ∈ S, c j * chiGradeStationaryMain (k j) (a j)‖ ≤
      ∑ j ∈ S, ‖c j‖ * chiGradeStationaryError (k j) (a j) (h j) := by
  rw [integral_chi_signed_finite_sum, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  obtain ⟨hk, ha, hh, hha, hl, hlh, hhu, hu⟩ := hS j hj
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_zetaChi_signed_grade_stationary_le hk ha hh hha hl hlh hhu hu)
    (norm_nonneg _)

/-- Full finite nonzero-grade support: every unselected saddle or endpoint
term pays its actual oscillatory cost. -/
theorem norm_integral_zetaChi_selected_mixed_grade_transform_le {ι : Type*} [DecidableEq ι]
    (R S : Finset ι) (hsub : S ⊆ R) (c : ι → ℂ) (k : ι → ℤ) (a h : ι → ℝ)
    {T : ℝ} (hT : 4 ≤ T) (hk : ∀ j ∈ R, k j ≠ 0)
    (hS : ∀ j ∈ S, 8 ≤ a j ∧ 0 < h j ∧ h j ≤ a j / 2 ∧
      a j / 2 ≤ T ∧ T ≤ a j - h j ∧ a j + h j ≤ 2 * T ∧ 2 * T ≤ 2 * a j) :
    ‖(∫ t in T..(2 * T), ∑ j ∈ R, c j * (zetaChi (linePt t) ^ k j *
        bourgainOscillation ((k j : ℝ) * t * Real.log (a j / (2 * Real.pi))))) -
      ∑ j ∈ S, c j * chiGradeStationaryMain (k j) (a j)‖ ≤
      (∑ j ∈ S, ‖c j‖ * chiGradeStationaryError (k j) (a j) (h j)) +
      ∑ j ∈ R \ S, ‖c j‖ * (6 / Real.sqrt (|(k j : ℝ)| / (100 * T))) := by
  let J (U : Finset ι) : ℂ := ∫ t in T..(2 * T), ∑ j ∈ U, c j *
    (zetaChi (linePt t) ^ k j *
      bourgainOscillation ((k j : ℝ) * t * Real.log (a j / (2 * Real.pi))))
  let M : ℂ := ∑ j ∈ S, c j * chiGradeStationaryMain (k j) (a j)
  have hsel := norm_integral_zetaChi_mixed_grade_stationary_transform_le S c k a h T (2 * T)
    (fun j hj => ⟨hk j (hsub hj), hS j hj⟩)
  have hsplit : J R = J (R \ S) + J S := by
    dsimp only [J]
    simp_rw [integral_chi_signed_finite_sum]
    exact (Finset.sum_sdiff hsub).symm
  have htail : ‖J (R \ S)‖ ≤
      ∑ j ∈ R \ S, ‖c j‖ * (6 / Real.sqrt (|(k j : ℝ)| / (100 * T))) := by
    dsimp only [J]
    rw [integral_chi_signed_finite_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have he : (fun t : ℝ => zetaChi (linePt t) ^ k j *
        bourgainOscillation ((k j : ℝ) * t * Real.log (a j / (2 * Real.pi)))) =
        fun t : ℝ => zetaChi (linePt t) ^ k j *
          Complex.exp (((((k j : ℝ) * Real.log (a j / (2 * Real.pi))) * t : ℝ) : ℂ) * I) := by
      funext t
      unfold bourgainOscillation
      congr 1
      congr 1
      push_cast
      ring
    rw [he]
    exact norm_integral_zetaChi_line_zpow_mul_exp_le hT le_rfl (by linarith) le_rfl
      (hk j (Finset.mem_sdiff.mp hj).1) _
  change ‖J R - M‖ ≤ _
  rw [hsplit]
  calc
    _ = ‖J (R \ S) + (J S - M)‖ := by congr 1; ring
    _ ≤ ‖J (R \ S)‖ + ‖J S - M‖ := norm_add_le _ _
    _ ≤ (∑ j ∈ R \ S, ‖c j‖ * (6 / Real.sqrt (|(k j : ℝ)| / (100 * T)))) +
        (∑ j ∈ S, ‖c j‖ * chiGradeStationaryError (k j) (a j) (h j)) :=
      add_le_add htail hsel
    _ = _ := by ring

end RHTower
