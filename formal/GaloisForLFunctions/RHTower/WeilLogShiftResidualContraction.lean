import GaloisForLFunctions.RHTower.WeilLogShiftResidualSlope
import GaloisForLFunctions.RHTower.WeilLogShiftFluctuationResidual

/-! A finite variance contraction controls the raw centered mismatch for every cluster. -/

open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalEdgeIndexMean_mem_Icc (r k : ℕ) :
    finiteWeilCanonicalEdgeIndexMean r k ∈ Set.Icc (0 : ℝ) r := by
  constructor
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (Nat.cast_nonneg _)
  · calc
      _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * (r : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (finiteWeilCanonicalEdgeMass_pos r k i).le
        exact_mod_cast (show (i : ℕ) ≤ r by have := i.isLt; omega)
      _ = _ := by rw [← Finset.sum_mul, finiteWeilCanonicalEdgeMass_sum, one_mul]

theorem finiteWeilCanonicalFluctuationResidual_profile_variance (r k : ℕ) :
    finiteWeilCanonicalFluctuationResidual r k =
      ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        (finiteWeilEdgeResidualProfile k (i : ℕ) -
          ∑ j : Fin (r + 1), finiteWeilCanonicalEdgeMass r k j *
            finiteWeilEdgeResidualProfile k (j : ℕ)) ^ 2 := by
  simp_rw [finiteWeilEdgeResidualProfile_at_index,
    finiteWeilCanonicalEdgeLogCorrection_scaled_residual_mean]
  unfold finiteWeilCanonicalFluctuationResidual
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finiteWeilCanonicalFluctuationResidual_variance_contraction (r k : ℕ) :
    finiteWeilCanonicalFluctuationResidual r k ≤
      (2 * ((r + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ^ 2 *
        finiteWeilCanonicalEdgeIndexVariance r k := by
  let C : ℝ := 2 * ((r + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)
  let E : ℝ := finiteWeilCanonicalEdgeIndexMean r k
  let f := fun i : Fin (r + 1) => finiteWeilEdgeResidualProfile k (i : ℕ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE : E ∈ Set.Icc (0 : ℝ) r := finiteWeilCanonicalEdgeIndexMean_mem_Icc r k
  have hcenter := finiteWeil_probability_centering (finiteWeilCanonicalEdgeMass r k) f
    (finiteWeilCanonicalEdgeMass_sum r k) (finiteWeilEdgeResidualProfile k E)
  calc
    _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        (f i - finiteWeilEdgeResidualProfile k E) ^ 2 := by
      rw [finiteWeilCanonicalFluctuationResidual_profile_variance]
      change (∑ i, finiteWeilCanonicalEdgeMass r k i *
        (f i - ∑ j, finiteWeilCanonicalEdgeMass r k j * f j) ^ 2) ≤ _
      rw [hcenter]
      exact sub_le_self _ (sq_nonneg _)
    _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        (C ^ 2 * (((i : ℕ) : ℝ) - E) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : ((i : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) r := by
        constructor
        · positivity
        · exact_mod_cast (show (i : ℕ) ≤ r by have := i.isLt; omega)
      have h := finiteWeilEdgeResidualProfile_lipschitz r k ⟨(i : ℕ), hi⟩ ⟨E, hE⟩
      have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (abs_nonneg _))).mpr h
      rw [mul_pow, sq_abs, sq_abs] at hs
      exact mul_le_mul_of_nonneg_left hs (finiteWeilCanonicalEdgeMass_pos r k i).le
    _ = _ := by
      unfold finiteWeilCanonicalEdgeIndexVariance
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [C, E]
      ring

theorem finiteWeilCanonicalFluctuationResidual_quadratic_variance_bound (r t : ℕ) :
    finiteWeilCanonicalFluctuationResidual r (2 * (r + 1) ^ 2 + t) ≤
      finiteWeilCanonicalEdgeIndexVariance r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ) ^ 2 := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let A : ℝ := ((2 * (r + 1) ^ 2 + t + 2 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : 2 * n / A ≤ 1 / n := by
    apply (div_le_div_iff₀ hA hn).mpr
    dsimp [A, n]
    push_cast
    nlinarith only [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ 2 * n / A)
    (by positivity : 0 ≤ 1 / n)).mpr hc
  calc
    _ ≤ (2 * n / A) ^ 2 * finiteWeilCanonicalEdgeIndexVariance r (2 * (r + 1) ^ 2 + t) :=
      finiteWeilCanonicalFluctuationResidual_variance_contraction r _
    _ ≤ (1 / n) ^ 2 * finiteWeilCanonicalEdgeIndexVariance r (2 * (r + 1) ^ 2 + t) :=
      mul_le_mul_of_nonneg_right hs (finiteWeilCanonicalEdgeIndexVariance_nonneg r _)
    _ = _ := by dsimp [n]; ring

end RHTower
