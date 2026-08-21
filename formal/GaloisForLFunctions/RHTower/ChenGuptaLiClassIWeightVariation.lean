/-
# Chen--Gupta--Li Class-I finite weight variation

Proves the literal positive real Class-I weight is nonincreasing on its
zero-extended finite dyadic sequence.  Its Abel variation therefore telescopes
exactly, yielding a closed bound by a maximum common-oscillatory prefix.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIAbelSpecialization

open Complex

noncomputable section

namespace RHTower

/-- The zero-extended literal Class-I weight decreases at every natural step. -/
theorem cglShiftedTailDyadicRealWeightSequence_step
    (N : ℕ) (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (k : ℕ) :
    cglShiftedTailDyadicRealWeightSequence N s x (k + 1) ≤
      cglShiftedTailDyadicRealWeightSequence N s x k := by
  by_cases hk1 : k + 1 < N
  · have hk : k < N := by omega
    simp only [cglShiftedTailDyadicRealWeightSequence, dif_pos hk1, dif_pos hk]
    unfold cglShiftedTailDyadicRealWeight cglCharacterDyadicIndex
    have hbasepos : (0 : ℝ) < (N + k + 1 : ℕ) := by positivity
    have hbasele : ((N + k + 1 : ℕ) : ℝ) ≤ ((N + (k + 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N + k + 1 ≤ N + (k + 1) + 1)
    have hre : 0 ≤ s.1.re := by linarith [s.2]
    have hpow : ((N + (k + 1) + 1 : ℕ) : ℝ) ^ (-s.1.re) ≤
        ((N + k + 1 : ℕ) : ℝ) ^ (-s.1.re) :=
      Real.rpow_le_rpow_of_nonpos hbasepos hbasele (by linarith)
    have harg : -(((N + (k + 1) + 1 : ℕ) : ℝ) * x.1) ≤
        -(((N + k + 1 : ℕ) : ℝ) * x.1) := by
      nlinarith [x.2]
    have hexp : Real.exp (-(((N + (k + 1) + 1 : ℕ) : ℝ) * x.1)) ≤
        Real.exp (-(((N + k + 1 : ℕ) : ℝ) * x.1)) :=
      Real.exp_le_exp.mpr harg
    exact mul_le_mul hpow hexp (by positivity) (by positivity)
  · by_cases hk : k < N
    · simp only [cglShiftedTailDyadicRealWeightSequence, dif_neg hk1, dif_pos hk]
      unfold cglShiftedTailDyadicRealWeight
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.exp_pos _).le
    · simp [cglShiftedTailDyadicRealWeightSequence, hk, hk1]

/-- The literal zero-extended Class-I weight is antitone. -/
theorem cglShiftedTailDyadicRealWeightSequence_antitone
    (N : ℕ) (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    Antitone (cglShiftedTailDyadicRealWeightSequence N s x) :=
  antitone_nat_of_succ_le (cglShiftedTailDyadicRealWeightSequence_step N s x)

/-- Exact total variation of CGL's finite Class-I real weight. -/
theorem cglShiftedTailDyadicRealWeightSequence_variation
    (N : ℕ) (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    ∑ k ∈ Finset.range (N - 1),
      |cglShiftedTailDyadicRealWeightSequence N s x (k + 1) -
        cglShiftedTailDyadicRealWeightSequence N s x k| =
      cglShiftedTailDyadicRealWeightSequence N s x 0 -
        cglShiftedTailDyadicRealWeightSequence N s x (N - 1) := by
  calc
    ∑ k ∈ Finset.range (N - 1),
        |cglShiftedTailDyadicRealWeightSequence N s x (k + 1) -
          cglShiftedTailDyadicRealWeightSequence N s x k| =
      ∑ k ∈ Finset.range (N - 1),
        (cglShiftedTailDyadicRealWeightSequence N s x k -
          cglShiftedTailDyadicRealWeightSequence N s x (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hstep := cglShiftedTailDyadicRealWeightSequence_step N s x k
        rw [abs_of_nonpos (by linarith)]
        ring
    _ = _ := Finset.sum_range_sub' _ _

/-- The literal finite Class-I weight variation is at most its initial weight. -/
theorem cglShiftedTailDyadicRealWeightSequence_variation_le_initial
    (N : ℕ) (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    ∑ k ∈ Finset.range (N - 1),
      |cglShiftedTailDyadicRealWeightSequence N s x (k + 1) -
        cglShiftedTailDyadicRealWeightSequence N s x k| ≤
      cglShiftedTailDyadicRealWeightSequence N s x 0 := by
  rw [cglShiftedTailDyadicRealWeightSequence_variation]
  have hlast : 0 ≤ cglShiftedTailDyadicRealWeightSequence N s x (N - 1) := by
    by_cases hlast : N - 1 < N
    · simp only [cglShiftedTailDyadicRealWeightSequence, dif_pos hlast]
      unfold cglShiftedTailDyadicRealWeight
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.exp_pos _).le
    · simp [cglShiftedTailDyadicRealWeightSequence, hlast]
  linarith

/-- Every literal zero-extended Class-I real weight is nonnegative. -/
theorem cglShiftedTailDyadicRealWeightSequence_nonneg
    (N : ℕ) (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (k : ℕ) :
    0 ≤ cglShiftedTailDyadicRealWeightSequence N s x k := by
  by_cases hk : k < N
  · simp only [cglShiftedTailDyadicRealWeightSequence, dif_pos hk]
    unfold cglShiftedTailDyadicRealWeight
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  · simp [cglShiftedTailDyadicRealWeightSequence, hk]

/-- Certified maximum of all partial norms of the common oscillatory sequence. -/
def cglShiftedTailDyadicPrefixNormMaximum (X N q : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) : ℝ :=
  (Finset.range (N + 1)).sup'
    ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun K => ‖cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) K‖)

/-- Every certified prefix norm is bounded by the finite common maximum. -/
theorem cglShiftedTailDyadicPartialNorm_le_prefixNormMaximum
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (K : Fin (N + 1)) :
    ‖cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) K.1‖ ≤
      cglShiftedTailDyadicPrefixNormMaximum X N q χ s := by
  unfold cglShiftedTailDyadicPrefixNormMaximum
  apply Finset.le_sup' (fun K =>
    ‖cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) K‖)
  exact Finset.mem_range.mpr K.2

/-- Abel plus the exact monotone variation bound controls the literal Class-I
weighted block by initial weight times a common-oscillatory prefix maximum. -/
theorem norm_cglShiftedTailDyadicWeightedBlock_le_initial_mul_prefixNormMaximum
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    ‖∑ j : Fin N, cglShiftedTailDyadicOscillatoryTerm X N q χ s j *
      (cglShiftedTailDyadicRealWeight N s x j : ℂ)‖ ≤
      cglShiftedTailDyadicRealWeightSequence N s x 0 *
        cglShiftedTailDyadicPrefixNormMaximum X N q χ s := by
  calc
    ‖∑ j : Fin N, cglShiftedTailDyadicOscillatoryTerm X N q χ s j *
        (cglShiftedTailDyadicRealWeight N s x j : ℂ)‖ ≤
      |cglShiftedTailDyadicRealWeightSequence N s x (N - 1)| *
        ‖cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) N‖ +
        ∑ k ∈ Finset.range (N - 1),
          |cglShiftedTailDyadicRealWeightSequence N s x (k + 1) -
            cglShiftedTailDyadicRealWeightSequence N s x k| *
            ‖cglComplexPartialSum
              (cglShiftedTailDyadicOscillatorySequence X N q χ s) (k + 1)‖ :=
      norm_cglShiftedTailDyadicWeightedBlock_le_abelEnvelope X N q χ s x
    _ ≤ cglShiftedTailDyadicRealWeightSequence N s x (N - 1) *
        cglShiftedTailDyadicPrefixNormMaximum X N q χ s +
        ∑ k ∈ Finset.range (N - 1),
          |cglShiftedTailDyadicRealWeightSequence N s x (k + 1) -
            cglShiftedTailDyadicRealWeightSequence N s x k| *
            cglShiftedTailDyadicPrefixNormMaximum X N q χ s := by
      apply add_le_add
      · rw [abs_of_nonneg (cglShiftedTailDyadicRealWeightSequence_nonneg N s x (N - 1))]
        exact mul_le_mul_of_nonneg_left
          (cglShiftedTailDyadicPartialNorm_le_prefixNormMaximum X N q χ s
            ⟨N, by omega⟩)
          (cglShiftedTailDyadicRealWeightSequence_nonneg N s x (N - 1))
      · apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (cglShiftedTailDyadicPartialNorm_le_prefixNormMaximum X N q χ s
            ⟨k + 1, by
              rw [Finset.mem_range] at hk
              omega⟩)
          (abs_nonneg _)
    _ = (cglShiftedTailDyadicRealWeightSequence N s x (N - 1) +
        ∑ k ∈ Finset.range (N - 1),
          |cglShiftedTailDyadicRealWeightSequence N s x (k + 1) -
            cglShiftedTailDyadicRealWeightSequence N s x k|) *
          cglShiftedTailDyadicPrefixNormMaximum X N q χ s := by
      rw [add_mul, Finset.sum_mul]
    _ = _ := by
      rw [cglShiftedTailDyadicRealWeightSequence_variation]
      ring

end RHTower
