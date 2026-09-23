import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherence
import GaloisForLFunctions.HTGeometry.FidelityPhaseRadius

/-!
# Anchored phase energy and fidelity are globally equivalent

For a finite probability-weighted unit-phase packet, fidelity deficit is
globally comparable to squared phase-chord energy from any fixed pivot.  The
lower constant is half the pivot weight; the upper constant is universal.

This lets exact fidelity first-return exponents transfer to target metrics
whose natural coordinates are anchored phase chords.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

theorem projectiveWeightedPivotEnergy_nonneg
    {d : ℕ} (w : Fin d → ℝ) (phase : Fin d → ℂ)
    (hw : ∀ i, 0 ≤ w i) (k : Fin d) :
    0 ≤ projectiveWeightedPivotEnergy w phase k := by
  rw [projectiveWeightedPivotEnergy]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)

/-- Pairwise weighted dispersion is at most four times dispersion from any
fixed pivot. -/
theorem projectiveWeightedPairwiseEnergy_le_four_mul_pivot
    {d : ℕ} (w : Fin d → ℝ) (phase : Fin d → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (k : Fin d) :
    projectiveWeightedPairwiseEnergy w phase ≤
      4 * projectiveWeightedPivotEnergy w phase k := by
  have hchord (i j : Fin d) :
      ‖phase i - phase j‖ ^ (2 : ℕ) ≤
        2 * (‖phase i - phase k‖ ^ (2 : ℕ) + ‖phase j - phase k‖ ^ (2 : ℕ)) := by
    have htri : ‖phase i - phase j‖ ≤
        ‖phase i - phase k‖ + ‖phase j - phase k‖ := by
      calc
        ‖phase i - phase j‖ =
            ‖(phase i - phase k) - (phase j - phase k)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_sub_le _ _
    have hsq : ‖phase i - phase j‖ ^ (2 : ℕ) ≤
        (‖phase i - phase k‖ + ‖phase j - phase k‖) ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htri
    nlinarith [hsq, sq_nonneg
      (‖phase i - phase k‖ - ‖phase j - phase k‖)]
  rw [projectiveWeightedPairwiseEnergy]
  calc
    (∑ i, ∑ j, w i * w j * ‖phase i - phase j‖ ^ (2 : ℕ)) ≤
        ∑ i, ∑ j, w i * w j *
          (2 * (‖phase i - phase k‖ ^ (2 : ℕ) + ‖phase j - phase k‖ ^ (2 : ℕ))) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (hchord i j)
        (mul_nonneg (hw i) (hw j))
    _ = 4 * projectiveWeightedPivotEnergy w phase k := by
      have hsplit (i j : Fin d) :
          w i * w j *
              (2 * (‖phase i - phase k‖ ^ (2 : ℕ) + ‖phase j - phase k‖ ^ (2 : ℕ))) =
            w i * w j * ‖phase i - phase k‖ ^ (2 : ℕ) * 2 +
              w i * w j * ‖phase j - phase k‖ ^ (2 : ℕ) * 2 := by
        ring
      simp_rw [hsplit, Finset.sum_add_distrib]
      have hleft :
          (∑ i, ∑ j, w i * w j * ‖phase i - phase k‖ ^ (2 : ℕ) * 2) =
            2 * ∑ i, w i * ‖phase i - phase k‖ ^ (2 : ℕ) := by
        calc
          (∑ i, ∑ j, w i * w j * ‖phase i - phase k‖ ^ (2 : ℕ) * 2) =
              ∑ i, (w i * ‖phase i - phase k‖ ^ (2 : ℕ) * 2) *
                (∑ j, w j) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
          _ = 2 * ∑ i, w i * ‖phase i - phase k‖ ^ (2 : ℕ) := by
            rw [hmass]
            simp only [mul_one, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      have hright :
          (∑ i, ∑ j, w i * w j * ‖phase j - phase k‖ ^ (2 : ℕ) * 2) =
            2 * ∑ j, w j * ‖phase j - phase k‖ ^ (2 : ℕ) := by
        rw [Finset.sum_comm]
        calc
          (∑ j, ∑ i, w i * w j * ‖phase j - phase k‖ ^ (2 : ℕ) * 2) =
              ∑ j, (w j * ‖phase j - phase k‖ ^ (2 : ℕ) * 2) *
                (∑ i, w i) := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          _ = 2 * ∑ j, w j * ‖phase j - phase k‖ ^ (2 : ℕ) := by
            rw [hmass]
            simp only [mul_one, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      rw [hleft, hright, projectiveWeightedPivotEnergy]
      ring

/-- Fidelity deficit lies between half the pivot weight times pivot energy
and twice pivot energy. -/
theorem weightedFidelityDeficit_pivot_comparable
    {d : ℕ} (w : Fin d → ℝ) (phase : Fin d → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hphase : ∀ i, ‖phase i‖ = 1) (k : Fin d) :
    (w k / 2) * projectiveWeightedPivotEnergy w phase k ≤
        1 - ‖projectiveWeightedPhaseAmplitude w phase‖ ^ (2 : ℕ) ∧
      1 - ‖projectiveWeightedPhaseAmplitude w phase‖ ^ (2 : ℕ) ≤
        2 * projectiveWeightedPivotEnergy w phase k := by
  have hpair := projectiveWeightedPairwiseEnergy_eq_two_mul_fidelityDeficit
    w phase hmass hphase
  have hterm : w k * projectiveWeightedPivotEnergy w phase k ≤
      projectiveWeightedPairwiseEnergy w phase := by
    rw [← sum_weight_mul_projectiveWeightedPivotEnergy]
    exact Finset.single_le_sum
      (fun i _ => mul_nonneg (hw i)
        (projectiveWeightedPivotEnergy_nonneg w phase hw i))
      (Finset.mem_univ k)
  have hupper := projectiveWeightedPairwiseEnergy_le_four_mul_pivot
    w phase hw hmass k
  rw [hpair] at hterm hupper
  constructor <;> nlinarith

end

end RHTower
