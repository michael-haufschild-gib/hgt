import GaloisForLFunctions.RHTower.ChenGuptaLiGramCenteredTrace

open scoped Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace RHTower

/-- The exact row-side Gram identity for CGL's literal character evaluation matrix. -/
theorem cglCharacterDyadicEvaluationMatrix_self_mul_conjTranspose_eq_gram
    (N q R : ℕ) (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicEvaluationMatrix N q R w *
        (cglCharacterDyadicEvaluationMatrix N q R w)ᴴ =
      cglCharacterDyadicGram N q R w := by
  ext r s
  rw [Matrix.mul_apply, cglCharacterDyadicGram_apply]
  unfold cglCharacterDyadicCorrelation cglCharacterDyadicEvaluationMatrix
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.conjTranspose_apply]
  rw [star_mul]
  change (w r).character (cglCharacterDyadicIndex N j) * cglCharacterDyadicPhase N (w r).time j *
      ((starRingEnd ℂ) (cglCharacterDyadicPhase N (w s).time j) *
        (starRingEnd ℂ) ((w s).character (cglCharacterDyadicIndex N j))) =
    (w r).character (cglCharacterDyadicIndex N j) *
      (starRingEnd ℂ) ((w s).character (cglCharacterDyadicIndex N j)) *
        cglCharacterDyadicPhase N ((w r).time - (w s).time) j
  calc
    _ = (w r).character (cglCharacterDyadicIndex N j) *
        (starRingEnd ℂ) ((w s).character (cglCharacterDyadicIndex N j)) *
          (cglCharacterDyadicPhase N (w r).time j *
            (starRingEnd ℂ) (cglCharacterDyadicPhase N (w s).time j)) := by ring
    _ = _ := by rw [cglCharacterDyadicPhase_mul_conj]

theorem norm_cglCharacterDyadicEvaluationOperator_eq_matrix (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) :
    ‖cglCharacterDyadicEvaluationOperator N q R w‖ = ‖cglCharacterDyadicEvaluationMatrix N q R w‖ := by
  simpa [cglCharacterDyadicEvaluationOperator] using
    (Matrix.l2_opNorm_def (cglCharacterDyadicEvaluationMatrix N q R w)).symm

/-- CGL Lemma 4.2 applied to a literal nonempty character/ordinate packet. -/
theorem cglCharacterDyadic_operatorNorm_le_centeredGramTrace (N q R : ℕ)
    (w : Fin (R + 1) → CGLCharacterDyadicRowData q) :
    ‖cglCharacterDyadicEvaluationOperator N q (R + 1) w‖ ≤
      2 * (((cglCharacterDyadicGram N q (R + 1) w) ^ 3).trace.re -
        ((cglCharacterDyadicGram N q (R + 1) w).trace.re ^ 3) / (R + 1 : ℝ) ^ 2) ^
          (1 / 6 : ℝ) +
      2 * √((cglCharacterDyadicGram N q (R + 1) w).trace.re / (R + 1 : ℝ)) := by
  rw [norm_cglCharacterDyadicEvaluationOperator_eq_matrix]
  have h := cglLemmaFourPointTwo_finite R N (cglCharacterDyadicEvaluationMatrix N q (R + 1) w)
  rw [cglCharacterDyadicEvaluationMatrix_self_mul_conjTranspose_eq_gram] at h
  exact h

/-- Closed CGL Lemmas 4.1--4.2 composition for a literal nonempty character packet. -/
theorem card_cglCharacterDyadicLargeValues_mul_sq_le_centeredGramTrace
    (N q R : ℕ) (w : Fin (R + 1) → CGLCharacterDyadicRowData q)
    (a : CGLCharacterDyadicBoundedCoefficients N) (V : NNReal) :
    ((cglCharacterDyadicLargeValues N q (R + 1) w a.value V).card : ℝ) * (V : ℝ) ^ 2 ≤
      (N : ℝ) *
        (2 * (((cglCharacterDyadicGram N q (R + 1) w) ^ 3).trace.re -
          ((cglCharacterDyadicGram N q (R + 1) w).trace.re ^ 3) / (R + 1 : ℝ) ^ 2) ^
            (1 / 6 : ℝ) +
          2 * √((cglCharacterDyadicGram N q (R + 1) w).trace.re / (R + 1 : ℝ))) ^ 2 := by
  have hlarge := card_cglCharacterDyadicLargeValues_mul_sq_le_operator_bounded N q (R + 1) w a V
  have hnorm := cglCharacterDyadic_operatorNorm_le_centeredGramTrace N q R w
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    ((cglCharacterDyadicLargeValues N q (R + 1) w a.value V).card : ℝ) * (V : ℝ) ^ 2 ≤
        (N : ℝ) * ‖cglCharacterDyadicEvaluationOperator N q (R + 1) w‖ ^ 2 := hlarge
    _ ≤ (N : ℝ) *
        (2 * (((cglCharacterDyadicGram N q (R + 1) w) ^ 3).trace.re -
          ((cglCharacterDyadicGram N q (R + 1) w).trace.re ^ 3) / (R + 1 : ℝ) ^ 2) ^
            (1 / 6 : ℝ) +
          2 * √((cglCharacterDyadicGram N q (R + 1) w).trace.re / (R + 1 : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)

end RHTower
