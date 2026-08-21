import GaloisForLFunctions.RHTower.ChenGuptaLiWeightedCharacterMatrix

open scoped Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace RHTower

/-- The weighted character/ordinate correlation in the row Gram matrix. -/
def cglCharacterDyadicWeightedCorrelation (N q : ℕ) (weight : Fin N → ℂ)
    (w v : CGLCharacterDyadicRowData q) : ℂ :=
  ∑ j, weight j * (starRingEnd ℂ) (weight j) *
    w.character (cglCharacterDyadicIndex N j) *
      (starRingEnd ℂ) (v.character (cglCharacterDyadicIndex N j)) *
        cglCharacterDyadicPhase N (w.time - v.time) j

/-- The literal row-side Gram matrix of CGL's weighted character matrix. -/
def cglCharacterDyadicWeightedGram (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) : Matrix (Fin R) (Fin R) ℂ :=
  fun r s => cglCharacterDyadicWeightedCorrelation N q weight (w r) (w s)

theorem cglCharacterDyadicWeightedEvaluationMatrix_self_mul_conjTranspose_eq_gram
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicWeightedEvaluationMatrix N q R weight w *
        (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w)ᴴ =
      cglCharacterDyadicWeightedGram N q R weight w := by
  ext r s
  rw [Matrix.mul_apply]
  unfold cglCharacterDyadicWeightedEvaluationMatrix cglCharacterDyadicWeightedGram
    cglCharacterDyadicWeightedCorrelation
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.conjTranspose_apply]
  rw [star_mul, star_mul]
  change weight j * (w r).character (cglCharacterDyadicIndex N j) *
      cglCharacterDyadicPhase N (w r).time j *
        ((starRingEnd ℂ) (cglCharacterDyadicPhase N (w s).time j) *
          ((starRingEnd ℂ) ((w s).character (cglCharacterDyadicIndex N j)) *
            (starRingEnd ℂ) (weight j))) = _
  calc
    _ = weight j * (starRingEnd ℂ) (weight j) *
        (w r).character (cglCharacterDyadicIndex N j) *
          (starRingEnd ℂ) ((w s).character (cglCharacterDyadicIndex N j)) *
            (cglCharacterDyadicPhase N (w r).time j *
              (starRingEnd ℂ) (cglCharacterDyadicPhase N (w s).time j)) := by ring
    _ = _ := by rw [cglCharacterDyadicPhase_mul_conj]

theorem norm_cglCharacterDyadicWeightedEvaluationOperator_eq_matrix (N q R : ℕ)
    (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q) :
    ‖cglCharacterDyadicWeightedEvaluationOperator N q R weight w‖ =
      ‖cglCharacterDyadicWeightedEvaluationMatrix N q R weight w‖ := by
  simpa [cglCharacterDyadicWeightedEvaluationOperator] using
    (Matrix.l2_opNorm_def (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w)).symm

/-- CGL Lemma 4.2 for its literal weighted finite character matrix. -/
theorem cglCharacterDyadicWeighted_operatorNorm_le_centeredGramTrace (N q R : ℕ)
    (weight : Fin N → ℂ) (w : Fin (R + 1) → CGLCharacterDyadicRowData q) :
    ‖cglCharacterDyadicWeightedEvaluationOperator N q (R + 1) weight w‖ ≤
      2 * (((cglCharacterDyadicWeightedGram N q (R + 1) weight w) ^ 3).trace.re -
        ((cglCharacterDyadicWeightedGram N q (R + 1) weight w).trace.re ^ 3) / (R + 1 : ℝ) ^ 2) ^
          (1 / 6 : ℝ) +
      2 * √((cglCharacterDyadicWeightedGram N q (R + 1) weight w).trace.re / (R + 1 : ℝ)) := by
  rw [norm_cglCharacterDyadicWeightedEvaluationOperator_eq_matrix]
  have h := cglLemmaFourPointTwo_finite R N
    (cglCharacterDyadicWeightedEvaluationMatrix N q (R + 1) weight w)
  rw [cglCharacterDyadicWeightedEvaluationMatrix_self_mul_conjTranspose_eq_gram] at h
  exact h

/-- Closed weighted composition of CGL Lemmas 4.1 and 4.2. -/
theorem card_cglCharacterDyadicWeightedLargeValues_mul_sq_le_centeredGramTrace
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin (R + 1) → CGLCharacterDyadicRowData q)
    (a : CGLCharacterDyadicBoundedCoefficients N) (V : NNReal) :
    ((cglCharacterDyadicWeightedLargeValues N q (R + 1) weight w a.value V).card : ℝ) * (V : ℝ) ^ 2 ≤
      (N : ℝ) *
        (2 * (((cglCharacterDyadicWeightedGram N q (R + 1) weight w) ^ 3).trace.re -
          ((cglCharacterDyadicWeightedGram N q (R + 1) weight w).trace.re ^ 3) /
            (R + 1 : ℝ) ^ 2) ^ (1 / 6 : ℝ) +
          2 * √((cglCharacterDyadicWeightedGram N q (R + 1) weight w).trace.re /
            (R + 1 : ℝ))) ^ 2 := by
  have hlarge := card_cglCharacterDyadicWeightedLargeValues_mul_sq_le_operator_bounded
    N q (R + 1) weight w a V
  have hnorm := cglCharacterDyadicWeighted_operatorNorm_le_centeredGramTrace N q R weight w
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    ((cglCharacterDyadicWeightedLargeValues N q (R + 1) weight w a.value V).card : ℝ) *
        (V : ℝ) ^ 2 ≤
      (N : ℝ) * ‖cglCharacterDyadicWeightedEvaluationOperator N q (R + 1) weight w‖ ^ 2 := hlarge
    _ ≤ (N : ℝ) *
        (2 * (((cglCharacterDyadicWeightedGram N q (R + 1) weight w) ^ 3).trace.re -
          ((cglCharacterDyadicWeightedGram N q (R + 1) weight w).trace.re ^ 3) /
            (R + 1 : ℝ) ^ 2) ^ (1 / 6 : ℝ) +
          2 * √((cglCharacterDyadicWeightedGram N q (R + 1) weight w).trace.re /
            (R + 1 : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)

end RHTower
