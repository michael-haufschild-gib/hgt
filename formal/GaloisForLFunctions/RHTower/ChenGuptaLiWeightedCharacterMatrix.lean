import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterGramCenteredTrace

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RHTower

/-- CGL's finite character matrix with an arbitrary complex dyadic weight, covering the v2
source specialization `weight j = w((N+j+1)/N)`. -/
def cglCharacterDyadicWeightedEvaluationMatrix (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) : Matrix (Fin R) (Fin N) ℂ :=
  fun r j => weight j * (w r).character (cglCharacterDyadicIndex N j) *
    cglCharacterDyadicPhase N (w r).time j

def cglCharacterDyadicWeightedEvaluationOperator (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin R) :=
  (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin R) (n := Fin N)).trans
    LinearMap.toContinuousLinearMap (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w)

def cglCharacterDyadicWeightedPolynomial (N q : ℕ) (weight : Fin N → ℂ)
    (w : CGLCharacterDyadicRowData q) (a : EuclideanSpace ℂ (Fin N)) : ℂ :=
  ∑ j, a j * weight j * w.character (cglCharacterDyadicIndex N j) *
    cglCharacterDyadicPhase N w.time j

theorem cglCharacterDyadicWeightedEvaluationOperator_apply (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) (a : EuclideanSpace ℂ (Fin N)) (r : Fin R) :
    cglCharacterDyadicWeightedEvaluationOperator N q R weight w a r =
      cglCharacterDyadicWeightedPolynomial N q weight (w r) a := by
  change (Matrix.mulVec (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w) a.ofLp) r = _
  unfold cglCharacterDyadicWeightedEvaluationMatrix cglCharacterDyadicWeightedPolynomial Matrix.mulVec
  apply Finset.sum_congr rfl
  intro j hj
  change weight j * (w r).character (cglCharacterDyadicIndex N j) *
      cglCharacterDyadicPhase N (w r).time j * a.ofLp j = _
  ring

theorem normSq_cglCharacterDyadicWeightedEvaluationOperator_apply (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) (a : EuclideanSpace ℂ (Fin N)) :
    ‖cglCharacterDyadicWeightedEvaluationOperator N q R weight w a‖ ^ 2 =
      ∑ r, ‖cglCharacterDyadicWeightedPolynomial N q weight (w r) a‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  apply Finset.sum_congr rfl
  intro r hr
  simpa using congrArg (fun z : ℂ => ‖z‖)
    (cglCharacterDyadicWeightedEvaluationOperator_apply N q R weight w a r)

def cglCharacterDyadicWeightedLargeValues (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) (a : EuclideanSpace ℂ (Fin N))
    (V : NNReal) : Finset (Fin R) :=
  Finset.univ.filter (fun r => (V : ℝ) ≤ ‖cglCharacterDyadicWeightedPolynomial N q weight (w r) a‖)

/-- The closed weighted form of CGL Lemma 4.1. -/
theorem card_cglCharacterDyadicWeightedLargeValues_mul_sq_le_operator_bounded
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q)
    (a : CGLCharacterDyadicBoundedCoefficients N) (V : NNReal) :
    ((cglCharacterDyadicWeightedLargeValues N q R weight w a.value V).card : ℝ) * (V : ℝ) ^ 2 ≤
      (N : ℝ) * ‖cglCharacterDyadicWeightedEvaluationOperator N q R weight w‖ ^ 2 := by
  let S := cglCharacterDyadicWeightedLargeValues N q R weight w a.value V
  have hlarge : ∀ r ∈ S,
      (V : ℝ) ^ 2 ≤ ‖cglCharacterDyadicWeightedPolynomial N q weight (w r) a.value‖ ^ 2 := by
    intro r hr
    exact pow_le_pow_left₀ NNReal.zero_le_coe (Finset.mem_filter.mp hr).2 2
  have hsumLarge : (S.card : ℝ) * (V : ℝ) ^ 2 ≤
      ∑ r ∈ S, ‖cglCharacterDyadicWeightedPolynomial N q weight (w r) a.value‖ ^ 2 := by
    calc
      (S.card : ℝ) * (V : ℝ) ^ 2 = ∑ _r ∈ S, (V : ℝ) ^ 2 := by simp
      _ ≤ ∑ r ∈ S, ‖cglCharacterDyadicWeightedPolynomial N q weight (w r) a.value‖ ^ 2 :=
        Finset.sum_le_sum hlarge
  have hsub : ∑ r ∈ S, ‖cglCharacterDyadicWeightedPolynomial N q weight (w r) a.value‖ ^ 2 ≤
      ∑ r : Fin R, ‖cglCharacterDyadicWeightedPolynomial N q weight (w r) a.value‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro r hrS hrU
    exact sq_nonneg ‖cglCharacterDyadicWeightedPolynomial N q weight (w r) a.value‖
  have hop := (cglCharacterDyadicWeightedEvaluationOperator N q R weight w).le_opNorm a.value
  have hopsq := pow_le_pow_left₀ (norm_nonneg _) hop 2
  calc
    ((cglCharacterDyadicWeightedLargeValues N q R weight w a.value V).card : ℝ) * (V : ℝ) ^ 2 ≤
        ∑ r ∈ S, ‖cglCharacterDyadicWeightedPolynomial N q weight (w r) a.value‖ ^ 2 := hsumLarge
    _ ≤ ∑ r : Fin R, ‖cglCharacterDyadicWeightedPolynomial N q weight (w r) a.value‖ ^ 2 := hsub
    _ = ‖cglCharacterDyadicWeightedEvaluationOperator N q R weight w a.value‖ ^ 2 :=
      (normSq_cglCharacterDyadicWeightedEvaluationOperator_apply N q R weight w a.value).symm
    _ ≤ (‖cglCharacterDyadicWeightedEvaluationOperator N q R weight w‖ * ‖a.value‖) ^ 2 := hopsq
    _ = ‖cglCharacterDyadicWeightedEvaluationOperator N q R weight w‖ ^ 2 * ‖a.value‖ ^ 2 := by ring
    _ ≤ ‖cglCharacterDyadicWeightedEvaluationOperator N q R weight w‖ ^ 2 * (N : ℝ) :=
      mul_le_mul_of_nonneg_left (normSq_cglCharacterDyadicBoundedCoefficients_le N a) (sq_nonneg _)
    _ = (N : ℝ) * ‖cglCharacterDyadicWeightedEvaluationOperator N q R weight w‖ ^ 2 := by ring

end RHTower
