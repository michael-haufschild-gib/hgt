/-
# Chen--Gupta--Li Lemma 4.1: finite operator-norm reduction

The source large-value matrix has entries `χ(n)n^{it}`.  This module builds
that literal finite evaluation matrix, identifies its action on the bounded
coefficient vector with the source Dirichlet polynomials, and proves the
operator-norm large-value reduction.  It does not estimate that operator norm:
the refined correlation analysis beginning with source Lemma 4.2 remains a
separate layer.
-/
import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterLargeValues

noncomputable section

namespace RHTower

/-- The literal finite Chen--Gupta--Li evaluation matrix: its `r,j` entry is
`χ_r(N+j+1)(N+j+1)^{it_r}`. -/
def cglCharacterDyadicEvaluationMatrix (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) : Matrix (Fin R) (Fin N) ℂ :=
  fun r j => (w r).character (cglCharacterDyadicIndex N j) *
    cglCharacterDyadicPhase N (w r).time j

/-- The CGL finite evaluation matrix as a bounded Euclidean-space operator. -/
def cglCharacterDyadicEvaluationOperator (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin R) :=
  (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin R) (n := Fin N)).trans
    LinearMap.toContinuousLinearMap (cglCharacterDyadicEvaluationMatrix N q R w)

/-- The source matrix action in row `r` is exactly the corresponding CGL
Dirichlet polynomial. -/
theorem cglCharacterDyadicEvaluationOperator_apply (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (a : EuclideanSpace ℂ (Fin N)) (r : Fin R) :
    cglCharacterDyadicEvaluationOperator N q R w a r =
      cglCharacterDyadicPolynomial N q (w r) a := by
  change (Matrix.mulVec (cglCharacterDyadicEvaluationMatrix N q R w) a.ofLp) r = _
  unfold cglCharacterDyadicEvaluationMatrix cglCharacterDyadicPolynomial Matrix.mulVec
  apply Finset.sum_congr rfl
  intro j hj
  change (w r).character (cglCharacterDyadicIndex N j) *
      cglCharacterDyadicPhase N (w r).time j * a.ofLp j =
    a j * (w r).character (cglCharacterDyadicIndex N j) *
      cglCharacterDyadicPhase N (w r).time j
  ring

/-- The Euclidean output energy of the CGL evaluation operator is exactly the
sum of the squared source polynomial values over its row packet. -/
theorem normSq_cglCharacterDyadicEvaluationOperator_apply (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (a : EuclideanSpace ℂ (Fin N)) :
    ‖cglCharacterDyadicEvaluationOperator N q R w a‖ ^ 2 =
      ∑ r, ‖cglCharacterDyadicPolynomial N q (w r) a‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  apply Finset.sum_congr rfl
  intro r hr
  simpa using congrArg (fun z : ℂ => ‖z‖)
    (cglCharacterDyadicEvaluationOperator_apply N q R w a r)

/-- Certified source coefficients satisfying the pointwise bound `|b_n| ≤ 1`.
The bound is data, so source-facing large-value statements take no premise. -/
structure CGLCharacterDyadicBoundedCoefficients (N : ℕ) where
  value : EuclideanSpace ℂ (Fin N)
  coord_norm_le_one : ∀ j, ‖value j‖ ≤ 1

/-- A certified bounded CGL coefficient vector has Euclidean energy at most
the block length. -/
theorem normSq_cglCharacterDyadicBoundedCoefficients_le (N : ℕ)
    (a : CGLCharacterDyadicBoundedCoefficients N) : ‖a.value‖ ^ 2 ≤ (N : ℝ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  calc
    ∑ j, ‖a.value.ofLp j‖ ^ 2 ≤ ∑ _j : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      nlinarith [norm_nonneg (a.value j), a.coord_norm_le_one j]
    _ = N := by simp

/-- Closed finite CGL Lemma-4.1 reduction: the number of selected large values
is bounded by the square of the literal evaluation operator norm times the
source block length. -/
theorem card_cglCharacterDyadicLargeValues_mul_sq_le_operator_bounded
    (N q R : ℕ) (w : Fin R → CGLCharacterDyadicRowData q)
    (a : CGLCharacterDyadicBoundedCoefficients N) (V : NNReal) :
    ((cglCharacterDyadicLargeValues N q R w a.value V).card : ℝ) * (V : ℝ) ^ 2 ≤
      (N : ℝ) * ‖cglCharacterDyadicEvaluationOperator N q R w‖ ^ 2 := by
  let S := cglCharacterDyadicLargeValues N q R w a.value V
  have hlarge : ∀ r ∈ S, (V : ℝ) ^ 2 ≤ ‖cglCharacterDyadicPolynomial N q (w r) a.value‖ ^ 2 := by
    intro r hr
    exact pow_le_pow_left₀ NNReal.zero_le_coe (Finset.mem_filter.mp hr).2 2
  have hsumLarge : (S.card : ℝ) * (V : ℝ) ^ 2 ≤
      ∑ r ∈ S, ‖cglCharacterDyadicPolynomial N q (w r) a.value‖ ^ 2 := by
    calc
      (S.card : ℝ) * (V : ℝ) ^ 2 = ∑ _r ∈ S, (V : ℝ) ^ 2 := by simp
      _ ≤ ∑ r ∈ S, ‖cglCharacterDyadicPolynomial N q (w r) a.value‖ ^ 2 :=
        Finset.sum_le_sum hlarge
  have hsub : ∑ r ∈ S, ‖cglCharacterDyadicPolynomial N q (w r) a.value‖ ^ 2 ≤
      ∑ r : Fin R, ‖cglCharacterDyadicPolynomial N q (w r) a.value‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro r hrS hrU
    exact sq_nonneg ‖cglCharacterDyadicPolynomial N q (w r) a.value‖
  have hop := (cglCharacterDyadicEvaluationOperator N q R w).le_opNorm a.value
  have hopsq := pow_le_pow_left₀ (norm_nonneg _) hop 2
  calc
    (S.card : ℝ) * (V : ℝ) ^ 2 ≤
        ∑ r ∈ S, ‖cglCharacterDyadicPolynomial N q (w r) a.value‖ ^ 2 := hsumLarge
    _ ≤ ∑ r : Fin R, ‖cglCharacterDyadicPolynomial N q (w r) a.value‖ ^ 2 := hsub
    _ = ‖cglCharacterDyadicEvaluationOperator N q R w a.value‖ ^ 2 :=
      (normSq_cglCharacterDyadicEvaluationOperator_apply N q R w a.value).symm
    _ ≤ (‖cglCharacterDyadicEvaluationOperator N q R w‖ * ‖a.value‖) ^ 2 := hopsq
    _ = ‖cglCharacterDyadicEvaluationOperator N q R w‖ ^ 2 * ‖a.value‖ ^ 2 := by ring
    _ ≤ ‖cglCharacterDyadicEvaluationOperator N q R w‖ ^ 2 * (N : ℝ) :=
      mul_le_mul_of_nonneg_left (normSq_cglCharacterDyadicBoundedCoefficients_le N a) (sq_nonneg _)
    _ = (N : ℝ) * ‖cglCharacterDyadicEvaluationOperator N q R w‖ ^ 2 := by ring

end RHTower
