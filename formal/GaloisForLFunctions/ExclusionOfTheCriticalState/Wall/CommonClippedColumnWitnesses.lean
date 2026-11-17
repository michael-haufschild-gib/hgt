import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ClippedTailProbeSigns
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.CofiniteColumnTailTests
import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClippingRestoration

/-!
# Both signs in one bounded column matrix

The union of two polynomial supports gives a single finite tail matrix.
Positive spectral rescaling transports both witnesses through every positive
cutoff. Its exponent set can lie in any prescribed cofinite residue columns.
-/

noncomputable section
open Matrix
open _root_.Polynomial
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry HilbertMetric.SymmetricClipping
open ArithmeticEffectivityTheory.ResidueColumns
open ArithmeticHodgeTheoryOfDegenerations BiScaleUncertainty.Observation

/-- Enlarging the exponent set by zero coefficients leaves the tail form unchanged. -/
theorem tailProbeMatrix_quadratic_of_support_subset (F : ℝ → ℝ) (T : ℝ)
    (P : ℝ[X]) (s : Finset ℕ) (hs : P.support ⊆ s) :
    hermQuad (tailProbeMatrix F T s) (fun i => (P.coeff i.val : ℂ)) =
      tailProbeQuadratic F T P := by
  classical
  simp only [hermQuad, dotProduct, mulVec, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal, Finset.mul_sum, Complex.re_sum, tailProbeMatrix,
    ← Complex.ofReal_mul, Complex.ofReal_re, tailProbeQuadratic]
  calc
    _ = ∑ i ∈ s, ∑ j : s,
        P.coeff i * (tailProbeMoment F T (i + j.val) * P.coeff j.val) :=
      Finset.sum_coe_sort (M := ℝ) s (fun i => ∑ j : s,
        P.coeff i * (tailProbeMoment F T (i + j.val) * P.coeff j.val))
    _ = ∑ i ∈ s, ∑ j ∈ s, P.coeff i * P.coeff j * tailProbeMoment F T (i + j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_coe_sort (M := ℝ) s (fun j =>
        P.coeff i * (tailProbeMoment F T (i + j) * P.coeff j))]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i ∈ P.support, ∑ j ∈ s,
        P.coeff i * P.coeff j * tailProbeMoment F T (i + j) := by
      symm
      apply Finset.sum_subset hs
      intro i _ hi
      have hz : P.coeff i = 0 := by
        by_contra h
        exact hi (mem_support_iff.mpr h)
      simp only [hz, zero_mul, Finset.sum_const_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply Finset.sum_subset hs
      intro j _ hj
      have hz : P.coeff j = 0 := by
        by_contra h
        exact hj (mem_support_iff.mpr h)
      simp only [hz, mul_zero, zero_mul]

/-- One finite column matrix has both signs at every strictly positive spectral cap. -/
theorem criticalState_common_clipped_column_witnesses {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (T : ℝ) (m : ℕ) (k : ℕ → ℕ) :
    ∃ s : Finset ℕ, (∀ n ∈ s, n ∈ carrier m k) ∧
      ∀ c : ℝ≥0, 0 < c → ∃ v w : s → ℂ,
        hermQuad (matrix (tailProbeMatrix_hermitian F T s) c) v < 0 ∧
          0 < hermQuad (matrix (tailProbeMatrix_hermitian F T s) c) w := by
  classical
  obtain ⟨⟨P, hPc, hP⟩, ⟨Q, hQc, hQ⟩⟩ :=
    criticalState_column_tail_both_signs hW ht hF T m k
  refine ⟨P.support ∪ Q.support, ?_, ?_⟩
  · intro n hn
    rcases Finset.mem_union.mp hn with hp | hq
    · exact hPc n hp
    · exact hQc n hq
  · intro c hc
    refine ⟨restoreMatrix (tailProbeMatrix_hermitian F T _) c *ᵥ
      (fun i => (P.coeff i.val : ℂ)),
      restoreMatrix (tailProbeMatrix_hermitian F T _) c *ᵥ
      (fun i => (Q.coeff i.val : ℂ)), ?_, ?_⟩
    · rw [matrix_quadratic_transport _ _ hc,
        tailProbeMatrix_quadratic_of_support_subset F T P _ Finset.subset_union_left]
      exact hP
    · rw [matrix_quadratic_transport _ _ hc,
        tailProbeMatrix_quadratic_of_support_subset F T Q _ Finset.subset_union_right]
      exact hQ

/-- RH or a single finite matrix on any cofinite columns retains both signs at every cap. -/
theorem riemannHypothesis_or_common_clipped_column_witnesses :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ (T : ℝ) (m : ℕ) (k : ℕ → ℕ),
        ∃ s : Finset ℕ, (∀ n ∈ s, n ∈ carrier m k) ∧
          ∀ c : ℝ≥0, 0 < c → ∃ v w : s → ℂ,
            hermQuad (matrix (tailProbeMatrix_hermitian F T s) c) v < 0 ∧
              0 < hermQuad (matrix (tailProbeMatrix_hermitian F T s) c) w := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with
    hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, criticalState_common_clipped_column_witnesses hW ht hF⟩

#print axioms tailProbeMatrix_quadratic_of_support_subset
#print axioms riemannHypothesis_or_common_clipped_column_witnesses

end GaloisForLFunctions.ExclusionOfTheCriticalState
