import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateHasIndefiniteFiniteProbeMatrices
import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClippingOrder

/-!
# Spectral clipping retains both critical-tail signs

The finite Hankel matrix on a polynomial support realizes the actual damped
tail moments. A positive symmetric cutoff preserves its inertia. Thus every
critical-state tail still has clipped matrices failing each semidefinite
sign; capping spectral magnitude does not restore a fixed density sign.
-/

open Matrix Polynomial
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry HilbertMetric.SymmetricClipping
open ArithmeticHodgeTheoryOfDegenerations ArithmeticHarmonicAnalysis.Coleman
open BiScaleUncertainty.Observation
noncomputable section

/-- The actual tail moment matrix on an arbitrary finite exponent set. -/
def tailProbeMatrix (F : ℝ → ℝ) (T : ℝ) (s : Finset ℕ) : Matrix s s ℂ :=
  fun i j => (tailProbeMoment F T (i.val + j.val) : ℂ)

theorem tailProbeMatrix_hermitian (F : ℝ → ℝ) (T : ℝ) (s : Finset ℕ) :
    (tailProbeMatrix F T s).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, tailProbeMatrix, Complex.star_def,
    Complex.conj_ofReal, Nat.add_comm]

/-- Polynomial coefficients realize the original signed tail quadratic exactly. -/
theorem tailProbeMatrix_quadratic (F : ℝ → ℝ) (T : ℝ) (P : Polynomial ℝ) :
    hermQuad (tailProbeMatrix F T P.support) (fun i => (P.coeff i.val : ℂ)) =
      tailProbeQuadratic F T P := by
  simp only [hermQuad, dotProduct, mulVec, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal, Finset.mul_sum, Complex.re_sum, tailProbeMatrix,
    ← Complex.ofReal_mul, Complex.ofReal_re, tailProbeQuadratic]
  calc
    _ = ∑ i ∈ P.support, ∑ j : P.support,
        P.coeff i * (tailProbeMoment F T (i + j.val) * P.coeff j.val) :=
      Finset.sum_coe_sort P.support _
    _ = ∑ i ∈ P.support, ∑ j ∈ P.support,
        P.coeff i * (tailProbeMoment F T (i + j) * P.coeff j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_coe_sort P.support _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Bounded spectral regularization of the tail matrix, at a strictly positive cap. -/
def clippedTailProbeMatrix (F : ℝ → ℝ) (T : ℝ) (s : Finset ℕ) (c : ℝ≥0) : Matrix s s ℂ :=
  matrix (tailProbeMatrix_hermitian F T s) (c + 1)

/-- Neither semidefinite sign can be gained through clipping a tail matrix. -/
theorem clippedTailProbeMatrix_signs (F : ℝ → ℝ) (T : ℝ) (s : Finset ℕ) (c : ℝ≥0) :
    ((clippedTailProbeMatrix F T s c).PosSemidef ↔ (tailProbeMatrix F T s).PosSemidef) ∧
      ((-clippedTailProbeMatrix F T s c).PosSemidef ↔ (-tailProbeMatrix F T s).PosSemidef) :=
  ⟨matrix_posSemidef_iff _ _ (by positivity), matrix_neg_posSemidef_iff _ _ (by positivity)⟩

/-- A negative square test certifies a negative direction after every positive cutoff. -/
theorem clippedTailProbeMatrix_not_posSemidef {F : ℝ → ℝ} {T : ℝ} {P : Polynomial ℝ}
    (h : tailProbeQuadratic F T P < 0) (c : ℝ≥0) :
    ¬(clippedTailProbeMatrix F T P.support c).PosSemidef := by
  intro hclip
  have hm := ((clippedTailProbeMatrix_signs F T P.support c).1).mp hclip
  have hq := hm.re_dotProduct_nonneg (fun i => (P.coeff i.val : ℂ))
  change 0 ≤ hermQuad (tailProbeMatrix F T P.support) (fun i => (P.coeff i.val : ℂ)) at hq
  rw [tailProbeMatrix_quadratic] at hq
  exact (not_lt.mpr hq) h

/-- A positive square test likewise certifies a positive direction after clipping. -/
theorem clippedTailProbeMatrix_not_negSemidef {F : ℝ → ℝ} {T : ℝ} {P : Polynomial ℝ}
    (h : 0 < tailProbeQuadratic F T P) (c : ℝ≥0) :
    ¬(-clippedTailProbeMatrix F T P.support c).PosSemidef := by
  intro hclip
  have hm := ((clippedTailProbeMatrix_signs F T P.support c).2).mp hclip
  have hq := hm.re_dotProduct_nonneg (fun i => (P.coeff i.val : ℂ))
  change 0 ≤ hermQuad (-tailProbeMatrix F T P.support) (fun i => (P.coeff i.val : ℂ)) at hq
  rw [hermQuad_neg, tailProbeMatrix_quadratic] at hq
  linarith only [h, hq]

/-- Unconditionally, RH holds or every critical-state tail retains both clipped signs. -/
theorem riemannHypothesis_or_clipped_tailProbeSigns :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ (T : ℝ) (c : ℝ≥0),
        (∃ P : Polynomial ℝ, ¬(clippedTailProbeMatrix F T P.support c).PosSemidef) ∧
          ∃ P : Polynomial ℝ, ¬(-clippedTailProbeMatrix F T P.support c).PosSemidef := by
  rcases riemannHypothesis_or_indefinite_tailProbeQuadratic with hRH | ⟨W₀, F, hW, ht, hF, hsign⟩
  · exact Or.inl hRH
  · refine Or.inr ⟨W₀, F, hW, ht, hF, ?_⟩
    intro T c
    obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ := hsign T
    exact ⟨⟨P, clippedTailProbeMatrix_not_posSemidef hP c⟩,
      ⟨Q, clippedTailProbeMatrix_not_negSemidef hQ c⟩⟩

#print axioms tailProbeMatrix_quadratic
#print axioms clippedTailProbeMatrix_signs
#print axioms riemannHypothesis_or_clipped_tailProbeSigns

end
end GaloisForLFunctions.ExclusionOfTheCriticalState
