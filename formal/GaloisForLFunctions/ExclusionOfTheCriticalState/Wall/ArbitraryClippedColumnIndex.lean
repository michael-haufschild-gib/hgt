import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ArbitraryTailProbeIndex
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.CommonClippedColumnWitnesses
import GaloisForLFunctions.HilbertMetric.Spectral.RealFamilyInertia
import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClippingInertia

/-!
# Unbounded clipped tail inertia

Polynomial definite spaces yield finite matrices with arbitrarily large positive and negative indices, preserved by every positive clipping cap.
-/

open Matrix Polynomial
open scoped BigOperators NNReal
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry HilbertMetric HilbertMetric.SymmetricClipping
open ArithmeticEffectivityTheory.ResidueColumns ArithmeticHodgeTheoryOfDegenerations

private theorem polynomial_family_support {n : ℕ} (P : Fin n → ℝ[X])
    (s : Finset ℕ) (hs : ∀ i, (P i).support ⊆ s) (c : Fin n → ℝ) :
    (∑ i, c i • P i).support ⊆ s := by
  classical
  intro j hj
  by_contra hjs
  have hz (i : Fin n) : (P i).coeff j = 0 := by
    by_contra hn
    exact hjs (hs i (mem_support_iff.mpr hn))
  have hzero : (∑ i, c i • P i).coeff j = 0 := by simp [hz]
  exact (mem_support_iff.mp hj) hzero

private theorem polynomial_family_coefficients {n : ℕ} (P : Fin n → ℝ[X])
    (s : Finset ℕ) (c : Fin n → ℝ) :
    complexRealFamilySynthesis (fun i (j : s) => (P i).coeff j.val) (fun i => (c i : ℂ)) =
      (fun j : s => ((∑ i, c i • P i).coeff j.val : ℂ)) := by
  classical
  ext j
  simp [complexRealFamilySynthesis]

/-- Polynomial negative spaces are literal negative inertia bounds for one finite tail matrix. -/
theorem tailProbeMatrix_negIndex_ge_family (F : ℝ → ℝ) (T : ℝ) {n : ℕ}
    (P : Fin n → ℝ[X]) (s : Finset ℕ) (hs : ∀ i, (P i).support ⊆ s)
    (hP : ∀ c : Fin n → ℝ, c ≠ 0 → tailProbeQuadratic F T (∑ i, c i • P i) < 0) :
    n ≤ hermNegIndex (tailProbeMatrix F T s) := by
  classical
  apply le_hermNegIndex_of_real_family
    (fun i j : s => tailProbeMoment F T (i.val + j.val))
    (fun i (j : s) => (P i).coeff j.val)
  intro c hc
  rw [polynomial_family_coefficients]
  change hermQuad (tailProbeMatrix F T s) _ < 0
  rw [tailProbeMatrix_quadratic_of_support_subset F T _ s (polynomial_family_support P s hs c)]
  exact hP c hc

/-- The same finite coefficient realization preserves positive dimension. -/
theorem tailProbeMatrix_posIndex_ge_family (F : ℝ → ℝ) (T : ℝ) {n : ℕ}
    (P : Fin n → ℝ[X]) (s : Finset ℕ) (hs : ∀ i, (P i).support ⊆ s)
    (hP : ∀ c : Fin n → ℝ, c ≠ 0 → 0 < tailProbeQuadratic F T (∑ i, c i • P i)) :
    n ≤ hermPosIndex (tailProbeMatrix F T s) := by
  classical
  apply le_hermPosIndex_of_real_family
    (fun i j : s => tailProbeMoment F T (i.val + j.val))
    (fun i (j : s) => (P i).coeff j.val)
  intro c hc
  rw [polynomial_family_coefficients]
  change 0 < hermQuad (tailProbeMatrix F T s) _
  rw [tailProbeMatrix_quadratic_of_support_subset F T _ s (polynomial_family_support P s hs c)]
  exact hP c hc

/-- A single finite cofinite-column matrix has any prescribed positive and negative index at every positive cap. -/
theorem criticalState_arbitrary_clipped_column_indices {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (T : ℝ) (m : ℕ) (k : ℕ → ℕ) (n : ℕ) :
    ∃ s : Finset ℕ, (∀ j ∈ s, j ∈ carrier m k) ∧
      ∀ c : ℝ≥0, 0 < c →
        n ≤ hermNegIndex (matrix (tailProbeMatrix_hermitian F T s) c) ∧
        n ≤ hermPosIndex (matrix (tailProbeMatrix_hermitian F T s) c) := by
  classical
  obtain ⟨P, hPc, hP⟩ := TailIndex.criticalState_column_polynomial_signed_family hW ht hF T 1
    (Or.inl rfl) m k n
  obtain ⟨Q, hQc, hQ⟩ := TailIndex.criticalState_column_polynomial_signed_family hW ht hF T (-1)
    (Or.inr rfl) m k n
  let s : Finset ℕ := Finset.univ.biUnion (fun i => (P i).support ∪ (Q i).support)
  have hPs (i : Fin n) : (P i).support ⊆ s := by
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_union_left _ hj⟩
  have hQs (i : Fin n) : (Q i).support ⊆ s := by
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_union_right _ hj⟩
  refine ⟨s, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hj
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hPc i j hi
    · exact hQc i j hi
  · intro c hc
    have hindices := matrix_inertia (tailProbeMatrix_hermitian F T s) c hc
    rw [hindices.2.1, hindices.1]
    constructor
    · apply tailProbeMatrix_negIndex_ge_family F T P s hPs
      intro a ha
      simpa only [one_mul] using hP a ha
    · apply tailProbeMatrix_posIndex_ge_family F T Q s hQs
      intro a ha
      simpa only [neg_one_mul, neg_lt_zero] using hQ a ha

/-- RH holds, or every cofinite column choice has unbounded positive and negative inertia surviving every positive clipping cap. -/
theorem riemannHypothesis_or_unbounded_clipped_column_indices :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ (T : ℝ) (m : ℕ) (k : ℕ → ℕ) (n : ℕ),
        ∃ s : Finset ℕ, (∀ j ∈ s, j ∈ carrier m k) ∧ ∀ c : ℝ≥0, 0 < c →
          n ≤ hermNegIndex (matrix (tailProbeMatrix_hermitian F T s) c) ∧
          n ≤ hermPosIndex (matrix (tailProbeMatrix_hermitian F T s) c) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with
    hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, criticalState_arbitrary_clipped_column_indices hW ht hF⟩

#print axioms riemannHypothesis_or_unbounded_clipped_column_indices
end GaloisForLFunctions.ExclusionOfTheCriticalState
