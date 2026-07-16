import GaloisForLFunctions.HTGeometry.FAndMRieszFejerPolynomial
import GaloisForLFunctions.HTGeometry.HardyCoefficientCompactness

/-!
# Hardy compactness in the F. and M. Riesz reduction

The uniformly `L¹`-bounded analytic Fejer polynomials of the remaining moment half-line are
factored into two Hardy coefficient arrays.  Countable compactness produces one common
subsequence, and coefficient uniqueness identifies every positive remaining moment with the
finite convolution of two square-summable limiting sequences.
-/

open MeasureTheory Complex Filter Topology Set Polynomial PowerSeries Finset
open scoped Real ENNReal NNReal Nat ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The positive remaining moment half-line is an exact convolution of two bounded `ℓ²`
sequences.  This is the compactness conclusion extracted from the finite analytic Fejer
factorizations. -/
theorem exists_hardy_l2_convolution_of_equal_analytic_moments
    (mu nu : Measure Circle) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (f g : Circle → ℂ) (hf : Integrable f mu) (hg : Integrable g nu)
    (hvanish : ∀ n : ℕ,
      (∫ w, f w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂mu) =
        ∫ w, g w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂nu) :
    ∃ A B : ℕ → ℂ,
      Memℓp A 2 ∧ Memℓp B 2 ∧
      (∑' k, ‖A k‖ ^ 2) ≤ ( (∫ w, ‖f w‖ ∂mu) + ∫ w, ‖g w‖ ∂nu) ∧
      (∑' k, ‖B k‖ ^ 2) ≤ ( (∫ w, ‖f w‖ ∂mu) + ∫ w, ‖g w‖ ∂nu) ∧
      ∀ n, 0 < n →
        (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g n) =
          ∑ i ∈ Finset.range (n + 1), A i * B (n - i) := by
  let C : ℝ := (∫ w, ‖f w‖ ∂mu) + ∫ w, ‖g w‖ ∂nu
  let p : ℕ → ℂ[X] := fun N => fAndMFejerPolynomial mu nu f g N
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpBound : ∀ N, polynomialBoundaryL1 (p N) ≤ C := by
    intro N
    exact polynomialBoundaryL1_fAndMFejerPolynomial_le mu nu f g hf hg hvanish N
  obtain ⟨A, B, subseq, hsubseq, hAmem, hBmem, hAbound, hBbound, hcoeff⟩ :=
    exists_polynomial_hardy_coefficient_limit_factorization p hC hpBound
  refine ⟨A, B, hAmem, hBmem, ?_, ?_, ?_⟩
  · simpa only [C] using hAbound
  · simpa only [C] using hBbound
  · intro n hn
    have hfinite : Tendsto (fun j => (p (subseq j)).coeff n) atTop
        (nhds ((starRingEnd ℂ) (fAndMRemainingMoment mu nu f g n))) := by
      simpa only [p] using
        (tendsto_fAndMFejerPolynomial_coeff_of_pos mu nu f g n hn).comp
          hsubseq.tendsto_atTop
    exact (tendsto_nhds_unique (hcoeff n) hfinite).symm

end

end GaloisForLFunctions.HTGeometry
