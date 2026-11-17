import GaloisForLFunctions.HilbertMetric.Spectral.ClippedCongruence
import GaloisForLFunctions.HilbertMetric.Spectral.ClippedThreshold
import GaloisForLFunctions.HTGeometry.GramRealizationFirewall

/-!
# Clipped Gram energy in arbitrary complex inner-product spaces

Only the observed family is finite. No ambient dimension or completeness
assumption is needed. Adding unit noise and normalizing each diagonal gives a
correlation matrix for every vector family, including zero vectors.
-/

open Matrix
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.Observation
open Clipped HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]


private theorem inner_self_real (x : E) : (inner ℂ x x).re = ‖x‖ ^ 2 := by
  simpa only [RCLike.re_to_complex] using (inner_self_eq_norm_sq (𝕜 := ℂ) x)

/-- Overlaps and vector masses determine a clipped defect in every ambient dimension. -/
theorem innerGram_clippedDefect (v : ι → E) (τ : ℝ≥0) :
    min ((∑ i, ∑ j, Complex.normSq (inner ℂ (v i) (v j))) -
      2 * (∑ i, ‖v i‖ ^ 2) + Fintype.card ι) ((τ : ℝ) ^ 2) ≤
        defectEnergy τ (innerGramMatrix v) := by
  have h := defectEnergy_min_bound (isHermitian_innerGramMatrix v) τ
  rw [trace_square (isHermitian_innerGramMatrix v)] at h
  simpa only [trace, diag, innerGramMatrix_apply, Complex.re_sum,
    inner_self_real] using h

/-- Diagonal normalization after adding unit independent noise. -/
def regularizedInnerGram (v : ι → E) : Matrix ι ι ℂ :=
  congruence (fun i => (Real.sqrt (1 + ‖v i‖ ^ 2))⁻¹) (1 + innerGramMatrix v)

theorem regularizedInnerGram_posSemidef (v : ι → E) :
    (regularizedInnerGram v).PosSemidef := by
  have hI : (1 : Matrix ι ι ℂ).PosSemidef := by
    change (diagonal fun _ : ι => (1 : ℂ)).PosSemidef
    exact Matrix.PosSemidef.diagonal fun _ => zero_le_one
  exact congruence_posSemidef _ (hI.add (posSemidef_innerGramMatrix v))

theorem regularizedInnerGram_hermitian (v : ι → E) :
    (regularizedInnerGram v).IsHermitian :=
  (regularizedInnerGram_posSemidef v).isHermitian

theorem regularizedInnerGram_diagonal (v : ι → E) (i : ι) :
    regularizedInnerGram v i i = 1 := by
  have hd (j : ι) : 0 < 1 + ‖v j‖ ^ 2 := add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)
  have hi := inverseSqrt_diagonal_cancel (fun j => 1 + ‖v j‖ ^ 2) hd i
  have he : (1 + innerGramMatrix v) i i = ((1 + ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simp [innerGramMatrix_apply, inner_self_eq_norm_sq_to_K]
  rw [regularizedInnerGram, congruence_apply, he]
  calc
    _ = (((1 + ‖v i‖ ^ 2) * (Real.sqrt (1 + ‖v i‖ ^ 2))⁻¹ *
        (Real.sqrt (1 + ‖v i‖ ^ 2))⁻¹ : ℝ) : ℂ) := by push_cast; ring
    _ = 1 := by rw [hi]; rfl

/-- Mixed observation multiplicities preserve normalized overlap in any Hilbert realization. -/
theorem innerGram_mixed_clipping (v : ι → E) (doubled : ι → Bool) (τ : ℝ≥0) :
    defectEnergy τ (regularizedInnerGram v) + ∑ i, binaryWeight doubled i ^ 2 ≤
      energy (mixedCutoff τ) (weightedGram (binaryWeight doubled) (regularizedInnerGram v)) :=
  binary_mixed_bound (regularizedInnerGram_hermitian v) (regularizedInnerGram_diagonal v) doubled τ

/-- Subtracting a second realization costs its total vector mass, even in another space. -/
theorem innerGram_subtraction_clipped (v : ι → E) (w : ι → F) (c : ℝ) :
    energy c (innerGramMatrix v) ≤
      (trace ((innerGramMatrix v - innerGramMatrix w) *
        (innerGramMatrix v - innerGramMatrix w))).re + 2 * c * ∑ i, ‖w i‖ ^ 2 := by
  have h := energy_le_sub_square (isHermitian_innerGramMatrix v) (posSemidef_innerGramMatrix w) c
  simpa only [trace, diag, innerGramMatrix_apply, Complex.re_sum,
    inner_self_real] using h

#print axioms innerGram_clippedDefect
#print axioms innerGram_mixed_clipping
#print axioms innerGram_subtraction_clipped

end
end GaloisForLFunctions.HilbertMetric.Observation
