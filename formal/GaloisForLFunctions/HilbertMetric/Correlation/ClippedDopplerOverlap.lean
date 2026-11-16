import GaloisForLFunctions.HilbertMetric.Spectral.ClippedCongruence
import GaloisForLFunctions.HilbertMetric.Correlation.DopplerFinitePrediction

/-!
# Clipped overlap in Doppler observation kernels

Adding unit independent noise and dividing by total diagonal mass gives a
correlation matrix even for an empty or zero-mass mixture. The mixed Gram
inequality then preserves its overlap defect under single or double pilot weights.
-/

open Matrix
open scoped NNReal
namespace HilbertMetric.Correlation
open GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section
variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Unit-noise Doppler covariance normalized to unit diagonal. -/
def regularizedDopplerCorrelation (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (time : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (((1 + ∑ i, (w i : ℝ))⁻¹ : ℝ) : ℂ) •
    (1 + Matrix.of fun i j => dopplerClusterKernel w mean variance (time j - time i))

theorem regularizedDopplerCorrelation_hermitian (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (time : Fin n → ℝ) :
    (regularizedDopplerCorrelation w mean variance time).IsHermitian := by
  have h := (dopplerGram_posSemidef w mean variance time).isHermitian
  simp only [Matrix.IsHermitian, regularizedDopplerCorrelation, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_one, h.eq,
    Complex.star_def, Complex.conj_ofReal]

theorem regularizedDopplerCorrelation_diagonal (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (time : Fin n → ℝ) (i : Fin n) :
    regularizedDopplerCorrelation w mean variance time i i = 1 := by
  have hm : 0 < 1 + ∑ j, (w j : ℝ) :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun j _ => (w j).coe_nonneg)
  simp only [regularizedDopplerCorrelation, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply_eq, Matrix.of_apply, sub_self, dopplerClusterKernel,
    Complex.ofReal_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero,
    zero_div, sub_zero, Complex.exp_zero, mul_one, smul_eq_mul]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_one, ← Complex.ofReal_add,
    ← Complex.ofReal_mul, inv_mul_cancel₀ hm.ne', Complex.ofReal_one]

/-- Arbitrary pilot doubling retains the full normalized Doppler defect. -/
theorem doppler_mixed_clipping (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (time : Fin n → ℝ) (doubled : Fin n → Bool) (τ : NNReal) :
    defectEnergy τ (regularizedDopplerCorrelation w mean variance time) +
      ∑ i, binaryWeight doubled i ^ 2 ≤
        energy (mixedCutoff τ) (weightedGram (binaryWeight doubled)
          (regularizedDopplerCorrelation w mean variance time)) :=
  binary_mixed_bound (regularizedDopplerCorrelation_hermitian w mean variance time)
    (regularizedDopplerCorrelation_diagonal w mean variance time) doubled τ

/-- Squared Doppler overlaps supply an explicit lower bound after clipping. -/
theorem doppler_clipped_overlap (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (time : Fin n → ℝ) (τ : NNReal) :
    min ((∑ i, ∑ j, Complex.normSq (regularizedDopplerCorrelation w mean variance time i j)) - n)
      ((τ : ℝ) ^ 2) ≤ defectEnergy τ (regularizedDopplerCorrelation w mean variance time) := by
  have hH := regularizedDopplerCorrelation_hermitian w mean variance time
  have h := defectEnergy_min_bound hH τ
  rw [trace_square hH] at h
  have ht : (trace (regularizedDopplerCorrelation w mean variance time)).re = n := by
    simp [trace, diag, regularizedDopplerCorrelation_diagonal]
  rw [ht, Fintype.card_fin] at h
  convert h using 1 <;> congr 1 <;> ring

#print axioms doppler_mixed_clipping
#print axioms doppler_clipped_overlap

end
end HilbertMetric.Correlation
