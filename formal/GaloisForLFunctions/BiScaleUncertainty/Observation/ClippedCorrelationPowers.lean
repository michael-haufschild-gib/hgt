import GaloisForLFunctions.HilbertMetric.Spectral.ClippedTrace
import GaloisForLFunctions.BiScaleUncertainty.SchurSquareCorrelation

/-!
# Clipped energy of translation correlations and their powers

Every integer power of the literal autocorrelation gives a Hermitian sampled
matrix. The first and second spectral moments are explicit correlation sums.
Clipping retains their centered surplus up to the cutoff square. At power two
this applies directly to the corpus's tensor-source Schur-square profile.
-/

open Matrix
open scoped NNReal CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty
open HilbertMetric.Clipped RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def correlationPowerGram (f : C_c(ℝ, ℝ)) (p : ℕ) (time : ι → ℝ) : Matrix ι ι ℂ :=
  fun i j => ((autocorr f (time i - time j) ^ p : ℝ) : ℂ)

omit [Fintype ι] [DecidableEq ι] in
theorem correlationPowerGram_hermitian (f : C_c(ℝ, ℝ)) (p : ℕ) (time : ι → ℝ) :
    (correlationPowerGram f p time).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, correlationPowerGram, Complex.star_def,
    Complex.conj_ofReal]
  rw [show time j - time i = -(time i - time j) by ring, autocorr_neg]

/-- All replica powers retain their centered correlation moment after clipping. -/
theorem correlationPower_clippedDefect (f : C_c(ℝ, ℝ)) (p : ℕ) (time : ι → ℝ) (τ : ℝ≥0) :
    min ((∑ i, ∑ j, autocorr f (time i - time j) ^ (p * 2)) -
      2 * ((Fintype.card ι : ℝ) * autocorr f 0 ^ p) + Fintype.card ι) ((τ : ℝ) ^ 2) ≤
        defectEnergy τ (correlationPowerGram f p time) := by
  have hH := correlationPowerGram_hermitian f p time
  have h := defectEnergy_min_bound hH τ
  rw [trace_square hH] at h
  have ht : (trace (correlationPowerGram f p time)).re =
      (Fintype.card ι : ℝ) * autocorr f 0 ^ p := by
    change (∑ i : ι, ((autocorr f (time i - time i) ^ p : ℝ) : ℂ)).re = _
    simp only [sub_self]
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simpa only [ht, correlationPowerGram, Complex.normSq_ofReal, ← pow_two, ← pow_mul] using h

/-- Tensor-source squared correlations retain an explicit fourth-order overlap surplus. -/
theorem schurSquare_clippedDefect (f : C_c(ℝ, ℝ)) (time : ι → ℝ) (τ : ℝ≥0) :
    min ((∑ i, ∑ j, autocorr f (time i - time j) ^ 4) -
      2 * ((Fintype.card ι : ℝ) * SchurSquare.profile f 0) + Fintype.card ι) ((τ : ℝ) ^ 2) ≤
        defectEnergy τ (Matrix.of fun i j => (SchurSquare.profile f (time i - time j) : ℂ)) := by
  exact correlationPower_clippedDefect f 2 time τ

#print axioms correlationPower_clippedDefect
#print axioms schurSquare_clippedDefect

end
end GaloisForLFunctions.BiScaleUncertainty
