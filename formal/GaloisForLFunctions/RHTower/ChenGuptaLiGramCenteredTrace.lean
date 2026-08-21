import GaloisForLFunctions.RHTower.ChenGuptaLiCenteredCubicSpectrum
import GaloisForLFunctions.HTGeometry.RankEnergyPowerSum
import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget

open scoped ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace RHTower

/-- The nonnegative eigenvalue spectrum of the row-side Gram matrix `A Aᴴ`. -/
def CGLGramSpectrum (R N : ℕ) (A : Matrix (Fin (R + 1)) (Fin N) ℂ) :
    Fin (R + 1) → NNReal := fun i =>
  ⟨(Matrix.posSemidef_self_mul_conjTranspose A).1.eigenvalues i,
    (Matrix.posSemidef_self_mul_conjTranspose A).eigenvalues_nonneg i⟩

theorem cglGramSpectrum_coe (R N : ℕ) (A : Matrix (Fin (R + 1)) (Fin N) ℂ)
    (i : Fin (R + 1)) :
    (CGLGramSpectrum R N A i : ℝ) =
      (Matrix.posSemidef_self_mul_conjTranspose A).1.eigenvalues i := rfl

theorem sum_cglGramSpectrum_eq_trace (R N : ℕ) (A : Matrix (Fin (R + 1)) (Fin N) ℂ) :
    ∑ i, (CGLGramSpectrum R N A i : ℝ) = ((A * Aᴴ).trace).re := by
  let hG : (A * Aᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  change (∑ i, hG.1.eigenvalues i) = ((A * Aᴴ).trace).re
  have htrace := GaloisForLFunctions.HTGeometry.trace_pow_eq_sum_eigenvalues_pow hG.1 1
  simp only [pow_one] at htrace
  rw [htrace, Complex.re_sum]
  simp

theorem sum_cube_cglGramSpectrum_eq_trace (R N : ℕ)
    (A : Matrix (Fin (R + 1)) (Fin N) ℂ) :
    ∑ i, (CGLGramSpectrum R N A i : ℝ) ^ 3 = ((A * Aᴴ) ^ 3).trace.re := by
  let hG : (A * Aᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  change (∑ i, hG.1.eigenvalues i ^ 3) = ((A * Aᴴ) ^ 3).trace.re
  rw [GaloisForLFunctions.HTGeometry.trace_pow_eq_sum_eigenvalues_pow hG.1 3, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem cglGramSpectrumMean_eq_trace (R N : ℕ) (A : Matrix (Fin (R + 1)) (Fin N) ℂ) :
    CGLSpectrumMean R (CGLGramSpectrum R N A) = ((A * Aᴴ).trace).re / (R + 1 : ℝ) := by
  unfold CGLSpectrumMean
  rw [sum_cglGramSpectrum_eq_trace]

theorem cglGramCenteredCubicDeviation_eq_trace (R N : ℕ)
    (A : Matrix (Fin (R + 1)) (Fin N) ℂ) :
    CGLCenteredCubicDeviation R (CGLGramSpectrum R N A) =
      ((A * Aᴴ) ^ 3).trace.re - ((A * Aᴴ).trace.re ^ 3) / (R + 1 : ℝ) ^ 2 := by
  unfold CGLCenteredCubicDeviation
  rw [sum_cube_cglGramSpectrum_eq_trace, cglGramSpectrumMean_eq_trace]
  field_simp

theorem cglGram_operatorNorm_le_spectrum_twoConstantBound (R N : ℕ)
    (A : Matrix (Fin (R + 1)) (Fin N) ℂ) :
    ‖A‖ ≤ 2 * CGLCenteredCubicDeviation R (CGLGramSpectrum R N A) ^ (1 / 6 : ℝ) +
      2 * √(CGLSpectrumMean R (CGLGramSpectrum R N A)) := by
  let hG : (A * Aᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  let B : ℝ := 2 * CGLCenteredCubicDeviation R (CGLGramSpectrum R N A) ^ (1 / 6 : ℝ) +
    2 * √(CGLSpectrumMean R (CGLGramSpectrum R N A))
  have hB : 0 ≤ B := by
    dsimp [B]
    have hD : 0 ≤ CGLCenteredCubicDeviation R (CGLGramSpectrum R N A) :=
      cglCenteredCubicDeviation_nonneg R _
    have hμ : 0 ≤ CGLSpectrumMean R (CGLGramSpectrum R N A) := by
      unfold CGLSpectrumMean
      positivity
    positivity
  have hcoord : ∀ i : Fin (R + 1), hG.1.eigenvalues i ≤ B ^ 2 := by
    intro i
    have hpoint := sqrt_cglSpectrum_coordinate_le_twoConstantBound R (CGLGramSpectrum R N A) i
    have hsquare : √(CGLGramSpectrum R N A i : ℝ) ^ 2 = (CGLGramSpectrum R N A i : ℝ) :=
      Real.sq_sqrt (by positivity)
    change (CGLGramSpectrum R N A i : ℝ) ≤ B ^ 2
    change √(CGLGramSpectrum R N A i : ℝ) ≤ B at hpoint
    nlinarith [Real.sqrt_nonneg (CGLGramSpectrum R N A i : ℝ)]
  have hdiag : A * Aᴴ = (hG.1.eigenvectorUnitary : Matrix (Fin (R + 1)) (Fin (R + 1)) ℂ) *
      Matrix.diagonal (fun i => (hG.1.eigenvalues i : ℂ)) *
        star (hG.1.eigenvectorUnitary : Matrix (Fin (R + 1)) (Fin (R + 1)) ℂ) :=
    GaloisForLFunctions.HTGeometry.isHermitian_eq_conj_diagonal hG.1
  have hgram : ‖A * Aᴴ‖ = ‖A‖ * ‖A‖ := by
    calc
      ‖A * Aᴴ‖ = ‖(Aᴴ)ᴴ * Aᴴ‖ := by simp
      _ = ‖Aᴴ‖ * ‖Aᴴ‖ := Matrix.l2_opNorm_conjTranspose_mul_self Aᴴ
      _ = ‖A‖ * ‖A‖ := by rw [Matrix.l2_opNorm_conjTranspose]
  have hgramBound : ‖A * Aᴴ‖ ≤ B ^ 2 := by
    rw [hdiag, GaloisForLFunctions.HTGeometry.l2_opNorm_unitary_conj_eq hG.1.eigenvectorUnitary.2,
      Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonempty _).mpr fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hG.eigenvalues_nonneg i)]
    exact hcoord i
  have hsq : ‖A‖ ^ 2 ≤ B ^ 2 := by
    rw [pow_two, ← hgram]
    exact hgramBound
  exact by nlinarith [norm_nonneg A]

/-- CGL Lemma 4.2 for a literal nonempty finite complex matrix. -/
theorem cglLemmaFourPointTwo_finite (R N : ℕ) (A : Matrix (Fin (R + 1)) (Fin N) ℂ) :
    ‖A‖ ≤
      2 * (((A * Aᴴ) ^ 3).trace.re - ((A * Aᴴ).trace.re ^ 3) / (R + 1 : ℝ) ^ 2) ^
        (1 / 6 : ℝ) +
      2 * √(((A * Aᴴ).trace.re) / (R + 1 : ℝ)) := by
  have h := cglGram_operatorNorm_le_spectrum_twoConstantBound R N A
  rw [cglGramCenteredCubicDeviation_eq_trace, cglGramSpectrumMean_eq_trace] at h
  exact h

end RHTower
