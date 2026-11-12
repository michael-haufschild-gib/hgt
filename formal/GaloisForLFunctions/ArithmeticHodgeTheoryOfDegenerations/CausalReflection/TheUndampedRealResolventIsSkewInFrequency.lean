import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheUndampedRealResolventHasTheActualDomain
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SkewFourierPairsHaveZeroArithmeticMixedForm

/-!
# Arithmetic mixed cancellation for the real undamped resolvent

Averaging the two conjugate resolvent equations gives a purely imaginary
multiplier. At either resonant frequency the original transform vanishes.
Thus Fourier orthogonality holds everywhere, and both arithmetic mixed
terms cancel on the actual energy domain.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23 FourierTransform
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry

private theorem orthogonal_of_imaginary_multiplier {a c : ℝ} (ha : a ≠ 0)
    {z w : ℂ} (he : (a : ℂ) * Complex.I * w = (c : ℂ) * z) :
    z.re * w.re + z.im * w.im = 0 := by
  have hp : a * (z.re * w.re + z.im * w.im) = 0 := by
    calc
      _ = ((starRingEnd ℂ) z * ((a : ℂ) * Complex.I * w)).im := by
        simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
        ring
      _ = ((starRingEnd ℂ) z * ((c : ℂ) * z)).im := by rw [he]
      _ = 0 := by
        simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.conj_re, Complex.conj_im]
        ring
  exact (mul_eq_zero.mp hp).resolve_left ha

/-- The real undamped resolvent is pointwise Fourier-orthogonal to its input,
including both resonances. -/
theorem gammaFourierPair_realUndampedCausalConvolution (b : ℝ)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 b) = 0) (r : ℝ) :
    gammaFourierPair F (realUndampedCausalConvolution b F) r = 0 := by
  have hm : Measurable (cx F) := Complex.continuous_ofReal.measurable.comp hF.meas
  have hf : Integrable (cx F) := hF.integrable.ofReal (𝕜 := ℂ)
  have hs : ∀ u, 0 ≤ u → cx F u = 0 := by
    intro u hu
    change (F u : ℂ) = 0
    rw [hF.support u hu, Complex.ofReal_zero]
  have hneg := undamped_conjugate_laplace_zero b hz
  have hK := (undampedCausalConvolution_memLp_and_integrable
    b hm hF.memLp_weightedComplex hs hz).2
  have hKneg := (undampedCausalConvolution_memLp_and_integrable
    (-b) hm hF.memLp_weightedComplex hs hneg).2
  let ξ := -r / (2 * Real.pi)
  have hp := fourier_undampedCausalConvolution_mul b hm hf hF.memLp_weightedComplex hs hz ξ
  have hn := fourier_undampedCausalConvolution_mul (-b) hm hf hF.memLp_weightedComplex hs hneg ξ
  have hH := paperFT_realUndampedCausalConvolution b hK hKneg r
  simp only [paperFT_ofReal_eq_fourier] at hH
  change 𝓕 (cx (realUndampedCausalConvolution b F)) ξ =
    (1 / 2 : ℂ) * (𝓕 (modulatedCausalConvolution 0 b (cx F)) ξ +
      𝓕 (modulatedCausalConvolution 0 (-b) (cx F)) ξ) at hH
  unfold gammaFourierPair
  simp only [paperFT_ofReal_eq_fourier]
  change (𝓕 (cx F) ξ).re * (𝓕 (cx (realUndampedCausalConvolution b F)) ξ).re +
    (𝓕 (cx F) ξ).im * (𝓕 (cx (realUndampedCausalConvolution b F)) ξ).im = 0
  by_cases hres : ξ = -b
  · have hzero : 𝓕 (cx F) ξ = 0 := by
      simpa only [hres, add_neg_cancel, mul_zero, Complex.ofReal_zero, zero_mul] using hp.symm
    rw [hzero, Complex.zero_re, Complex.zero_im, zero_mul, zero_mul, add_zero]
  by_cases hres' : ξ = b
  · have hzero : 𝓕 (cx F) ξ = 0 := by
      simpa only [hres', neg_add_cancel, mul_zero, Complex.ofReal_zero, zero_mul] using hn.symm
    rw [hzero, Complex.zero_re, Complex.zero_im, zero_mul, zero_mul, add_zero]
  have hcoef : 2 * (ξ ^ 2 - b ^ 2) ≠ 0 := by
    rw [show ξ ^ 2 - b ^ 2 = (ξ - b) * (ξ + b) by ring]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero (sub_ne_zero.mpr hres') (by
        intro he
        apply hres
        linarith only [he]))
  apply orthogonal_of_imaginary_multiplier hcoef (c := ξ)
  rw [hH]
  calc
    _ = (((ξ - b) / 2 : ℝ) : ℂ) *
          (((2 * (b + ξ) : ℝ) : ℂ) * Complex.I *
            𝓕 (modulatedCausalConvolution 0 b (cx F)) ξ) +
        (((ξ + b) / 2 : ℝ) : ℂ) *
          (((2 * (-b + ξ) : ℝ) : ℂ) * Complex.I *
            𝓕 (modulatedCausalConvolution 0 (-b) (cx F)) ξ) := by
      push_cast
      ring
    _ = _ := by rw [hp, hn]; push_cast; ring

/-- The complete prime and Gamma mixed terms vanish for the admitted real
resolvent at every imaginary-axis Laplace zero. -/
theorem arithmetic_mixed_realUndampedCausalConvolution_eq_zero (b : ℝ)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 b) = 0) :
    gammaMixedForm F (realUndampedCausalConvolution b F) = 0 ∧
      primeMixedForm F (realUndampedCausalConvolution b F) +
        primeMixedForm (realUndampedCausalConvolution b F) F = 0 :=
  arithmetic_mixed_eq_zero_of_fourier_pair_zero hF
    (hF.realUndampedCausalConvolution b hz)
    (gammaFourierPair_realUndampedCausalConvolution b hF hz)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
