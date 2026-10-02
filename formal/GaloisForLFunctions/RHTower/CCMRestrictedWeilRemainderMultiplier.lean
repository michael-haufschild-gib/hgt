import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarConvolution
import GaloisForLFunctions.RHTower.CCMPolarPrimeExponentialFrequencyCancellation
import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundFrequencyLocalization
import GaloisForLFunctions.RHTower.CCMFiniteExponentialRemainderTail

/-!
# Exact full-line multiplier of the actual bounded Weil remainder

The complete prime-power translation sum and crossed polar convolution,
including the scalar atom, give a full-line operator whose compression is
exactly the actual bounded remainder. Its Fourier cofunction has the
corrected polar-prime symbol at the exact Fourier frequency. A uniform
aperture-scale norm bound controls the complementary source tail.
-/

open MeasureTheory Set Filter
open scoped FourierTransform InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- All prime translations before the physical aperture compression. -/
def ccmFullLinePrimeOperator (a : SuzukiPositiveAperture) : SoninL2 →L[ℂ] SoninL2 :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
    (criticalMellinAtomWeight n : ℂ) • ccmSymmetricLogTranslation (Real.log n)

/-- The uncompressed full remainder, including its actual scalar atom. -/
def ccmFullLineBoundedRemainder (a : SuzukiPositiveAperture) : SoninL2 →L[ℂ] SoninL2 :=
  ccmArchimedeanRemainderScalar • 1 + ccmPolarConvolution a - ccmFullLinePrimeOperator a

theorem ccmFinitePrimeOperator_eq_compressed_fullLine (a : SuzukiPositiveAperture) :
    ccmFinitePrimeOperator a = ccmApertureCompression a (ccmFullLinePrimeOperator a) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ccmFinitePrimeOperator, ccmFullLinePrimeOperator, ccmPrimeTransportOperator,
    ccmApertureCompression, sum_apply, smul_apply, ContinuousLinearMap.comp_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [smul_smul, criticalMellinAtomWeight_eq_div_sqrt]
  congr 1
  push_cast
  ring

/-- The literal full remainder is the compression of the full-line operator. -/
theorem ccmRestrictedWeilBoundedRemainder_eq_compressed_fullLine (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilBoundedRemainder a =
      ccmApertureCompression a (ccmFullLineBoundedRemainder a) := by
  apply ContinuousLinearMap.ext
  intro f
  have hi : ccmApertureCompression a 1 f = f := by
    apply Subtype.ext
    rw [ccmApertureCompression_val, one_apply_eq_self, indicatorCutoff_suzukiApertureHilbert]
  change (suzukiApertureHilbert a).subtypeL.adjoint ((suzukiApertureHilbert a).subtypeL f) = f at hi
  rw [ccmRestrictedWeilBoundedRemainder, ccmPolarOperator_eq_compressed_convolution,
    ccmFinitePrimeOperator_eq_compressed_fullLine]
  simp only [ccmFullLineBoundedRemainder, ccmApertureCompression, sub_apply,
    add_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub, map_add, map_smul, hi]

private theorem fourier_translation_ae (h : ℝ) (f : SoninL2) :
    (fourierUnitary (logTranslationCLM h f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => MellinL2.fourierPhase h ξ * fourierUnitary f ξ := by
  have he : fourierUnitary (logTranslationCLM h f) =
      MellinL2.fourierPhaseMulUnitary h (fourierUnitary f) :=
    MellinL2.fourier_additiveTranslation h f
  rw [he]
  exact MellinL2.fourierPhaseMulAux_ae h (fourierUnitary f)

private theorem phase_pair (h ξ : ℝ) :
    MellinL2.fourierPhase h ξ + MellinL2.fourierPhase (-h) ξ =
      ((2 * Real.cos ((-2 * Real.pi * ξ) * h) : ℝ) : ℂ) := by
  have he (s : ℝ) : MellinL2.fourierPhase s ξ =
      Complex.exp (((2 * Real.pi * ξ * s : ℝ) : ℂ) * Complex.I) := by
    simp only [MellinL2.fourierPhase, Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [he h, he (-h), show 2 * Real.pi * ξ * -h = -(2 * Real.pi * ξ * h) by ring,
    show (-2 * Real.pi * ξ) * h = -(2 * Real.pi * ξ * h) by ring,
    Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, Real.cos_neg]
  push_cast
  ring

private theorem fourier_symmetric_translation_ae (h : ℝ) (f : SoninL2) :
    (fourierUnitary (ccmSymmetricLogTranslation h f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => ((2 * Real.cos ((-2 * Real.pi * ξ) * h) : ℝ) : ℂ) * fourierUnitary f ξ := by
  simp only [ccmSymmetricLogTranslation, add_apply, map_add]
  filter_upwards [Lp.coeFn_add (fourierUnitary (logTranslationCLM h f))
    (fourierUnitary (logTranslationCLM (-h) f)), fourier_translation_ae h f,
    fourier_translation_ae (-h) f] with ξ ha hp hm
  rw [ha, Pi.add_apply, hp, hm, ← add_mul, phase_pair]

private theorem fourier_prime_sum_ae (S : Finset ℕ) (f : SoninL2) :
    (fourierUnitary (∑ n ∈ S, (criticalMellinAtomWeight n : ℂ) •
      ccmSymmetricLogTranslation (Real.log n) f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (∑ n ∈ S, (criticalMellinAtomWeight n : ℂ) *
        ((2 * Real.cos ((-2 * Real.pi * ξ) * Real.log n) : ℝ) : ℂ)) * fourierUnitary f ξ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, map_zero, zero_mul]
      exact Lp.coeFn_zero ℂ 2 volume
  | @insert n S hn ih =>
      simp only [Finset.sum_insert hn, map_add, map_smul]
      filter_upwards [Lp.coeFn_add
        ((criticalMellinAtomWeight n : ℂ) • fourierUnitary (ccmSymmetricLogTranslation (Real.log n) f))
        (fourierUnitary (∑ k ∈ S, (criticalMellinAtomWeight k : ℂ) •
          ccmSymmetricLogTranslation (Real.log k) f)),
        Lp.coeFn_smul (criticalMellinAtomWeight n : ℂ)
          (fourierUnitary (ccmSymmetricLogTranslation (Real.log n) f)),
        fourier_symmetric_translation_ae (Real.log n) f, ih] with ξ ha hs ht hi
      rw [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, ht, hi]
      ring

theorem fourier_ccmFullLinePrimeOperator_ae (a : SuzukiPositiveAperture) (f : SoninL2) :
    (fourierUnitary (ccmFullLinePrimeOperator a f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (criticalMellinPrimeCosineModule a.1 (-2 * Real.pi * ξ) : ℂ) * fourierUnitary f ξ := by
  simp only [ccmFullLinePrimeOperator, sum_apply, smul_apply]
  filter_upwards [fourier_prime_sum_ae (Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊) f] with ξ hξ
  rw [hξ]
  congr 1
  simp only [criticalMellinPrimeCosineModule]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem fourier_ccmPolarConvolution_ae (a : SuzukiPositiveAperture) (f : SoninL2) :
    (fourierUnitary (ccmPolarConvolution a f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (polarMultiplier a.1 (-2 * Real.pi * ξ) : ℂ) * fourierUnitary f ξ := by
  have he : fourierUnitary (ccmPolarConvolution a f) =
      lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (continuous_fourier_of_integrable' (integrable_ccmPolarConvolutionProfile a)).measurable
        (integral_nonneg fun x => norm_nonneg (ccmPolarConvolutionProfile a x))
        (norm_fourier_apply_le_integral_norm (ccmPolarConvolutionProfile a)) (fourierUnitary f) := by
    change fourierL2 ℝ (ccmPolarConvolution a f) = _
    rw [ccmPolarConvolution, convolutionKernel_op_eq_fourierMulCLM,
      fourierMulCLM_apply, fourierL2_fourierL2inv]
    rfl
  rw [he]
  have hc := lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (continuous_fourier_of_integrable' (integrable_ccmPolarConvolutionProfile a)).measurable
    (integral_nonneg fun x => norm_nonneg (ccmPolarConvolutionProfile a x))
    (norm_fourier_apply_le_integral_norm (ccmPolarConvolutionProfile a)) (fourierUnitary f)
  filter_upwards [hc] with ξ hξ
  rw [hξ, fourier_ccmPolarConvolutionProfile]

/-- Exact Fourier symbol of the full uncompressed remainder, retaining the
scalar, both polar channels and every prime-power translation. -/
theorem fourier_ccmFullLineBoundedRemainder_ae (a : SuzukiPositiveAperture) (f : SoninL2) :
    (fourierUnitary (ccmFullLineBoundedRemainder a f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (ccmArchimedeanRemainderScalar +
        (polarPrimeStieltjesSymbol a.1 (-2 * Real.pi * ξ) : ℂ)) * fourierUnitary f ξ := by
  simp only [ccmFullLineBoundedRemainder, sub_apply, add_apply, smul_apply,
    one_apply_eq_self, map_sub, map_add, map_smul]
  filter_upwards [Lp.coeFn_sub
    (ccmArchimedeanRemainderScalar • fourierUnitary f + fourierUnitary (ccmPolarConvolution a f))
    (fourierUnitary (ccmFullLinePrimeOperator a f)),
    Lp.coeFn_add (ccmArchimedeanRemainderScalar • fourierUnitary f)
      (fourierUnitary (ccmPolarConvolution a f)),
    Lp.coeFn_smul ccmArchimedeanRemainderScalar (fourierUnitary f),
    fourier_ccmPolarConvolution_ae a f, fourier_ccmFullLinePrimeOperator_ae a f] with ξ hs ha hc hp ht
  rw [hs, Pi.sub_apply, ha, Pi.add_apply, hc, Pi.smul_apply, smul_eq_mul, hp, ht]
  simp only [polarPrimeStieltjesSymbol, Complex.ofReal_sub]
  ring

private theorem complete_prime_weight_sum_le (a : SuzukiPositiveAperture) :
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, criticalMellinAtomWeight n) ≤
      21 * Real.exp a.1 := by
  simp_rw [criticalMellinAtomWeight_eq_div_sqrt]
  have hsub : Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊ ⊆ Finset.Icc 0 ⌊Real.exp (2 * a.1)⌋₊ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hn).2⟩
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (Real.sqrt_nonneg (n : ℝ)))
  have hp := primeMassHalf_le_sqrt (Real.one_le_exp (show 0 ≤ 2 * a.1 by linarith [a.2]))
  have he : Real.sqrt (Real.exp (2 * a.1)) = Real.exp a.1 := by
    rw [show 2 * a.1 = a.1 + a.1 by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos a.1).le]
  rw [he] at hp
  exact hs.trans hp

/-- Complete uncompressed prime transport has a global aperture-scale bound. -/
theorem norm_ccmFullLinePrimeOperator_le (a : SuzukiPositiveAperture) :
    ‖ccmFullLinePrimeOperator a‖ ≤ 42 * Real.exp a.1 := by
  have hn (n : ℕ) : 0 ≤ criticalMellinAtomWeight n := by
    rw [criticalMellinAtomWeight_eq_div_sqrt]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  unfold ccmFullLinePrimeOperator
  calc
    _ ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ‖(criticalMellinAtomWeight n : ℂ) • ccmSymmetricLogTranslation (Real.log n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, criticalMellinAtomWeight n * 2 := by
      apply Finset.sum_le_sum
      intro n hnS
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn n)]
      exact mul_le_mul_of_nonneg_left (norm_ccmSymmetricLogTranslation_le_two _) (hn n)
    _ = (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, criticalMellinAtomWeight n) * 2 :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (21 * Real.exp a.1) * 2 := mul_le_mul_of_nonneg_right (complete_prime_weight_sum_le a) (by norm_num)
    _ = _ := by ring

/-- Global full-line norm control pays the Fourier tail, while the signed
symbol cancellation is reserved for the retained low-frequency band. -/
theorem norm_ccmFullLineBoundedRemainder_le (a : SuzukiPositiveAperture) :
    ‖ccmFullLineBoundedRemainder a‖ ≤
      (‖ccmArchimedeanRemainderScalar‖ + 46) * Real.exp a.1 := by
  have hk : ‖ccmArchimedeanRemainderScalar • (1 : SoninL2 →L[ℂ] SoninL2)‖ ≤
      ‖ccmArchimedeanRemainderScalar‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    change ‖ccmArchimedeanRemainderScalar • f‖ ≤ ‖ccmArchimedeanRemainderScalar‖ * ‖f‖
    exact (norm_smul _ _).le
  let A : SoninL2 →L[ℂ] SoninL2 := ccmArchimedeanRemainderScalar • 1
  let P := ccmPolarConvolution a
  let T := ccmFullLinePrimeOperator a
  have hsplit : ‖A + P - T‖ ≤ ‖A‖ + ‖P‖ + ‖T‖ :=
    (norm_sub_le (A + P) T).trans (add_le_add (norm_add_le A P) (le_refl ‖T‖))
  calc
    _ ≤ ‖A‖ + ‖P‖ + ‖T‖ := hsplit
    _ ≤ ‖ccmArchimedeanRemainderScalar‖ + 4 * Real.exp a.1 + 42 * Real.exp a.1 :=
      add_le_add (add_le_add hk (norm_ccmPolarConvolution_le a)) (norm_ccmFullLinePrimeOperator_le a)
    _ ≤ _ := by
      have hc := mul_le_mul_of_nonneg_left (Real.one_le_exp a.2.le)
        (norm_nonneg ccmArchimedeanRemainderScalar)
      nlinarith only [hc]

end RHTower
end
