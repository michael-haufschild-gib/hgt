import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateSatisfiesTheWeakEquation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.FourierModulusDeterminesActualCorrelation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ThePairedReflectionPreservesTheActualDomain

/-!
# Skew Fourier pairs cancel the prime and Gamma mixed forms

Pointwise orthogonality of two Fourier transforms gives equal moduli for
their sum and difference. Fourier determination of translated correlations
then cancels the entire absolutely convergent prime mixed series.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23 FourierTransform
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry

private theorem norm_add_eq_norm_sub_of_real_orthogonal (z w : ℂ)
    (h : z.re * w.re + z.im * w.im = 0) : ‖z + w‖ = ‖z - w‖ := by
  have he : ‖z + w‖ ^ 2 = ‖z - w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    nlinarith only [h]
  nlinarith only [he, norm_nonneg (z + w), norm_nonneg (z - w)]

private theorem primeSum_eq_of_domain_fourier_norm {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hn : ∀ ξ, ‖𝓕 (cx F) ξ‖ = ‖𝓕 (cx G) ξ‖) : primeSum F = primeSum G := by
  have hc (t : ℝ) : (∫ u, F u * F (u + t)) = ∫ u, G u * G (u + t) := by
    have he := integral_conj_mul_translate_eq_of_fourier_norm
      (hF.integrable.ofReal (𝕜 := ℂ)) hF.memLp_complex
      (hG.integrable.ofReal (𝕜 := ℂ)) hG.memLp_complex (Eventually.of_forall hn) t
    change (∫ u, (starRingEnd ℂ) (F u : ℂ) * (F (u + t) : ℂ)) =
      ∫ u, (starRingEnd ℂ) (G u : ℂ) * (G (u + t) : ℂ) at he
    simp only [Complex.conj_ofReal, ← Complex.ofReal_mul] at he
    rw [integral_complex_ofReal, integral_complex_ofReal] at he
    exact Complex.ofReal_inj.mp he
  unfold primeSum
  apply tsum_congr
  intro n
  have hm := hc (-Real.log n)
  simp only [← sub_eq_add_neg] at hm
  rw [hm, hc]

/-- Pointwise skewness cancels both complete arithmetic mixed contributions. -/
theorem arithmetic_mixed_eq_zero_of_fourier_pair_zero {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hpair : ∀ r, gammaFourierPair F G r = 0) :
    gammaMixedForm F G = 0 ∧ primeMixedForm F G + primeMixedForm G F = 0 := by
  constructor
  · unfold gammaMixedForm
    simp only [hpair, zero_mul, integral_zero, mul_zero]
  · have hn (r : ℝ) :
        ‖paperFT (cx (fun u => F u + (1 : ℝ) * G u)) r‖ =
          ‖paperFT (cx (fun u => F u + (-1 : ℝ) * G u)) r‖ := by
      rw [paperFT_cx_add_const_mul hF.integrable hG.integrable,
        paperFT_cx_add_const_mul hF.integrable hG.integrable]
      simp only [Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul,
        ← sub_eq_add_neg]
      exact norm_add_eq_norm_sub_of_real_orthogonal _ _ (hpair r)
    have hfourier (ξ : ℝ) :
        ‖𝓕 (cx (fun u => F u + (1 : ℝ) * G u)) ξ‖ =
          ‖𝓕 (cx (fun u => F u + (-1 : ℝ) * G u)) ξ‖ := by
      have he := hn (-(2 * Real.pi * ξ))
      simp only [paperFT_ofReal_eq_fourier] at he
      have hs : -(-(2 * Real.pi * ξ)) / (2 * Real.pi) = ξ := by
        field_simp [Real.pi_ne_zero]
      simpa only [hs] using he
    have he := primeSum_eq_of_domain_fourier_norm
      (hF.add_const_mul hG 1) (hF.add_const_mul hG (-1)) hfourier
    rw [primeSum_add_const_mul hF.weighted hG.weighted,
      primeSum_add_const_mul hF.weighted hG.weighted] at he
    nlinarith only [he]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
