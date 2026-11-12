import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ThePairedReflectionPreservesTheActualDomain
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.FourierModulusDeterminesActualCorrelation

/-!
# Prime, Gamma and pole energy survive the conjugate pair

Fourier modulus determines every actual translated correlation, so the
prime sum is unchanged. The two half-pole Laplace values give the pole
product, which is preserved by the conjugate pair's reciprocal factors.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23 FourierTransform
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry

/-- Every actual real translated correlation is preserved by the conjugate pair. -/
theorem integral_mul_translate_realPairedCausalReflection {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : b ≠ 0) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0) (t : ℝ) :
    (∫ u, realPairedCausalReflection a b F u * realPairedCausalReflection a b F (u + t)) =
      ∫ u, F u * F (u + t) := by
  have hH := hF.realPairedCausalReflection ha hb hz
  have hmod : ∀ᵐ ξ : ℝ, ‖𝓕 (cx (realPairedCausalReflection a b F)) ξ‖ = ‖𝓕 (cx F) ξ‖ :=
    Eventually.of_forall (norm_fourier_realPairedCausalReflection ha b hF.integrable)
  have hc := integral_conj_mul_translate_eq_of_fourier_norm
    (hH.integrable.ofReal (𝕜 := ℂ)) hH.memLp_complex
    (hF.integrable.ofReal (𝕜 := ℂ)) hF.memLp_complex hmod t
  change (∫ u, (starRingEnd ℂ) (realPairedCausalReflection a b F u : ℂ) *
      (realPairedCausalReflection a b F (u + t) : ℂ)) =
    ∫ u, (starRingEnd ℂ) (F u : ℂ) * (F (u + t) : ℂ) at hc
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul] at hc
  rw [integral_complex_ofReal, integral_complex_ofReal] at hc
  exact Complex.ofReal_inj.mp hc

/-- The complete actual prime sum is unchanged. -/
theorem primeSum_realPairedCausalReflection {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : b ≠ 0) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0) :
    primeSum (realPairedCausalReflection a b F) = primeSum F := by
  unfold primeSum
  apply tsum_congr
  intro n
  have hm := integral_mul_translate_realPairedCausalReflection ha hb hF hz (-Real.log n)
  simp only [← sub_eq_add_neg] at hm
  rw [hm, integral_mul_translate_realPairedCausalReflection ha hb hF hz]

/-- Real Laplace arguments recover the literal real integral. -/
theorem negativeHalfLineLaplace_ofReal (s : ℝ) (F : ℝ → ℝ) :
    negativeHalfLineLaplace (cx F) (s : ℂ) = ((∫ u, F u * Real.exp (s * u) : ℝ) : ℂ) := by
  calc
    _ = ∫ u, ((F u * Real.exp (s * u) : ℝ) : ℂ) := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      change Complex.exp ((s : ℂ) * (u : ℂ)) * (F u : ℂ) =
        ((F u * Real.exp (s * u) : ℝ) : ℂ)
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
      congr 1
      exact mul_comm _ _
    _ = _ := integral_complex_ofReal

/-- The opposite half-pole Laplace values are the cosh/sinh sum and difference. -/
theorem negativeHalfLineLaplace_halfPole_real {F : ℝ → ℝ} (hF : WeightedTwo F) :
    negativeHalfLineLaplace (cx F) ((1 / 2 : ℝ) : ℂ) =
        ((coshHalfMoment F + sinhHalfMoment F : ℝ) : ℂ) ∧
      negativeHalfLineLaplace (cx F) (-((1 / 2 : ℝ) : ℂ)) =
        ((coshHalfMoment F - sinhHalfMoment F : ℝ) : ℂ) := by
  have hc := (abs_integral_mul_kernel_le hF
    (Real.continuous_cosh.comp (continuous_id.div_const 2)) abs_cosh_half_le_exp).1
  have hs := (abs_integral_mul_kernel_le hF
    (Real.continuous_sinh.comp (continuous_id.div_const 2)) abs_sinh_half_le_exp).1
  have hp : (∫ u, F u * Real.exp ((1 / 2 : ℝ) * u)) = coshHalfMoment F + sinhHalfMoment F := by
    have he (u : ℝ) : F u * Real.exp ((1 / 2 : ℝ) * u) =
        F u * Real.cosh (u / 2) + F u * Real.sinh (u / 2) := by
      rw [show (1 / 2 : ℝ) * u = u / 2 by ring, Real.cosh_eq, Real.sinh_eq]
      ring
    change (∫ u, F u * Real.exp ((1 / 2 : ℝ) * u)) =
      (∫ u, F u * Real.cosh (u / 2)) + ∫ u, F u * Real.sinh (u / 2)
    simp_rw [he]
    exact integral_add hc hs
  have hm : (∫ u, F u * Real.exp (-(1 / 2 : ℝ) * u)) = coshHalfMoment F - sinhHalfMoment F := by
    have he (u : ℝ) : F u * Real.exp (-(1 / 2 : ℝ) * u) =
        F u * Real.cosh (u / 2) - F u * Real.sinh (u / 2) := by
      rw [show -(1 / 2 : ℝ) * u = -(u / 2) by ring, Real.cosh_eq, Real.sinh_eq]
      ring
    change (∫ u, F u * Real.exp (-(1 / 2 : ℝ) * u)) =
      (∫ u, F u * Real.cosh (u / 2)) - ∫ u, F u * Real.sinh (u / 2)
    simp_rw [he]
    exact integral_sub hc hs
  constructor
  · rw [negativeHalfLineLaplace_ofReal, hp]
  · rw [← Complex.ofReal_neg, negativeHalfLineLaplace_ofReal, hm]

/-- The actual real pole term is preserved at every nonreal right-half-plane zero. -/
theorem poleTerm_realPairedCausalReflection {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : b ≠ 0) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0) :
    2 * coshHalfMoment (realPairedCausalReflection a b F) ^ 2 -
        2 * sinhHalfMoment (realPairedCausalReflection a b F) ^ 2 =
      2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2 := by
  have hH := hF.realPairedCausalReflection ha hb hz
  have he : cx (realPairedCausalReflection a b F) =ᵐ[volume]
      pairedCausalReflection a b (cx F) := coe_realPairedCausalReflection_ae ha b hF.integrable
  have hl (q : ℂ) : negativeHalfLineLaplace (cx (realPairedCausalReflection a b F)) q =
      negativeHalfLineLaplace (pairedCausalReflection a b (cx F)) q := by
    apply integral_congr_ae
    filter_upwards [he] with u hu
    exact congrArg (fun z : ℂ => Complex.exp (q * (u : ℂ)) * z) hu
  have hp := pairedCausalReflection_laplace_pair ha hb hF.integrable
    hF.memLp_complex hF.memLp_weightedComplex hF.support hz (s := 1 / 2) (by norm_num)
  change negativeHalfLineLaplace (pairedCausalReflection a b (cx F)) ((1 / 2 : ℝ) : ℂ) *
      negativeHalfLineLaplace (pairedCausalReflection a b (cx F)) (-((1 / 2 : ℝ) : ℂ)) =
    negativeHalfLineLaplace (cx F) ((1 / 2 : ℝ) : ℂ) *
      negativeHalfLineLaplace (cx F) (-((1 / 2 : ℝ) : ℂ)) at hp
  obtain ⟨hHplus, hHminus⟩ := negativeHalfLineLaplace_halfPole_real hH.weighted
  obtain ⟨hFplus, hFminus⟩ := negativeHalfLineLaplace_halfPole_real hF.weighted
  rw [← hl _, ← hl _, hHplus, hHminus, hFplus, hFminus] at hp
  have hr : (coshHalfMoment (realPairedCausalReflection a b F) +
      sinhHalfMoment (realPairedCausalReflection a b F)) *
      (coshHalfMoment (realPairedCausalReflection a b F) -
        sinhHalfMoment (realPairedCausalReflection a b F)) =
      (coshHalfMoment F + sinhHalfMoment F) * (coshHalfMoment F - sinhHalfMoment F) := by
    exact_mod_cast hp
  nlinarith only [hr]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
