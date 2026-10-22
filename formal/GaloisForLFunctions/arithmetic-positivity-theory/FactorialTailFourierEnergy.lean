import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailLevyEnergy
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanLogWeightEquivalence

/-! The actual factorial tail belongs to the logarithmic Fourier form domain
uniformly on the enlarged Mellin strip. The proof transports its physical jump
budget through the exact Gamma–Lévy identity and global weight comparison. -/

open MeasureTheory Set Filter
open scoped FourierTransform
open _root_.RHTower
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The complexified actual weighted source is admitted to the Fourier integral. -/
theorem factorialWeightedTail_complex_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Integrable (fun x : ℝ => (factorialWeightedTail n σ x : ℂ)) := by
  have hs : -1 < ((σ : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    have := σ.2.1
    linarith
  convert factorialMuntzCorrectedTail_readout_integrable n ((σ : ℝ) : ℂ) hs using 1
  funext x
  simp only [factorialWeightedTail,Complex.ofReal_mul,Complex.ofReal_exp,
    Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]

theorem factorialWeightedTail_complex_memLp (n : ℕ) (σ : FactorialSamplingAbscissa) :
    MemLp (fun x : ℝ => (factorialWeightedTail n σ x : ℂ)) 2 :=
  ((memLp_two_iff_integrable_sq
    (factorialWeightedTail_measurable n σ).aestronglyMeasurable).mpr
      (factorialWeightedTail_sq_integrable n σ)).ofReal

/-- Fourier readout in the unitary `2*pi` convention. -/
def factorialTailFourier (n : ℕ) (σ : ℝ) : ℝ → ℂ :=
  𝓕 (fun x : ℝ => (factorialWeightedTail n σ x : ℂ))

private theorem fourier_continuous (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Continuous (factorialTailFourier n σ) :=
  GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
    (factorialWeightedTail_complex_integrable n σ)

private theorem fourier_sq_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Integrable (fun ξ : ℝ => ‖factorialTailFourier n σ ξ‖^2) :=
  GaloisForLFunctions.RHTower.integrable_norm_sq_fourier
    (factorialWeightedTail_complex_integrable n σ) (factorialWeightedTail_complex_memLp n σ)

private theorem fourier_sq_integral (n : ℕ) (σ : FactorialSamplingAbscissa) :
    (∫ ξ : ℝ, ‖factorialTailFourier n σ ξ‖^2) =
      ∫ x : ℝ, factorialWeightedTail n σ x^2 := by
  rw [factorialTailFourier,GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq
    (factorialWeightedTail_complex_integrable n σ) (factorialWeightedTail_complex_memLp n σ)]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]

private def gammaExcessDensity (n : ℕ) (σ ξ : ℝ) : ℝ :=
  2*(gammaHardyPhaseRate (2*Real.pi*ξ)-gammaHardyPhaseRate 0)*
    ‖factorialTailFourier n σ ξ‖^2

private theorem gamma_excess_nonneg (n : ℕ) (σ ξ : ℝ) :
    0 ≤ gammaExcessDensity n σ ξ :=
  mul_nonneg (mul_nonneg (by norm_num)
    (sub_nonneg.mpr (gammaHardyPhaseRate_zero_le_levy _))) (sq_nonneg _)

private theorem gamma_excess_continuous (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Continuous (gammaExcessDensity n σ) :=
  (continuous_const.mul ((continuous_gammaHardyPhaseRate.comp
    (continuous_const.mul continuous_id)).sub continuous_const)).mul
      ((fourier_continuous n σ).norm.pow 2)

private theorem gamma_excess_lintegral (n : ℕ) (σ : FactorialSamplingAbscissa) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (gammaExcessDensity n σ ξ)) =
      ∫⁻ h : ℝ in Ioi 0,
        ENNReal.ofReal (archLevyDensity h*factorialTailTranslationEnergy n σ h) := by
  have he := lintegral_archSymbol_mul_normSq_fourier
    (factorialWeightedTail_complex_integrable n σ) (factorialWeightedTail_complex_memLp n σ)
  have hD (h : ℝ) : (∫ u : ℝ,
      ‖(factorialWeightedTail n σ u : ℂ)-(factorialWeightedTail n σ (u+h) : ℂ)‖^2) =
        factorialTailTranslationEnergy n σ h := by
    unfold factorialTailTranslationEnergy
    congr 1 with u
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs,sub_sq_comm]
  simp_rw [hD] at he
  exact he

private theorem gamma_excess_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Integrable (gammaExcessDensity n σ) := by
  have hp : ∀ᵐ h : ℝ ∂volume.restrict (Ioi 0),
      0 ≤ archLevyDensity h*factorialTailTranslationEnergy n σ h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact mul_nonneg (archLevyDensity_pos hh).le (factorialTailTranslationEnergy_nonneg n σ h)
  have hfinite := (hasFiniteIntegral_iff_ofReal hp).mp (factorialTailLevy_integrable n σ).2
  exact ⟨(gamma_excess_continuous n σ).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (gamma_excess_nonneg n σ))).mpr
      ((gamma_excess_lintegral n σ).trans_lt hfinite)⟩

private theorem gamma_excess_integral (n : ℕ) (σ : FactorialSamplingAbscissa) :
    (∫ ξ : ℝ, gammaExcessDensity n σ ξ) = factorialTailLevyEnergy n σ := by
  have hp : ∀ᵐ h : ℝ ∂volume.restrict (Ioi 0),
      0 ≤ archLevyDensity h*factorialTailTranslationEnergy n σ h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact mul_nonneg (archLevyDensity_pos hh).le (factorialTailTranslationEnergy_nonneg n σ h)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (gamma_excess_nonneg n σ))
    (gamma_excess_continuous n σ).aestronglyMeasurable,
    gamma_excess_lintegral]
  exact (integral_eq_lintegral_of_nonneg_ae hp (factorialTailLevy_integrable n σ).1).symm

private theorem gamma_density_eq (n : ℕ) (σ ξ : ℝ) :
    ccmArchimedeanFormWeight ξ*‖factorialTailFourier n σ ξ‖^2 =
      ‖factorialTailFourier n σ ξ‖^2+gammaExcessDensity n σ ξ := by
  have heven : gammaHardyPhaseRate (2*Real.pi*|ξ|) =
      gammaHardyPhaseRate (2*Real.pi*ξ) := by
    by_cases hξ : 0 ≤ ξ
    · rw [abs_of_nonneg hξ]
    · rw [abs_of_neg (lt_of_not_ge hξ),show 2*Real.pi*(-ξ) = -(2*Real.pi*ξ) by ring,
        gammaHardyPhaseRate_neg]
  unfold ccmArchimedeanFormWeight gammaExcessDensity
  rw [heven]
  ring

/-- Finiteness of the positive Gamma form is derived from the source, not assumed. -/
theorem factorialTailGamma_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Integrable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ*‖factorialTailFourier n σ ξ‖^2) :=
  ((fourier_sq_integrable n σ).add (gamma_excess_integrable n σ)).congr
    (Eventually.of_forall fun ξ => (gamma_density_eq n σ ξ).symm)

/-- Exact identification of the complete positive Gamma energy with physical costs. -/
theorem factorialTailGamma_integral_eq (n : ℕ) (σ : FactorialSamplingAbscissa) :
    (∫ ξ : ℝ, ccmArchimedeanFormWeight ξ*‖factorialTailFourier n σ ξ‖^2) =
      (∫ x : ℝ, factorialWeightedTail n σ x^2)+factorialTailLevyEnergy n σ := by
  simp_rw [gamma_density_eq]
  rw [integral_add (fourier_sq_integrable n σ) (gamma_excess_integrable n σ),
    fourier_sq_integral,gamma_excess_integral]

theorem factorialTailGamma_integral_le (n : ℕ) (σ : FactorialSamplingAbscissa) :
    (∫ ξ : ℝ, ccmArchimedeanFormWeight ξ*‖factorialTailFourier n σ ξ‖^2) ≤
      (96+factorialTailLevyConstant)*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ) := by
  have hlog : 0 ≤ Real.log ((n+1 : ℕ) : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ n+1 by omega))
  have hm : 96/((n+1 : ℕ) : ℝ) ≤
      96*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  rw [factorialTailGamma_integral_eq]
  calc
    _ ≤ 96*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ)+
        factorialTailLevyConstant*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ) :=
      add_le_add ((factorialWeightedTail_sq_integral_le n σ).trans hm)
        (factorialTailLevyEnergy_le n σ)
    _ = _ := by ring

/-- A source-independent constant for the logarithmic Fourier budget. -/
def factorialTailLogFourierConstant : ℝ :=
  ccmArchimedeanLogComparisonConstant*(96+factorialTailLevyConstant)

theorem factorialTailLogFourierConstant_pos : 0 < factorialTailLogFourierConstant :=
  mul_pos (lt_of_lt_of_le zero_lt_one one_le_ccmArchimedeanLogComparisonConstant)
    (by have := factorialTailLevyConstant_pos; linarith)

theorem factorialTailLogFourier_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ*‖factorialTailFourier n σ ξ‖^2) := by
  apply ((factorialTailGamma_integrable n σ).const_mul
    ccmArchimedeanLogComparisonConstant).mono'
    ((measurable_suzukiLogWeight.mul
      ((fourier_continuous n σ).norm.measurable.pow_const 2)).aestronglyMeasurable)
  filter_upwards [] with ξ
  change ‖suzukiLogWeight ξ*‖factorialTailFourier n σ ξ‖^2‖ ≤
    ccmArchimedeanLogComparisonConstant*
      (ccmArchimedeanFormWeight ξ*‖factorialTailFourier n σ ξ‖^2)
  rw [Real.norm_eq_abs,abs_of_nonneg
    (mul_nonneg (suzukiLogWeight_nonneg ξ) (sq_nonneg _))]
  calc
    _ ≤ (ccmArchimedeanLogComparisonConstant*ccmArchimedeanFormWeight ξ)*
        ‖factorialTailFourier n σ ξ‖^2 :=
      mul_le_mul_of_nonneg_right (suzukiLogWeight_le_ccmArchimedeanComparison ξ) (sq_nonneg _)
    _ = _ := by ring

/-- Uniform logarithmic Fourier control over the entire enlarged Mellin strip. -/
theorem factorialTailLogFourier_integral_le (n : ℕ) (σ : FactorialSamplingAbscissa) :
    (∫ ξ : ℝ, suzukiLogWeight ξ*‖factorialTailFourier n σ ξ‖^2) ≤
      factorialTailLogFourierConstant*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ) := by
  calc
    _ ≤ ∫ ξ : ℝ, ccmArchimedeanLogComparisonConstant*
        (ccmArchimedeanFormWeight ξ*‖factorialTailFourier n σ ξ‖^2) := by
      apply integral_mono (factorialTailLogFourier_integrable n σ)
        ((factorialTailGamma_integrable n σ).const_mul _)
      intro ξ
      calc
        _ ≤ (ccmArchimedeanLogComparisonConstant*ccmArchimedeanFormWeight ξ)*
            ‖factorialTailFourier n σ ξ‖^2 :=
          mul_le_mul_of_nonneg_right (suzukiLogWeight_le_ccmArchimedeanComparison ξ) (sq_nonneg _)
        _ = _ := by ring
    _ = ccmArchimedeanLogComparisonConstant*
        (∫ ξ : ℝ, ccmArchimedeanFormWeight ξ*‖factorialTailFourier n σ ξ‖^2) := integral_const_mul _ _
    _ ≤ ccmArchimedeanLogComparisonConstant*
        ((96+factorialTailLevyConstant)*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (factorialTailGamma_integral_le n σ)
        (zero_le_one.trans one_le_ccmArchimedeanLogComparisonConstant)
    _ = _ := by unfold factorialTailLogFourierConstant; ring

end
end GaloisForLFunctions.ArithmeticPositivityTheory
