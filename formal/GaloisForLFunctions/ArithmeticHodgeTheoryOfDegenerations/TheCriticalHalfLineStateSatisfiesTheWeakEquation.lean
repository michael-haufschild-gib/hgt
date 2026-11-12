import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowThresholdControlsTheFullHalfLineForm

/-!
# The actual critical half-line state's weak equation

Full-energy domain closure permits genuine variations of the measurable
state. Endpoint nonnegativity and zero energy then annihilate its mixed
form against every finite-energy half-line test.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis WindowTowerOfSpecZ

private theorem integrable_weighted_cross {F G w : ℝ → ℝ}
    (hFm : Measurable F) (hGm : Measurable G) (hwm : Measurable w) (hw : ∀ u, 0 ≤ w u)
    (hF : Integrable (fun u => F u ^ 2 * w u))
    (hG : Integrable (fun u => G u ^ 2 * w u)) :
    Integrable (fun u => F u * G u * w u) := by
  apply ((hF.add hG).div_const 2).mono'
    ((hFm.mul hGm).mul hwm).aestronglyMeasurable
  refine Eventually.of_forall fun u => ?_
  change ‖F u * G u * w u‖ ≤ (F u ^ 2 * w u + G u ^ 2 * w u) / 2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw u)]
  have hcross : |F u * G u| ≤ (F u ^ 2 + G u ^ 2) / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [sq_nonneg (F u + G u), sq_nonneg (F u - G u)]
  calc
    _ ≤ ((F u ^ 2 + G u ^ 2) / 2) * w u :=
      mul_le_mul_of_nonneg_right hcross (hw u)
    _ = _ := by ring

private theorem integrable_weighted_square_variation {F G w : ℝ → ℝ}
    (hFm : Measurable F) (hGm : Measurable G) (hwm : Measurable w) (hw : ∀ u, 0 ≤ w u)
    (hF : Integrable (fun u => F u ^ 2 * w u))
    (hG : Integrable (fun u => G u ^ 2 * w u)) (c : ℝ) :
    Integrable (fun u => (F u + c * G u) ^ 2 * w u) := by
  have hm := integrable_weighted_cross hFm hGm hwm hw hF hG
  apply ((hF.add (hm.const_mul (2 * c))).add (hG.const_mul (c ^ 2))).congr
  exact Eventually.of_forall fun u => by dsimp only [Pi.add_apply]; ring

/-- Every real variation stays in the actual half-line energy domain. -/
theorem CriticalHalfLineEnergyDomain.add_const_mul {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (c : ℝ) :
    CriticalHalfLineEnergyDomain (fun u => F u + c * G u) := by
  refine ⟨hF.meas.add (measurable_const.mul hG.meas), hF.integrable.add (hG.integrable.const_mul c),
    ?_, ?_, ?_, integrable_gamma_add_const_mul hF.integrable hG.integrable hF.gamma hG.gamma c⟩
  · have hf : Integrable (fun u => F u ^ 2 * (1 : ℝ)) := by simpa only [mul_one] using hF.sq
    have hg : Integrable (fun u => G u ^ 2 * (1 : ℝ)) := by simpa only [mul_one] using hG.sq
    simpa only [mul_one] using integrable_weighted_square_variation
      hF.meas hG.meas measurable_const (fun _ => zero_le_one) hf hg c
  · exact integrable_weighted_square_variation hF.meas hG.meas (by fun_prop)
      (fun u => (Real.exp_pos _).le) hF.exponential hG.exponential c
  · intro u hu
    rw [hF.support u hu, hG.support u hu, mul_zero, add_zero]

/-- The mixed form retains all four pieces of the full critical energy. -/
def criticalHalfLineMixedEnergy (R : ℝ) (F G : ℝ → ℝ) : ℝ :=
  gammaMixedForm F G - (primeMixedForm F G + primeMixedForm G F) / 2 +
    (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G) +
    criticalAliasCoefficient R * (∫ u in Iio 0, F u * G u * Real.exp (-(8 * u)))

private theorem coshHalfMoment_add_const_mul {F G : ℝ → ℝ}
    (hF : WeightedTwo F) (hG : WeightedTwo G) (c : ℝ) :
    coshHalfMoment (fun u => F u + c * G u) = coshHalfMoment F + c * coshHalfMoment G := by
  have hc : Continuous fun u : ℝ => Real.cosh (u / 2) :=
    Real.continuous_cosh.comp (continuous_id.div_const 2)
  have hiF := (abs_integral_mul_kernel_le hF hc abs_cosh_half_le_exp).1
  have hiG := (abs_integral_mul_kernel_le hG hc abs_cosh_half_le_exp).1
  unfold coshHalfMoment
  simp_rw [add_mul, mul_assoc]
  rw [integral_add hiF (hiG.const_mul c), integral_const_mul]

private theorem sinhHalfMoment_add_const_mul {F G : ℝ → ℝ}
    (hF : WeightedTwo F) (hG : WeightedTwo G) (c : ℝ) :
    sinhHalfMoment (fun u => F u + c * G u) = sinhHalfMoment F + c * sinhHalfMoment G := by
  have hc : Continuous fun u : ℝ => Real.sinh (u / 2) :=
    Real.continuous_sinh.comp (continuous_id.div_const 2)
  have hiF := (abs_integral_mul_kernel_le hF hc abs_sinh_half_le_exp).1
  have hiG := (abs_integral_mul_kernel_le hG hc abs_sinh_half_le_exp).1
  unfold sinhHalfMoment
  simp_rw [add_mul, mul_assoc]
  rw [integral_add hiF (hiG.const_mul c), integral_const_mul]

private theorem exponential_mass_variation {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (c : ℝ) :
    (∫ u in Iio 0, (F u + c * G u) ^ 2 * Real.exp (-(8 * u))) =
      (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))) +
      (2 * c) * (∫ u in Iio 0, F u * G u * Real.exp (-(8 * u))) +
      c ^ 2 * (∫ u in Iio 0, G u ^ 2 * Real.exp (-(8 * u))) := by
  have hm := integrable_weighted_cross hF.meas hG.meas (by fun_prop)
    (fun u => (Real.exp_pos _).le) hF.exponential hG.exponential
  have he (u : ℝ) : (F u + c * G u) ^ 2 * Real.exp (-(8 * u)) =
      F u ^ 2 * Real.exp (-(8 * u)) + (2 * c) * (F u * G u * Real.exp (-(8 * u))) +
      c ^ 2 * (G u ^ 2 * Real.exp (-(8 * u))) := by ring
  have hsum : IntegrableOn (fun u => F u ^ 2 * Real.exp (-(8 * u)) +
      (2 * c) * (F u * G u * Real.exp (-(8 * u)))) (Iio 0) :=
    hF.exponential.integrableOn.add (hm.integrableOn.const_mul (2 * c))
  simp_rw [he]
  rw [integral_add hsum
      (hG.exponential.integrableOn.const_mul (c ^ 2)),
    integral_add hF.exponential.integrableOn (hm.integrableOn.const_mul (2 * c)),
    integral_const_mul, integral_const_mul]

/-- The full critical energy is quadratic along each admissible variation. -/
theorem criticalHalfLineFullEnergy_add_const_mul (R : ℝ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (c : ℝ) :
    criticalHalfLineFullEnergy R (fun u => F u + c * G u) =
      criticalHalfLineFullEnergy R F + 2 * c * criticalHalfLineMixedEnergy R F G +
      c ^ 2 * criticalHalfLineFullEnergy R G := by
  unfold criticalHalfLineFullEnergy criticalHalfLineMixedEnergy
  rw [archForm_add_const_mul_of_integrable hF.integrable hG.integrable hF.gamma hG.gamma,
    primeSum_add_const_mul hF.weighted hG.weighted,
    coshHalfMoment_add_const_mul hF.weighted hG.weighted,
    sinhHalfMoment_add_const_mul hF.weighted hG.weighted,
    exponential_mass_variation hF hG]
  ring

private theorem mixed_eq_zero_of_nonnegative_variations {A B : ℝ} (hA : 0 ≤ A)
    (h : ∀ c : ℝ, 0 ≤ 2 * c * B + c ^ 2 * A) : B = 0 := by
  have hden : A + 1 ≠ 0 := by linarith only [hA]
  have he : (2 * (-B / (A + 1)) * B + (-B / (A + 1)) ^ 2 * A) * (A + 1) ^ 2 =
      -(A + 2) * B ^ 2 := by
    field_simp
    ring
  have hp := mul_nonneg (h (-B / (A + 1))) (sq_nonneg (A + 1))
  rw [he] at hp
  nlinarith only [hp, mul_nonneg hA (sq_nonneg B), sq_nonneg B]

/-- At the global window threshold the actual critical state solves the full
weak equation against every finite-energy half-line test. -/
theorem criticalHalfLineMixedEnergy_groundState_eq_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineMixedEnergy W₀ F G = 0 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hzero := criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hF
  apply mixed_eq_zero_of_nonnegative_variations
    (criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW hthreshold hG)
  intro c
  have hp := criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW hthreshold (hd.add_const_mul hG c)
  rwa [criticalHalfLineFullEnergy_add_const_mul W₀ hd hG, hzero, zero_add] at hp

/-- The unconditional threshold classification supplies a genuine weak
zero mode in its remaining case. -/
theorem criticalHalfLine_weakEquation_classification :
    RiemannHypothesis ∨
      polarPaymentCriticalThreshold < (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        polarPaymentCriticalThreshold = (W₀ : EReal) ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧ CriticalHalfLineEnergyDomain F ∧
        criticalHalfLineFullEnergy W₀ F = 0 ∧
        (∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → criticalHalfLineMixedEnergy W₀ F G = 0) ∧
        (∫ u, F u * polarSourceProfile u) = 0 := by
  rcases criticalHalfLine_fullEnergy_classification with hRH | hlt | ⟨W₀, F, hW, hp, ht, hF, hzero, horth⟩
  · exact Or.inl hRH
  · exact Or.inr (Or.inl hlt)
  · exact Or.inr (Or.inr ⟨W₀, F, hW, hp, ht, hF, criticalHalfLineEnergyDomain_of_groundState hF,
      hzero, fun G hG => criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF hG, horth⟩)

/-- Failure of RH supplies an actual weak zero mode at the global window
threshold, independently of the polar threshold. -/
theorem riemannHypothesis_or_exists_weak_criticalHalfLineGroundState :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ CriticalHalfLineEnergyDomain F ∧
      criticalHalfLineFullEnergy W₀ F = 0 ∧
      ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → criticalHalfLineMixedEnergy W₀ F G = 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, criticalHalfLineEnergyDomain_of_groundState hF,
      criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF,
      fun G hG => criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF hG⟩

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
