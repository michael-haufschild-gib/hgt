import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ThePairedReflectionPreservesTheActualDomain
import GaloisForLFunctions.RHTower.EvenSectorLevyKreinRigidity
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional

/-!
# The Lévy representation on the actual half-line domain

Full Gamma integrability transfers to the Fourier symbol after rescaling.
The general Lévy–Plancherel identity then gives a finite physical jump
energy, without smoothness or compact support of the profile.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23 FourierTransform
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
open BiScaleUncertainty ArchimedeanAnomaly

theorem CriticalHalfLineEnergyDomain.memLp_real {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : MemLp F 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hF.meas.aestronglyMeasurable).mpr
  simpa only [Real.norm_eq_abs, sq_abs] using hF.sq

theorem CriticalHalfLineEnergyDomain.integrable_gammaHardyFourier {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Integrable (fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 (cx F) ξ‖ ^ 2) := by
  have h := (hF.gamma.comp_mul_left' (R := -(2 * Real.pi))
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero))).div_const 2
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [fourier_eq_paperFT_neg_two_pi_mul, WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
    show -(2 * Real.pi) * ξ = -(2 * Real.pi * ξ) by ring, gammaHardyPhaseRate_neg]
  ring

theorem CriticalHalfLineEnergyDomain.aestronglyMeasurable_levyIntegrand {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    AEStronglyMeasurable (fun x : ℝ => archLevyDensity x * ∫ u, (F u - F (u + x)) ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => (F p.2 - F (p.2 + p.1)) ^ 2) := by
    have hm := hF.meas
    fun_prop
  have hm : StronglyMeasurable (fun x : ℝ => ∫ u, (F u - F (u + x)) ^ 2) :=
    hmeas.stronglyMeasurable.integral_prod_right'
  exact measurable_archLevyDensity.aestronglyMeasurable.mul hm.aestronglyMeasurable

/-- The full Gamma domain has finite physical Lévy energy. -/
theorem CriticalHalfLineEnergyDomain.integrableOn_levyIntegrand {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    IntegrableOn (fun x : ℝ => archLevyDensity x * ∫ u, (F u - F (u + x)) ^ 2) (Ioi 0) := by
  have hG1 : Integrable (fun u => (F u : ℂ)) := hF.integrable.ofReal (𝕜 := ℂ)
  have hG2 : MemLp (fun u => (F u : ℂ)) 2 volume := hF.memLp_complex
  have hGγ : Integrable (fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) *
      ‖𝓕 (fun u => (F u : ℂ)) ξ‖ ^ 2) := hF.integrable_gammaHardyFourier
  have hne := lintegral_archLevyDirichlet_ne_top hG1 hG2 hGγ
  rw [lintegral_levy_eq F] at hne
  refine ⟨hF.aestronglyMeasurable_levyIntegrand, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (levyIntegrand_nonneg F)]
  exact lt_top_iff_ne_top.mpr hne

/-- The literal Gamma form equals its mass offset plus finite Lévy jump energy. -/
theorem CriticalHalfLineEnergyDomain.archForm_eq_levyEnergy {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    archForm F = 2 * gammaHardyPhaseRate 0 * (∫ u, F u ^ 2) + levyEnergy F := by
  have hG1 : Integrable (fun u => (F u : ℂ)) := hF.integrable.ofReal (𝕜 := ℂ)
  have hG2 : MemLp (fun u => (F u : ℂ)) 2 volume := hF.memLp_complex
  have hGγ : Integrable (fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) *
      ‖𝓕 (fun u => (F u : ℂ)) ξ‖ ^ 2) := hF.integrable_gammaHardyFourier
  have hsplit := integral_archSymbol_mul_normSq_fourier_eq hG1 hG2 hGγ
  have hnorm : (∫ u : ℝ, ‖(F u : ℂ)‖ ^ 2) = ∫ u, F u ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold archForm levyEnergy
  rw [WeilLevyPole.integral_paperFT_sq_mul_gammaBracket, hsplit,
    lintegral_levy_eq F, hnorm,
    ← integral_eq_lintegral_of_nonneg_ae (levyIntegrand_nonneg F)
      hF.aestronglyMeasurable_levyIntegrand]

/-- Square expansion identifies the jump and correlation integrands on the full domain. -/
theorem CriticalHalfLineEnergyDomain.levyIntegrand_eq {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {x : ℝ} (hx : 0 < x) :
    archLevyDensity x * (∫ u, (F u - F (u + x)) ^ 2) =
      (autocorr F 0 - autocorr F x) * archLevySinhWeight x := by
  rw [AutocorrelationKrein.integral_sub_shift_sq hF.memLp_real x,
    archLevySinhWeight, exp_half_div_sinh_eq hx]
  ring

theorem CriticalHalfLineEnergyDomain.integrableOn_biScaleLevyIntegrand {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    IntegrableOn (fun x => (autocorr F 0 - autocorr F x) * archLevySinhWeight x) (Ioi 0) := by
  apply hF.integrableOn_levyIntegrand.congr
  exact (ae_restrict_mem measurableSet_Ioi).mono fun x hx => hF.levyIntegrand_eq hx

theorem CriticalHalfLineEnergyDomain.levyEnergy_eq_biScaleLevyEnergy {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : levyEnergy F = biScaleLevyEnergy F := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact hF.levyIntegrand_eq hx

/-- The actual Gamma energy is its mass offset plus the correlation-deficit energy. -/
theorem CriticalHalfLineEnergyDomain.archForm_eq_biScaleLevyEnergy {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    archForm F = 2 * gammaHardyPhaseRate 0 * (∫ u, F u ^ 2) + biScaleLevyEnergy F := by
  rw [hF.archForm_eq_levyEnergy, hF.levyEnergy_eq_biScaleLevyEnergy]

theorem CriticalHalfLineEnergyDomain.biScaleLevyIntegrand_nonneg {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {x : ℝ} (hx : 0 < x) :
    0 ≤ (autocorr F 0 - autocorr F x) * archLevySinhWeight x :=
  mul_nonneg (AutocorrelationKrein.deficit_nonneg hF.memLp_real x)
    (archLevySinhWeight_pos hx).le

theorem CriticalHalfLineEnergyDomain.biScaleLevyEnergy_nonneg {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : 0 ≤ biScaleLevyEnergy F :=
  setIntegral_nonneg measurableSet_Ioi fun _ hx => hF.biScaleLevyIntegrand_nonneg hx

#print axioms CriticalHalfLineEnergyDomain.archForm_eq_biScaleLevyEnergy
#print axioms CriticalHalfLineEnergyDomain.integrableOn_biScaleLevyIntegrand
#print axioms CriticalHalfLineEnergyDomain.biScaleLevyEnergy_nonneg

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
