import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningGammaSymbol

/-!
# Contractions in the actual half-line Gamma domain

Finite physical jump energy recovers full Gamma integrability by the
extended Lévy–Plancherel identity. A real contraction fixing zero therefore
preserves the actual half-line domain, including its exponential weight.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open ArithmeticCastelnuovoSeveri

private theorem lintegral_cx_jump_eq_real (F : ℝ → ℝ) :
    (∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
      (archLevyDensity h * ∫ u, ‖cx F u - cx F (u + h)‖ ^ 2)) =
      ∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
        (archLevyDensity h * ∫ u, (F u - F (u + h)) ^ 2) := lintegral_levy_eq F

/-- Gamma integrability gives finite jump energy without a support or exponential-mass premise. -/
theorem integrableOn_levyIntegrand_of_gammaBracket {F : ℝ → ℝ}
    (hFm : Measurable F) (hF1 : Integrable F) (hF2 : MemLp F 2 volume)
    (hγ : Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r)) :
    IntegrableOn
      (fun h : ℝ => archLevyDensity h * ∫ u, (F u - F (u + h)) ^ 2) (Ioi 0) := by
  have hc1 : Integrable (cx F) := hF1.ofReal (𝕜 := ℂ)
  have hc2 : MemLp (cx F) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable).mpr
    have hi := (memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).mp hF2
    simpa only [cx, Complex.norm_real] using hi
  have hs : Integrable (fun ξ : ℝ =>
      gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 (cx F) ξ‖ ^ 2) := by
    have hh := (hγ.comp_mul_left' (R := -(2 * Real.pi))
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero))).div_const 2
    refine hh.congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_eq_paperFT_neg_two_pi_mul, WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
      show -(2 * Real.pi) * ξ = -(2 * Real.pi * ξ) by ring, gammaHardyPhaseRate_neg]
    ring
  have hfinite := lintegral_archLevyDirichlet_ne_top hc1 hc2 hs
  rw [lintegral_cx_jump_eq_real F] at hfinite
  have hjm : Measurable (fun p : ℝ × ℝ => (F p.2 - F (p.2 + p.1)) ^ 2) := by
    fun_prop
  refine ⟨measurable_archLevyDensity.aestronglyMeasurable.mul
    hjm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (levyIntegrand_nonneg F)]
  exact lt_top_iff_ne_top.mpr hfinite

/-- Finite jump energy recovers the literal Gamma domain for an `L¹ ∩ L²` profile. -/
theorem integrable_gammaBracket_of_levyIntegrand {F : ℝ → ℝ}
    (hF1 : Integrable F) (hF2 : MemLp F 2 volume)
    (hJ : IntegrableOn
      (fun h : ℝ => archLevyDensity h * ∫ u, (F u - F (u + h)) ^ 2) (Ioi 0)) :
    Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r) := by
  have hc1 : Integrable (cx F) := hF1.ofReal (𝕜 := ℂ)
  have hc2 : MemLp (cx F) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable).mpr
    have hi := (memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).mp hF2
    simpa only [cx, Complex.norm_real] using hi
  have hft := RHTower.integrable_norm_sq_fourier (f := cx F) hc1 hc2
  have hnn : ∀ ξ : ℝ, 0 ≤
      2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) *
        ‖𝓕 (cx F) ξ‖ ^ 2 := fun ξ =>
    mul_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.mpr (gammaHardyPhaseRate_zero_le_levy _))) (sq_nonneg _)
  have hsymbol : Integrable (fun ξ : ℝ =>
      2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) *
        ‖𝓕 (cx F) ξ‖ ^ 2) := by
    refine ⟨?_, ?_⟩
    · have hs : Continuous (fun ξ : ℝ =>
          2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0)) :=
        ((continuous_gammaHardyPhaseRate.comp
          (continuous_const.mul continuous_id)).sub continuous_const).const_mul 2
      exact hs.aestronglyMeasurable.mul hft.aestronglyMeasurable
    · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)]
      have he := lintegral_archSymbol_mul_normSq_fourier hc1 hc2
      change (∫⁻ ξ, ENNReal.ofReal
        (2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) *
          ‖𝓕 (cx F) ξ‖ ^ 2)) < ⊤
      rw [he, lintegral_cx_jump_eq_real F]
      exact (hasFiniteIntegral_iff_ofReal (levyIntegrand_nonneg F)).mp hJ.2
  apply integrable_gammaBracket_of_confiningGammaSymbol
  apply (hsymbol.add (hft.const_mul (2 * gammaHardyPhaseRate 0))).congr
  exact Eventually.of_forall fun ξ => by
    simp only [Pi.add_apply, confiningGammaSymbol]
    ring

/-- Contractions preserve finite jump energy without any confining-weight hypothesis. -/
theorem integrableOn_levyIntegrand_comp_contraction {F T : ℝ → ℝ}
    (hFm : Measurable F) (hF2 : MemLp F 2 volume)
    (hFJ : IntegrableOn
      (fun h : ℝ => archLevyDensity h * ∫ u, (F u - F (u + h)) ^ 2) (Ioi 0))
    (hT : LipschitzWith 1 T) (hT0 : T 0 = 0) :
    IntegrableOn
      (fun h : ℝ => archLevyDensity h * ∫ u, (T (F u) - T (F (u + h))) ^ 2) (Ioi 0) := by
  have hm : Measurable (T ∘ F) := hT.continuous.measurable.comp hFm
  have hL2 : MemLp (T ∘ F) 2 volume := by
    apply hF2.mono hm.aestronglyMeasurable
    exact Eventually.of_forall fun u => by
      simpa only [Function.comp_apply, hT0, sub_zero, NNReal.coe_one, one_mul]
        using hT.norm_sub_le (F u) 0
  have hdiff (u v : ℝ) : |T (F u) - T (F v)| ≤ |F u - F v| := by
    simpa only [NNReal.coe_one, one_mul, Real.norm_eq_abs] using hT.norm_sub_le (F u) (F v)
  have hjm : Measurable (fun p : ℝ × ℝ => (T (F p.2) - T (F (p.2 + p.1))) ^ 2) := by
    have ht := hT.continuous.measurable
    fun_prop
  refine hFJ.mono'
    (measurable_archLevyDensity.aestronglyMeasurable.mul
      hjm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos hh).le
    (integral_nonneg fun u => sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (archLevyDensity_pos hh).le
  have hd2 := hL2.sub (hL2.comp_measurePreserving (measurePreserving_add_right volume h))
  have hf2 := hF2.sub (hF2.comp_measurePreserving (measurePreserving_add_right volume h))
  have hdi := (memLp_two_iff_integrable_sq_norm hd2.aestronglyMeasurable).mp hd2
  have hfi := (memLp_two_iff_integrable_sq_norm hf2.aestronglyMeasurable).mp hf2
  simp only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs, sq_abs] at hdi hfi
  apply integral_mono hdi hfi
  intro u
  have hd := hdiff u (u + h)
  have hp := mul_nonneg (sub_nonneg.mpr hd)
    (add_nonneg (abs_nonneg (F u - F (u + h)))
      (abs_nonneg (T (F u) - T (F (u + h)))))
  nlinarith only [hp, sq_abs (F u - F (u + h)), sq_abs (T (F u) - T (F (u + h)))]

/-- The full Gamma domain is closed under real contractions fixing zero. -/
theorem integrable_gammaBracket_comp_contraction {F T : ℝ → ℝ}
    (hFm : Measurable F) (hF1 : Integrable F) (hF2 : MemLp F 2 volume)
    (hγ : Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r))
    (hT : LipschitzWith 1 T) (hT0 : T 0 = 0) :
    Integrable (fun r : ℝ => ‖paperFT (cx (T ∘ F)) r‖ ^ 2 * EF.gammaBracket r) := by
  have hm : Measurable (T ∘ F) := hT.continuous.measurable.comp hFm
  have hb : ∀ᵐ u ∂volume, ‖(T ∘ F) u‖ ≤ ‖F u‖ :=
    Eventually.of_forall fun u => by
      simpa only [Function.comp_apply, hT0, sub_zero, NNReal.coe_one, one_mul]
        using hT.norm_sub_le (F u) 0
  have hi := hF1.norm.mono' hm.aestronglyMeasurable hb
  have hL2 := hF2.mono hm.aestronglyMeasurable hb
  exact integrable_gammaBracket_of_levyIntegrand (F := T ∘ F) hi hL2
    (integrableOn_levyIntegrand_comp_contraction (F := F) (T := T) hFm hF2
      (integrableOn_levyIntegrand_of_gammaBracket (F := F) hFm hF1 hF2 hγ) hT hT0)

/-- A zero-preserving contraction preserves every condition of the actual domain. -/
theorem CriticalHalfLineEnergyDomain.comp_contraction {F T : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hT : LipschitzWith 1 T) (hT0 : T 0 = 0) :
    CriticalHalfLineEnergyDomain (T ∘ F) := by
  have hm : Measurable (T ∘ F) := hT.continuous.measurable.comp hF.meas
  have hb (u : ℝ) : |T (F u)| ≤ |F u| := by
    simpa only [hT0, sub_zero, NNReal.coe_one, one_mul, Real.norm_eq_abs]
      using hT.norm_sub_le (F u) 0
  have hsq (u : ℝ) : T (F u) ^ 2 ≤ F u ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr (hb u))
      (add_nonneg (abs_nonneg (F u)) (abs_nonneg (T (F u))))
    nlinarith only [hh, sq_abs (F u), sq_abs (T (F u))]
  have hi : Integrable (T ∘ F) := hF.integrable.norm.mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun u => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hb u)
  have hi2 : Integrable (fun u => (T (F u)) ^ 2) :=
    hF.sq.mono' (hm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (T (F u)))] using hsq u)
  have hL2 : MemLp (T ∘ F) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    simpa only [Function.comp_apply, Real.norm_eq_abs, sq_abs] using hi2
  have hj := integrableOn_levyIntegrand_comp_contraction hF.meas hF.memLp_real
    hF.integrableOn_levyIntegrand hT hT0
  refine ⟨hm, hi, hi2, ?_, ?_, integrable_gammaBracket_of_levyIntegrand hi hL2 hj⟩
  · refine hF.exponential.mono' ((hm.pow_const 2).mul (by fun_prop)).aestronglyMeasurable ?_
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right (hsq u) (Real.exp_pos _).le
  · intro u hu
    simp only [Function.comp_apply, hF.support u hu, hT0]

#print axioms integrable_gammaBracket_of_levyIntegrand
#print axioms integrable_gammaBracket_comp_contraction
#print axioms CriticalHalfLineEnergyDomain.comp_contraction
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
