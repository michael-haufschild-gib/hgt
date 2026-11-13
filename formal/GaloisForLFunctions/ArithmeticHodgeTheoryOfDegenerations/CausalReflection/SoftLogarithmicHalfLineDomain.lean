import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningGammaSymbol
import GaloisForLFunctions.HTGeometry.HardyBoundary.LogarithmicFourierDilation

/-!
# A dilation-stable half-line logarithmic domain

The union of positive exponential square-moment domains is preserved by
dilation. Gamma-symbol comparison includes every actual energy profile,
and sufficiently compressed logarithmic profiles recover the actual domain.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
open HTGeometry

/-- The negative half-line logarithmic domain with some positive exponential square moment. -/
structure SoftLogarithmicHalfLineDomain (F : ℝ → ℝ) : Prop where
  meas : Measurable F
  integrable : Integrable F
  sq : Integrable (fun u => F u ^ 2)
  support : ∀ u, 0 ≤ u → F u = 0
  exponential : ∃ β : ℝ, 0 < β ∧ Integrable (fun u => F u ^ 2 * Real.exp (-(β * u)))
  logarithmic : Integrable (fun ξ => |Real.log (|ξ|)| * ‖𝓕 (cx F) ξ‖ ^ 2)

theorem SoftLogarithmicHalfLineDomain.memLp_complex {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) : MemLp (cx F) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (hF.integrable.ofReal (𝕜 := ℂ)).aestronglyMeasurable).mpr
  apply hF.sq.congr
  exact Eventually.of_forall fun u => by
    change F u ^ 2 = ‖(F u : ℂ)‖ ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Actual Gamma integrability supplies absolute logarithmic energy. -/
theorem CriticalHalfLineEnergyDomain.softLogarithmic {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : SoftLogarithmicHalfLineDomain F := by
  obtain ⟨C, _, _, hbound⟩ := exists_confiningGammaSymbol_log_bound
  exact ⟨hF.meas, hF.integrable, hF.sq, hF.support,
    ⟨8, by norm_num, hF.exponential⟩,
    integrable_log_fourier_sq_of_symbol (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ))
      hF.memLp_complex hbound hF.integrable_confiningGammaSymbol⟩

/-- Any lower exponential rate is controlled by a known exponential square moment. -/
theorem SoftLogarithmicHalfLineDomain.integrable_exponential_of_le {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) {β γ : ℝ}
    (hβ : Integrable (fun u => F u ^ 2 * Real.exp (-(β * u)))) (hγ : γ ≤ β) :
    Integrable (fun u => F u ^ 2 * Real.exp (-(γ * u))) := by
  have hmeas : Measurable (fun u => F u ^ 2 * Real.exp (-(γ * u))) := by
    have hm := hF.meas
    fun_prop
  apply hβ.mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    by_cases hu : 0 ≤ u
    · simp only [hF.support u hu, zero_pow two_ne_zero, zero_mul, le_refl]
    · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
      have hh := mul_le_mul_of_nonneg_right hγ (neg_nonneg.mpr (lt_of_not_ge hu).le)
      simpa only [mul_neg, neg_mul] using hh

/-- An exponential moment controls the physical first moment. -/
theorem SoftLogarithmicHalfLineDomain.integrable_firstMoment {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) : Integrable (fun u => (-u) * F u ^ 2) := by
  obtain ⟨β, hβ, hi⟩ := hF.exponential
  have hmeas : Measurable (fun u => (-u) * F u ^ 2) := by
    have hm := hF.meas
    fun_prop
  apply (hi.div_const β).mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    by_cases hu : 0 ≤ u
    · simp only [hF.support u hu, zero_pow two_ne_zero, mul_zero, zero_mul, zero_div, norm_zero,
        le_refl]
    · have ht : 0 ≤ -u := neg_nonneg.mpr (lt_of_not_ge hu).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht (sq_nonneg _))]
      have he := Real.add_one_le_exp (-(β * u))
      have hb : -u ≤ Real.exp (-(β * u)) / β := by
        apply (le_div_iff₀ hβ).mpr
        nlinarith only [he]
      simpa only [div_mul_eq_mul_div, mul_comm (F u ^ 2)] using
        mul_le_mul_of_nonneg_right hb (sq_nonneg (F u))

/-- Fourier logarithmic control and the eighth exponential moment recover the actual domain. -/
theorem SoftLogarithmicHalfLineDomain.toActual {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F)
    (h8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    CriticalHalfLineEnergyDomain F := by
  obtain ⟨C, _, hbound, _⟩ := exists_confiningGammaSymbol_log_bound
  refine ⟨hF.meas, hF.integrable, hF.sq, h8, hF.support, ?_⟩
  apply integrable_gammaBracket_of_confiningGammaSymbol
  exact integrable_symbol_fourier_sq_of_log (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ))
    hF.memLp_complex continuous_confiningGammaSymbol hbound hF.logarithmic

theorem SoftLogarithmicHalfLineDomain.absMoment_integrand_eq {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) (u : ℝ) :
    |u| * ‖cx F u‖ ^ 2 = (-u) * F u ^ 2 := by
  simp only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  by_cases hu : 0 ≤ u
  · simp only [hF.support u hu, zero_pow two_ne_zero, mul_zero]
  · rw [abs_of_neg (lt_of_not_ge hu)]

theorem SoftLogarithmicHalfLineDomain.integrable_absMoment {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) : Integrable (fun u => |u| * ‖cx F u‖ ^ 2) := by
  apply hF.integrable_firstMoment.congr
  exact Eventually.of_forall fun u => (hF.absMoment_integrand_eq u).symm

theorem SoftLogarithmicHalfLineDomain.integral_absMoment {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) :
    (∫ u, |u| * ‖cx F u‖ ^ 2) = ∫ u, (-u) * F u ^ 2 := by
  apply integral_congr_ae
  exact Eventually.of_forall hF.absMoment_integrand_eq

theorem integrable_exponential_unitaryRealDilation {F : ℝ → ℝ} {a β : ℝ}
    (ha : 0 < a) (hi : Integrable (fun u => F u ^ 2 * Real.exp (-(β * u)))) :
    Integrable (fun u => unitaryRealDilation a F u ^ 2 * Real.exp (-((a * β) * u))) := by
  have hright : Integrable (fun u => Real.exp (-((a * β) * (u / a))) * F u ^ 2) := by
    apply hi.congr
    exact Eventually.of_forall fun u => by
      change F u ^ 2 * Real.exp (-(β * u)) = Real.exp (-((a * β) * (u / a))) * F u ^ 2
      have he : (a * β) * (u / a) = β * u := by field_simp [ha.ne']
      rw [he, mul_comm]
  have hd := integrable_weighted_sq_unitaryRealDilation ha F
    (fun u => Real.exp (-((a * β) * u))) hright
  simpa only [mul_comm] using hd

/-- The union over positive exponential rates is invariant under every positive dilation. -/
theorem SoftLogarithmicHalfLineDomain.unitaryDilation {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) {a : ℝ} (ha : 0 < a) :
    SoftLogarithmicHalfLineDomain (unitaryRealDilation a F) := by
  obtain ⟨β, hβ, hi⟩ := hF.exponential
  refine ⟨measurable_const.mul (hF.meas.comp (measurable_const.mul measurable_id)),
    integrable_unitaryRealDilation ha hF.integrable,
    integrable_sq_unitaryRealDilation ha hF.sq, ?_,
    ⟨a * β, mul_pos ha hβ, integrable_exponential_unitaryRealDilation ha hi⟩, ?_⟩
  · intro u hu
    dsimp only [unitaryRealDilation]
    rw [hF.support (a * u) (mul_nonneg ha.le hu), mul_zero]
  · exact integrable_abs_log_fourier_sq_unitaryRealDilation ha hF.integrable
      hF.memLp_complex hF.logarithmic

/-- Every logarithmic-domain trial enters the actual Gamma domain after sufficient compression. -/
theorem SoftLogarithmicHalfLineDomain.eventually_actual_dilation {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) :
    ∀ᶠ a : ℝ in atTop, CriticalHalfLineEnergyDomain (unitaryRealDilation a F) := by
  obtain ⟨β, hβ, hi⟩ := hF.exponential
  filter_upwards [eventually_ge_atTop (max 1 (8 / β))] with a ha
  have ha0 : 0 < a := zero_lt_one.trans_le ((le_max_left _ _).trans ha)
  have h8 : 8 ≤ a * β := (div_le_iff₀ hβ).mp ((le_max_right _ _).trans ha)
  have hd := hF.unitaryDilation ha0
  exact hd.toActual (hd.integrable_exponential_of_le
    (integrable_exponential_unitaryRealDilation ha0 hi) h8)

#print axioms CriticalHalfLineEnergyDomain.softLogarithmic
#print axioms SoftLogarithmicHalfLineDomain.unitaryDilation
#print axioms SoftLogarithmicHalfLineDomain.eventually_actual_dilation
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
