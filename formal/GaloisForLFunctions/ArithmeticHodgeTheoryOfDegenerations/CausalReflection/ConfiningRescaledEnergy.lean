import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningLogarithmicFloor

/-!
# Exact energy decomposition for rescaled minimizers

The exponential potential exceeds its linearization. A uniform bound on
scaled excess controls the rescaled first moment, making the spectral and
arithmetic remainders uniformly bounded below by quantities tending to zero.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- Undo the physical concentration at the actual confinement strength. -/
def rescaledConfiningProfile (a : ℝ) (F : ℝ → ℝ) : ℝ → ℝ :=
  unitaryRealDilation a⁻¹ F

theorem CriticalHalfLineEnergyDomain.rescaled_softLogarithmic {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {a : ℝ} (ha : 0 < a) :
    SoftLogarithmicHalfLineDomain (rescaledConfiningProfile a F) :=
  hF.softLogarithmic.unitaryDilation (inv_pos.mpr ha)

theorem integral_sq_rescaledConfiningProfile {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    (∫ u, rescaledConfiningProfile a F u ^ 2) = ∫ u, F u ^ 2 :=
  integral_sq_unitaryRealDilation (inv_pos.mpr ha) F

theorem firstMoment_rescaledConfiningProfile {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    criticalHalfLineFirstMoment (rescaledConfiningProfile a F) =
      a * criticalHalfLineFirstMoment F := by
  simpa only [criticalHalfLineFirstMoment, rescaledConfiningProfile,
    div_inv_eq_mul, mul_comm] using
    integral_firstMoment_unitaryRealDilation (inv_pos.mpr ha) F

/-- The rescaled potential has a nonnegative error beyond its linear part. -/
theorem CriticalHalfLineEnergyDomain.rescaled_potential_error_nonneg {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {a : ℝ} (ha : 0 < a) :
    0 ≤ a * criticalHalfLineExponentialDefect F -
      8 * criticalHalfLineFirstMoment (rescaledConfiningProfile a F) := by
  have h := mul_le_mul_of_nonneg_left hF.eight_mul_firstMoment_le_defect ha.le
  rw [firstMoment_rescaledConfiningProfile ha]
  nlinarith only [h]

/-- Every actual minimizer has an exact logarithmic energy decomposition after rescaling. -/
theorem IsHalfLineEnergyMinimizer.rescaled_energy_identity {a : ℝ} (ha : 1 ≤ a)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer (confiningHalfLineRatio a) F) :
    renormalizedConfiningGroundEnergy a =
      softLogarithmicHalfLineEnergy (rescaledConfiningProfile a F) +
      (a * criticalHalfLineExponentialDefect F -
        8 * criticalHalfLineFirstMoment (rescaledConfiningProfile a F)) +
      confiningGammaErrorForm a (cx (rescaledConfiningProfile a F)) +
      criticalHalfLineArithmeticRemainder F := by
  have ha0 := zero_lt_one.trans_le ha
  have hg := hF.1.rescaled_softLogarithmic ha0
  have hm : (∫ u, rescaledConfiningProfile a F u ^ 2) = 1 := by
    rw [integral_sq_rescaledConfiningProfile ha0, hF.2.1]
  have hc : unitaryRealDilation a (rescaledConfiningProfile a F) = F :=
    unitaryRealDilation_inv_cancel ha0 F
  have harch := hg.archForm_unitaryDilation ha
  rw [hc, hm, mul_one] at harch
  rw [renormalizedConfiningGroundEnergy, ← hF.2.2,
    criticalHalfLineFullEnergy_eq_arch_add_remainder _ hF.1,
    criticalAliasCoefficient_confiningHalfLineRatio ha0, harch,
    softLogarithmicHalfLineEnergy, criticalHalfLineExponentialDefect, hF.2.1]
  ring

/-- Bounded scaled excess gives a uniform physical first-moment bound after rescaling. -/
theorem rescaledConfiningProfile_firstMoment_le {a C : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hC : a * criticalHalfLineExponentialDefect F ≤ C) :
    criticalHalfLineFirstMoment (rescaledConfiningProfile a F) ≤ C / 8 := by
  have h := hF.rescaled_potential_error_nonneg ha
  linarith only [h, hC]

/-- The two remainder terms have a uniform lower bound tending to zero on actual minimizers. -/
theorem exists_minimizer_remainder_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {a : ℝ}, A ≤ a → ∀ {F : ℝ → ℝ},
      IsHalfLineEnergyMinimizer (confiningHalfLineRatio a) F →
      -ε ≤ confiningGammaErrorForm a (cx (rescaledConfiningProfile a F)) +
        criticalHalfLineArithmeticRemainder F := by
  obtain ⟨A₀, K, c, C, hA₀, _, _, hC, hstrong⟩ := criticalHalfLineGroundEnergy_strong_confinement
  obtain ⟨d, hd, harith⟩ := exists_arithmeticRemainder_small_of_excess (half_pos hε)
  obtain ⟨A₁, hA₁, hspec⟩ := exists_uniform_confiningGammaErrorForm_lower
    (div_nonneg hC.le (by norm_num : (0 : ℝ) ≤ 8)) (half_pos hε)
  refine ⟨max A₀ (max A₁ (C / d)), hA₀.trans (le_max_left _ _), ?_⟩
  intro a ha F hF
  have ha₀ := (le_max_left _ _).trans ha
  have hA₁a : A₁ ≤ a := (le_max_left A₁ (C / d)).trans ((le_max_right _ _).trans ha)
  have hCd : C / d ≤ a := (le_max_right A₁ (C / d)).trans ((le_max_right _ _).trans ha)
  have ha0 := zero_lt_one.trans_le (hA₀.trans ha₀)
  have hstrength := criticalAliasCoefficient_confiningHalfLineRatio ha0
  have hCa := ((hstrong (confiningHalfLineRatio a) (confiningHalfLineRatio_pos ha0)
    (by rwa [hstrength])).2 F hF).2
  rw [hstrength] at hCa
  have hδ : criticalHalfLineExponentialDefect F ≤ d := by
    have hh := (div_le_iff₀ hd).mp hCd
    exact (mul_le_mul_left ha0).mp (hCa.trans (by simpa only [mul_comm] using hh))
  have hA := (abs_lt.mp (harith hF.1 hF.2.1 hδ)).1
  have hg := hF.1.rescaled_softLogarithmic ha0
  have hm : (∫ u, ‖cx (rescaledConfiningProfile a F) u‖ ^ 2) = 1 := by
    simp only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [integral_sq_rescaledConfiningProfile ha0, hF.2.1]
  have hM : (∫ u, |u| * ‖cx (rescaledConfiningProfile a F) u‖ ^ 2) ≤ C / 8 := by
    rw [hg.integral_absMoment]
    exact rescaledConfiningProfile_firstMoment_le ha0 hF.1 hCa
  have hS := hspec hA₁a (f := cx (rescaledConfiningProfile a F))
    (hg.integrable.ofReal (𝕜 := ℂ)) hg.memLp_complex hm
    hg.logarithmic hg.integrable_absMoment hM
  linarith only [hA, hS]

#print axioms IsHalfLineEnergyMinimizer.rescaled_energy_identity
#print axioms exists_minimizer_remainder_lower
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
