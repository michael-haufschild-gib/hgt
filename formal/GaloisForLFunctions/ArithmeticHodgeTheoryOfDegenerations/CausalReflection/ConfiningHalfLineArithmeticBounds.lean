import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineEnergyGap

/-!
# Uniform arithmetic remainder under confinement

Weighted Cauchy–Schwarz controls both polar moments. Together with the
complete prime-form bound, this isolates the Gamma form and exponential
confinement with an error bounded by ordinary and exponential square mass.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

theorem CriticalHalfLineEnergyDomain.cosh_bound {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    coshHalfMoment F ^ 2 ≤ exponentialSourceMass F * (∫ u : ℝ, Real.exp (-|u|)) := by
  have h := (abs_integral_mul_kernel_le hF.weighted
    (Real.continuous_cosh.comp (continuous_id.div_const 2)) abs_cosh_half_le_exp).2
  have hi : 0 ≤ ∫ u : ℝ, Real.exp (-|u|) := integral_nonneg fun u => (Real.exp_pos _).le
  have hh := pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (exponentialSourceMass_nonneg F),
    Real.sq_sqrt hi, coshHalfMoment, Function.comp_apply, id_eq] using hh

/-- The complete prime and pole terms have a ratio-independent mass bound. -/
theorem criticalHalfLineFullEnergy_arch_remainder_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) {F : ℝ → ℝ}, CriticalHalfLineEnergyDomain F →
      |criticalHalfLineFullEnergy R F - archForm F - criticalAliasCoefficient R *
        (∫ u, F u ^ 2 * Real.exp (-(8 * u)))| ≤
          C * ((∫ u, F u ^ 2) + (∫ u, F u ^ 2 * Real.exp (-(8 * u)))) := by
  let J : ℝ := ∫ u : ℝ, Real.exp (-|u|)
  let C : ℝ := 2 * vonMangoldtThreeHalvesMass + 2 * J
  have hJ : 0 ≤ J := integral_nonneg fun u => (Real.exp_pos _).le
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (by norm_num) vonMangoldtThreeHalvesMass_nonneg)
    (mul_nonneg (by norm_num) hJ)
  refine ⟨C, hC, ?_⟩
  intro R F hF
  have hp := hF.prime_bound
  have hc := hF.cosh_bound
  have hs := hF.sinh_bound
  have hsource := exponentialSourceMass_le_of_support (Y := 0) le_rfl
    hF.meas.aestronglyMeasurable hF.sq hF.exponential
    (Eventually.of_forall fun u hu => hF.support u hu.le)
  have hsource' : exponentialSourceMass F ≤ (∫ u, F u ^ 2) +
      (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
    simpa only [mul_zero, neg_zero, Real.exp_zero, one_mul] using hsource.2
  have hraw : |criticalHalfLineFullEnergy R F - archForm F - criticalAliasCoefficient R *
      (∫ u, F u ^ 2 * Real.exp (-(8 * u)))| ≤ C * exponentialSourceMass F := by
    unfold criticalHalfLineFullEnergy
    rw [halfLineExpMass_eq_full hF.support]
    apply abs_le.mpr
    dsimp only [C, J]
    constructor
    · nlinarith only [hp, le_abs_self (primeSum F), hs, sq_nonneg (coshHalfMoment F)]
    · nlinarith only [hp, neg_abs_le (primeSum F), hc, sq_nonneg (sinhHalfMoment F)]
  exact hraw.trans (mul_le_mul_of_nonneg_left hsource' hC)

#print axioms criticalHalfLineFullEnergy_arch_remainder_bound

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
