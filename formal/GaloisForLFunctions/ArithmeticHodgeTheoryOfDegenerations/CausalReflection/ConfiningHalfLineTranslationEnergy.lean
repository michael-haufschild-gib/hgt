import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation

/-!
# Translation energy of a confining minimizer

Exponential absorption retains the entire Gamma form as well as half the
confining potential. The weak equation then identifies the exact energy of
a translation difference after subtracting the attained ordinary-mass floor.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- Arithmetic terms can be absorbed without discarding the Gamma energy. -/
theorem criticalHalfLineFullEnergy_arch_coercive_remainder {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {F : ℝ → ℝ}, CriticalHalfLineEnergyDomain F →
      archForm F + (criticalAliasCoefficient R / 2) *
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ≤
        criticalHalfLineFullEnergy R F + B * ∫ u, F u ^ 2 := by
  let J : ℝ := ∫ u : ℝ, Real.exp (-|u|)
  let C : ℝ := 2 * vonMangoldtThreeHalvesMass + 2 * J
  have hJ : 0 ≤ J := integral_nonneg fun u => (Real.exp_pos _).le
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (by norm_num) vonMangoldtThreeHalvesMass_nonneg)
    (mul_nonneg (by norm_num) hJ)
  have ha := criticalAliasCoefficient_positive hR
  have hl : Tendsto (fun Y : ℝ => C * Real.exp (-(6 * Y))) atTop (𝓝 0) := by
    have ht : Tendsto (fun Y : ℝ => 6 * Y) atTop atTop :=
      tendsto_id.const_mul_atTop (by norm_num)
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul C
  obtain ⟨Y, hsmall, hY⟩ :=
    ((hl.eventually (gt_mem_nhds (half_pos ha))).and (eventually_ge_atTop (0 : ℝ))).exists
  refine ⟨C * Real.exp (2 * Y), mul_nonneg hC (Real.exp_pos _).le, ?_⟩
  intro F hF
  have hp := (le_abs_self (primeSum F)).trans hF.prime_bound
  have hs := hF.sinh_bound
  have hw := (exponentialSourceMass_le_of_support hY hF.meas.aestronglyMeasurable
    hF.sq hF.exponential (Eventually.of_forall fun u hu =>
      hF.support u (hY.trans hu.le))).2
  have hcw := mul_le_mul_of_nonneg_left hw hC
  have hW : 0 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have he := mul_le_mul_of_nonneg_right hsmall.le hW
  dsimp only [criticalHalfLineFullEnergy]
  rw [halfLineExpMass_eq_full hF.support]
  dsimp only [C, J] at hcw he ⊢
  nlinarith only [hp, hs, hcw, he, sq_nonneg (coshHalfMoment F)]

/-- Translating any confining minimizer has an exact shifted-energy cost. -/
theorem IsHalfLineEnergyMinimizer.translation_difference_energy
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F)
    {h : ℝ} (hh : 0 ≤ h) :
    criticalHalfLineFullEnergy R (fun u => F (u + h) - F u) -
      criticalHalfLineGroundEnergy R * (∫ u, (F (u + h) - F u) ^ 2) =
      criticalAliasCoefficient R * (Real.exp (8 * h) - 1) *
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
  have hdT := hF.1.causalTranslate hh
  have hE := criticalHalfLineFullEnergy_add_const_mul R hdT hF.1 (-1)
  have hM := criticalHalfLine_square_mass_add_const_mul hdT hF.1 (-1)
  have hT := criticalHalfLineFullEnergy_comp_add_right hF.1 h R
    (fun u hu => hF.1.support _ (add_nonneg hu hh))
  have hmT : (∫ u, F (u + h) ^ 2) = 1 := by
    rw [integral_add_right_eq_self (fun u => F u ^ 2) h, hF.2.1]
  have hw : criticalHalfLineMixedEnergy R (fun u => F (u + h)) F =
      criticalHalfLineGroundEnergy R * (∫ u, F (u + h) * F u) := by
    rw [criticalHalfLineMixedEnergy_symm R hdT hF.1, hF.weakEquation hR hdT]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun u => mul_comm (F u) (F (u + h)))
  have hdiff : (fun u => F (u + h) + (-1) * F u) =
      (fun u => F (u + h) - F u) := by
    funext u
    ring
  rw [hdiff, hT, hF.2.2, hw] at hE
  rw [hdiff, hmT, hF.2.1] at hM
  linear_combination hE - criticalHalfLineGroundEnergy R * hM

#print axioms criticalHalfLineFullEnergy_arch_coercive_remainder
#print axioms IsHalfLineEnergyMinimizer.translation_difference_energy
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
