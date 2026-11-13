import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Distinct confinements have distinct minimizing profiles

Subtracting two weak equations makes a common minimizer annihilate all
smooth tests after multiplication by an affine exponential. Distributional
uniqueness confines its support to one point, contradicting unit mass.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

private theorem locallyIntegrable_affine_exponential_mul {F : ℝ → ℝ}
    (hF : Integrable F) (c d : ℝ) :
    LocallyIntegrable (fun u => (c * Real.exp (-(8 * u)) - d) * F u) volume := by
  have hg : Continuous (fun u : ℝ => c * Real.exp (-(8 * u)) - d) := by fun_prop
  rw [locallyIntegrable_iff]
  intro k hk
  simpa only [mul_comm] using
    (hF.locallyIntegrable.integrableOn_isCompact hk).mul_continuousOn hg.continuousOn hk

private theorem ae_affine_exponential_ne_zero {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    ∀ᵐ u : ℝ, c * Real.exp (-(8 * u)) - d ≠ 0 := by
  by_cases hz : ∃ v : ℝ, c * Real.exp (-(8 * v)) - d = 0
  · obtain ⟨v, hv⟩ := hz
    have hne : ∀ᵐ u : ℝ, u ≠ v := by simp [ae_iff]
    filter_upwards [hne] with u hu
    intro he
    have hprod : c * (Real.exp (-(8 * u)) - Real.exp (-(8 * v))) = 0 := by
      nlinarith only [he, hv]
    have heq := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hc)
    have harg := Real.exp_injective heq
    exact hu (by linarith only [harg])
  · exact Eventually.of_forall fun u hu => hz ⟨u, hu⟩

/-- A normalized profile can minimize at only one positive ratio. -/
theorem halfLineEnergyMinimizer_ratio_unique {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F)
    (hFS : IsHalfLineEnergyMinimizer S F) : R = S := by
  by_contra hRS
  let c : ℝ := criticalAliasCoefficient R - criticalAliasCoefficient S
  let d : ℝ := criticalHalfLineGroundEnergy R - criticalHalfLineGroundEnergy S
  have hc : c ≠ 0 := by
    intro he
    exact hRS (criticalAliasCoefficient_injective_positive hR hS (sub_eq_zero.mp he))
  have hannihilate (G : ℝ → ℝ) (hG : CriticalHalfLineEnergyDomain G) :
      (∫ u, G u * ((c * Real.exp (-(8 * u)) - d) * F u)) = 0 := by
    have hr := IsHalfLineEnergyMinimizer.weakEquation hR hF hG
    have hs := IsHalfLineEnergyMinimizer.weakEquation hS hFS hG
    have hm := criticalHalfLineMixedEnergy_change_ratio R S hF.1 hG
    rw [hr, hs] at hm
    have hpair : Integrable (fun u => F u * G u) :=
      HTGeometry.integrable_mul_of_sq_integrable hF.1.meas.aestronglyMeasurable
        hG.meas.aestronglyMeasurable hF.1.sq hG.sq
    have hexp := hF.1.integrable_exponentialCross hG
    have heq : (fun u => G u * ((c * Real.exp (-(8 * u)) - d) * F u)) =
        fun u => c * (F u * G u * Real.exp (-(8 * u))) - d * (F u * G u) := by
      funext u
      ring
    rw [heq, integral_sub (hexp.const_mul c) (hpair.const_mul d),
      integral_const_mul, integral_const_mul]
    change c * criticalHalfLineExponentialPair F G - d * (∫ u, F u * G u) = 0
    dsimp only [c, d]
    nlinarith only [hm]
  have hzero : ∀ᵐ u : ℝ, u ∈ Iio (0 : ℝ) →
      (c * Real.exp (-(8 * u)) - d) * F u = 0 := by
    apply isOpen_Iio.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((locallyIntegrable_affine_exponential_mul hF.1.integrable c d).locallyIntegrableOn _)
    intro G hG hcompact hsupp
    have hnegative : ∀ u, 0 ≤ u → G u = 0 := by
      intro u hu
      by_contra hne
      have hlt : u < 0 := hsupp (subset_tsupport G hne)
      exact (not_lt_of_ge hu) hlt
    have hd := criticalHalfLineEnergyDomain_of_compact_negative
      (hG.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hcompact hnegative
    simpa only [smul_eq_mul] using hannihilate G hd
  have hFzero : F =ᵐ[volume] 0 := by
    filter_upwards [hzero, ae_affine_exponential_ne_zero hc d] with u hu hne
    change F u = 0
    by_cases hneg : u < 0
    · exact (mul_eq_zero.mp (hu hneg)).resolve_left hne
    · exact hF.1.support u (le_of_not_gt hneg)
  have hmass : (∫ u, F u ^ 2) = 0 := by
    calc
      _ = ∫ _u : ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hFzero] with u hu
        change F u = 0 at hu
        simp only [hu, zero_pow two_ne_zero]
      _ = 0 := integral_zero _ _
  rw [hF.2.1] at hmass
  norm_num at hmass

#print axioms halfLineEnergyMinimizer_ratio_unique

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
