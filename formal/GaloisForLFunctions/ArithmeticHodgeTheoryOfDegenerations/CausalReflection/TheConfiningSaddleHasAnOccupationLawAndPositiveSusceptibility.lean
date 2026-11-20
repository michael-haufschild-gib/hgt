import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningGlobalTransverseGapAndResponse
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineGroundEnergyCurvature

/-!
# Occupation law and coupling susceptibility of the confining saddle

At every positive confinement ratio `R`, the half-line energy obeys the occupation law
`E_R(G) ≥ λ(R) ∫ G²` with equality exactly on the saddle line `G = c F_R`, `c² = ∫ G²`.
On the occupation ball `∫ G² ≤ 1` this is the linear competition `min(0, λ(R))` between the
vacuum and the saddle.

The coupling energy `μ(t) = λ(t⁻¹)` has positive susceptibility: it is strictly concave and
`C^{1,1}_loc` on `(0, ∞)`, with strictly decreasing slope `μ'(t) = a(1) W₈(F_{t⁻¹})`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- **Occupation law.** At every positive ratio, `E_R(G) ≥ λ(R) ∫ G²` on the half-line domain,
with equality exactly when `G = c F_R` almost everywhere for a scalar `c` with `c² = ∫ G²`.
Equality makes the shifted energy vanish, so the neutral part of `G` has zero exponential mass by
the transverse control. -/
theorem criticalHalfLineFullEnergy_eq_groundEnergy_mul_mass_iff {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineGroundEnergy R * (∫ u, G u ^ 2) ≤ criticalHalfLineFullEnergy R G ∧
      (criticalHalfLineFullEnergy R G = criticalHalfLineGroundEnergy R * (∫ u, G u ^ 2) ↔
        ∃ c : ℝ, c ^ 2 = (∫ u, G u ^ 2) ∧ G =ᵐ[volume] fun u => c * F u) := by
  refine ⟨criticalHalfLineGroundEnergy_mul_mass_le_all hR hG, ⟨fun hE => ?_, ?_⟩⟩
  · obtain ⟨γ, hγ, hgap⟩ := hF.controls_neutralPart hR
    have hQ0 : confiningShiftedEnergy R G = 0 := by
      unfold confiningShiftedEnergy
      rw [hE, sub_self]
    have hn_le := hgap hG
    rw [hQ0] at hn_le
    have hn_nonneg : 0 ≤ ∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u)) :=
      integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    have hn0 : (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) = 0 :=
      le_antisymm (by nlinarith only [hγ, hn_le, hn_nonneg]) hn_nonneg
    have hdN := hF.1.neutralPart hG
    have hmN0 : (∫ u, criticalHalfLineNeutralPart F G u ^ 2) = 0 :=
      le_antisymm (hdN.square_mass_le_exponential_mass.trans_eq hn0)
        (integral_nonneg fun u => sq_nonneg _)
    have hNae : ∀ᵐ u ∂volume, criticalHalfLineNeutralPart F G u = 0 := by
      have hae := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun u => sq_nonneg (criticalHalfLineNeutralPart F G u)) hdN.sq).mp hmN0
      filter_upwards [hae] with u hu
      exact (pow_eq_zero_iff two_ne_zero).mp hu
    have hG_ae : G =ᵐ[volume] fun u => (∫ v, F v * G v) * F u := by
      filter_upwards [hNae] with u hu
      change G u - (∫ v, F v * G v) * F u = 0 at hu
      linarith only [hu]
    refine ⟨∫ v, F v * G v, ?_, hG_ae⟩
    calc (∫ v, F v * G v) ^ 2 = ∫ u, (∫ v, F v * G v) ^ 2 * F u ^ 2 := by
          rw [integral_const_mul, hF.2.1, mul_one]
      _ = ∫ u, G u ^ 2 := by
          apply integral_congr_ae
          filter_upwards [hG_ae] with u hu
          rw [hu, mul_pow]
  · rintro ⟨c, hc, hG_ae⟩
    rw [criticalHalfLineFullEnergy_congr_ae hG (hF.1.const_mul c) hG_ae,
      criticalHalfLineFullEnergy_const_mul, hF.2.2, ← hc]
    ring

/-- **Positive coupling susceptibility.** The coupling energy `μ(t) = λ(t⁻¹)` is strictly concave
and `C¹` on `(0, ∞)`, its slope `μ'(t) = a(1) W₈(F_{t⁻¹})` is locally Lipschitz (so `μ` is
`C^{1,1}_loc`) and strictly decreasing. -/
theorem confiningHalfLineGroundEnergy_susceptibility :
    StrictConcaveOn ℝ (Ioi 0) confiningHalfLineGroundEnergy ∧
      ContDiffOn ℝ 1 confiningHalfLineGroundEnergy (Ioi 0) ∧
      LocallyLipschitzOn (Ioi 0) (deriv confiningHalfLineGroundEnergy) ∧
      StrictAntiOn (deriv confiningHalfLineGroundEnergy) (Ioi 0) ∧
      ∀ t : ℝ, 0 < t → ∀ F : ℝ → ℝ, IsHalfLineEnergyMinimizer t⁻¹ F →
        deriv confiningHalfLineGroundEnergy t =
          criticalAliasCoefficient 1 * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  refine ⟨⟨convex_Ioi 0, fun x hx y hy hxy a b ha hb hab => ?_⟩,
    contDiffOn_one_confiningHalfLineGroundEnergy,
    locallyLipschitzOn_deriv_confiningHalfLineGroundEnergy, ?_,
    fun t ht F hF => (hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer ht hF).deriv⟩
  · simpa only [smul_eq_mul] using confiningHalfLineGroundEnergy_strict_jensen hx hy hxy ha hb hab
  · intro x hx y hy hxy
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr hx')
    obtain ⟨G, hG⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr hy')
    rw [(hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer hx' hF).deriv,
      (hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer hy' hG).deriv]
    exact mul_lt_mul_of_pos_left
      (halfLineEnergyMinimizer_exponential_mass_strict_antitone hx' hxy hF hG)
      (criticalAliasCoefficient_positive zero_lt_one)

#print axioms criticalHalfLineFullEnergy_eq_groundEnergy_mul_mass_iff
#print axioms confiningHalfLineGroundEnergy_susceptibility

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
