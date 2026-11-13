import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningFixedTrialLimit
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineStrongLimit

/-!
# The finite logarithmic variational floor

The actual strong-confinement lower bound passes to every fixed trial.
A compact spline makes the limiting Rayleigh set nonempty. Approximating
its infimum gives the upper bound for renormalized actual ground energies.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri


/-- Ground energy with its universal linear and logarithmic terms removed. -/
def renormalizedConfiningGroundEnergy (a : ℝ) : ℝ :=
  criticalHalfLineGroundEnergy (confiningHalfLineRatio a) - a - Real.log a

/-- The Rayleigh floor of logarithmic spectral energy with linear confinement. -/
def softLogarithmicHalfLineGroundEnergy : ℝ :=
  sInf {e : ℝ | ∃ F : ℝ → ℝ, SoftLogarithmicHalfLineDomain F ∧
    (∫ u, F u ^ 2) = 1 ∧ softLogarithmicHalfLineEnergy F = e}

theorem softLogarithmicHalfLineEnergyRange_nonempty :
    ({e : ℝ | ∃ F : ℝ → ℝ, SoftLogarithmicHalfLineDomain F ∧
      (∫ u, F u ^ 2) = 1 ∧ softLogarithmicHalfLineEnergy F = e} : Set ℝ).Nonempty := by
  obtain ⟨F, hF, hm⟩ := exists_unit_criticalHalfLineEnergyDomain
  exact ⟨softLogarithmicHalfLineEnergy F, F, hF.softLogarithmic, hm, rfl⟩

/-- The actual confining lower bound passes through every fixed-trial limit. -/
theorem exists_softLogarithmicHalfLineEnergy_lower :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {F : ℝ → ℝ}, SoftLogarithmicHalfLineDomain F →
      (∫ u, F u ^ 2) = 1 → -K ≤ softLogarithmicHalfLineEnergy F := by
  obtain ⟨A, K, c, C, hA, hK, _, _, hbound⟩ := criticalHalfLineGroundEnergy_strong_confinement
  refine ⟨K, hK, ?_⟩
  intro F hF hm
  have h := le_of_tendsto (hF.tendsto_renormalized_trialEnergy hm).neg (show
      ∀ᶠ a : ℝ in atTop,
        -(criticalHalfLineFullEnergy (confiningHalfLineRatio a) (unitaryRealDilation a F) -
          a - Real.log a) ≤ K from by
    filter_upwards [hF.eventually_actual_dilation, eventually_ge_atTop A] with a hda ha
    have ha0 := zero_lt_one.trans_le (hA.trans ha)
    have hr := confiningHalfLineRatio_pos ha0
    have hc := criticalAliasCoefficient_confiningHalfLineRatio ha0
    have hb := (hbound (confiningHalfLineRatio a) hr (by rwa [hc])).1
    rw [hc] at hb
    have htest := criticalHalfLineGroundEnergy_le hr hda
      (by rw [integral_sq_unitaryRealDilation ha0, hm])
    have hlo := (abs_le.mp hb).1
    linarith only [hlo, htest])
  linarith only [h]

theorem softLogarithmicHalfLineEnergyRange_bddBelow :
    BddBelow {e : ℝ | ∃ F : ℝ → ℝ, SoftLogarithmicHalfLineDomain F ∧
      (∫ u, F u ^ 2) = 1 ∧ softLogarithmicHalfLineEnergy F = e} := by
  obtain ⟨K, _, hK⟩ := exists_softLogarithmicHalfLineEnergy_lower
  refine ⟨-K, ?_⟩
  rintro e ⟨F, hF, hm, rfl⟩
  exact hK hF hm

theorem softLogarithmicHalfLineGroundEnergy_le {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) (hm : (∫ u, F u ^ 2) = 1) :
    softLogarithmicHalfLineGroundEnergy ≤ softLogarithmicHalfLineEnergy F :=
  csInf_le softLogarithmicHalfLineEnergyRange_bddBelow ⟨F, hF, hm, rfl⟩

/-- Every strict upper neighborhood of the limiting floor eventually bounds the actual floor. -/
theorem eventually_renormalizedConfiningGroundEnergy_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop,
      renormalizedConfiningGroundEnergy a < softLogarithmicHalfLineGroundEnergy + ε := by
  obtain ⟨e, ⟨F, hF, hm, rfl⟩, he⟩ := exists_lt_of_csInf_lt
    softLogarithmicHalfLineEnergyRange_nonempty
    (show softLogarithmicHalfLineGroundEnergy < softLogarithmicHalfLineGroundEnergy + ε / 2 by
      linarith only [hε])
  have he' : softLogarithmicHalfLineEnergy F < softLogarithmicHalfLineGroundEnergy + ε := by
    linarith only [he, hε]
  filter_upwards [hF.eventually_actual_dilation, eventually_gt_atTop (0 : ℝ),
    (hF.tendsto_renormalized_trialEnergy hm).eventually (gt_mem_nhds he')] with a hda ha hsmall
  have htest := criticalHalfLineGroundEnergy_le (confiningHalfLineRatio_pos ha) hda
    (by rw [integral_sq_unitaryRealDilation ha, hm])
  dsimp only [renormalizedConfiningGroundEnergy]
  linarith only [htest, hsmall]

#print axioms exists_softLogarithmicHalfLineEnergy_lower
#print axioms eventually_renormalizedConfiningGroundEnergy_lt
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
