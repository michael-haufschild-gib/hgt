import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineExponentialBarrierJumps
import GaloisForLFunctions.FiniteFreeProbability.JensenSaddleError

/-!
# Uniform control of small Gamma jumps

The exponential correction is bounded by a constant times displacement on
the unit interval. The finite first Lévy moment therefore bounds the entire
small-jump loss independently of the positive truncation level and cutoff.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- A constant controlling all small-jump corrections for an exponential barrier. -/
def halfLineBarrierSmallJumpConstant (β : ℝ) : ℝ :=
  β * Real.exp β * ∫ h in Ioi (0 : ℝ), h * archLevyDensity h

theorem halfLineBarrierSmallJumpConstant_nonneg {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ halfLineBarrierSmallJumpConstant β := by
  apply mul_nonneg (mul_nonneg hβ (Real.exp_pos _).le)
  exact setIntegral_nonneg measurableSet_Ioi fun h hh =>
    mul_nonneg hh.le (archLevyDensity_pos hh).le

/-- On the unit interval the symmetric exponential correction has a linear majorant. -/
theorem exponentialBarrier_jump_correction_bound {β h : ℝ}
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    0 ≤ Real.exp (β * h) + Real.exp (-(β * h)) - 2 ∧
      Real.exp (β * h) + Real.exp (-(β * h)) - 2 ≤ β * Real.exp β * h := by
  have hp := Real.add_one_le_exp (β * h)
  have hn := Real.add_one_le_exp (-(β * h))
  refine ⟨by linarith only [hp, hn], ?_⟩
  have hneg : Real.exp (-(β * h)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hβ hh))
  have hpos := FiniteFreeProbability.exp_sub_one_le_mul_exp (y := β * h)
  have hexp : Real.exp (β * h) ≤ Real.exp β :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hh1 hβ).trans_eq (mul_one _))
  have hb := mul_le_mul_of_nonneg_left hexp (mul_nonneg hβ hh)
  nlinarith only [hneg, hpos, hb]

/-- All jumps below any cutoff at most one have a common lower bound against a positive level. -/
theorem CriticalHalfLineEnergyDomain.exponentialBarrier_smallGamma_lower {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {β t δ : ℝ}
    (hβ : 0 < β) (ht : 0 ≤ t) (hδ1 : δ ≤ 1) :
    -halfLineBarrierSmallJumpConstant β *
      (∫ u, F u * exponentialBarrierPositiveLevel β t F u) ≤
      ∫ h in Ioc 0 δ, halfLineGammaMixedJump F (exponentialBarrierPositiveLevel β t F) h := by
  let M : ℝ := ∫ u, F u * exponentialBarrierPositiveLevel β t F u
  have hM : 0 ≤ M := integral_nonneg fun u =>
    hF.mul_exponentialBarrierPositiveLevel_nonneg ht β u
  have hj := integrableOn_halfLineGammaMixedJump hF (hF.exponentialBarrierPositiveLevel hβ ht)
  have hi := CHMDDoobGraph.integrableOn_mul_archLevyDensity
  have hsubset : Ioc (0 : ℝ) δ ⊆ Ioi 0 := fun _ hh => hh.1
  have hrow : (∫ h in Ioc 0 δ, h * archLevyDensity h) ≤
      ∫ h in Ioi 0, h * archLevyDensity h := by
    apply setIntegral_mono_set hi
      ((ae_restrict_mem measurableSet_Ioi).mono fun h hh =>
        mul_nonneg hh.le (archLevyDensity_pos hh).le)
    exact Eventually.of_forall fun h hh => hsubset hh
  have hk : 0 ≤ β * Real.exp β * M := mul_nonneg (mul_nonneg hβ.le (Real.exp_pos _).le) hM
  have hscaled := mul_le_mul_of_nonneg_left hrow hk
  calc
    _ ≤ -(β * Real.exp β * M) * (∫ h in Ioc 0 δ, h * archLevyDensity h) := by
      dsimp only [halfLineBarrierSmallJumpConstant, M] at hscaled ⊢
      nlinarith only [hscaled]
    _ = ∫ h in Ioc 0 δ, -(β * Real.exp β * M) * (h * archLevyDensity h) :=
      (integral_const_mul _ _).symm
    _ ≤ _ := by
      apply integral_mono_ae ((hi.mono_set hsubset).const_mul _) (hj.mono_set hsubset)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
      have hlo := hF.exponentialBarrier_levyJump_lower hβ ht hh.1
      have hc := (exponentialBarrier_jump_correction_bound hβ.le hh.1.le
        (hh.2.trans hδ1)).2
      have hw := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (archLevyDensity_pos hh.1).le) hM
      change archLevyDensity h * (2 - Real.exp (β * h) - Real.exp (-(β * h))) * M ≤ _ at hlo
      nlinarith only [hlo, hw]

#print axioms CriticalHalfLineEnergyDomain.exponentialBarrier_smallGamma_lower
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
