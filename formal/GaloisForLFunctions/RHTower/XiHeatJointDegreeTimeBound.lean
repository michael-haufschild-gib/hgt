import GaloisForLFunctions.RHTower.XiHeatFiniteUniformPositivity
import GaloisForLFunctions.RHTower.XiHeatQuarterPowerDebt

/-!
# A quantitative joint order and heat-time bound for the actual Xi Hankel family

The sampling cutoff is shared by all orders. Beyond that cutoff, the complete
Hankel form has a stated lower margin: its independent sampling floor minus
the quarter-power phase budget. An explicit degree-dependent time restriction
makes the margin positive. This does not assert all-order positivity at a fixed
positive time, or transfer positivity to the entire heat-time half-line.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators

/-- One cutoff, every order, every vector, with all degree and time dependence displayed. -/
theorem xiHeatHankelForm_eventually_joint_lower_bound :
    ∀ᶠ τ : ℝ in atBot, ∀ (N : ℕ) (a : Fin N → ℝ),
      (xiHeatSamplingEnergyFloor N -
        xiHeatFiniteQuarterConstant N * Real.exp (τ / 4) * xiHeatThreeHalvesMass) *
          (∑ j, a j ^ 2) ≤
        xiHeatHankelForm N (xiHeatScaledCoefficients a τ) (Real.exp τ) := by
  filter_upwards [xiHeatFiniteNormEnergy_eventually_uniform_floor] with τ hK N a
  have hD := xiHeatFinitePhaseDebt_le_quarter a τ
  have hK' := hK N a
  rw [xiHeatHankelForm_scaled_eq_energy_sub_debt]
  nlinarith only [hD, hK']

def xiHeatJointDebtConstant (N : ℕ) : ℝ :=
  1 + xiHeatFiniteQuarterConstant N * xiHeatThreeHalvesMass

theorem xiHeatJointDebtConstant_pos (N : ℕ) : 0 < xiHeatJointDebtConstant N := by
  have h := mul_nonneg (xiHeatFiniteQuarterConstant_nonneg N) xiHeatThreeHalvesMass_nonneg
  dsimp only [xiHeatJointDebtConstant]
  linarith

def xiHeatJointLogTime (N : ℕ) : ℝ :=
  4 * Real.log (xiHeatSamplingEnergyFloor N / (2 * xiHeatJointDebtConstant N))

/-- An explicit positive region for the complete family, uniform over all coefficient vectors. -/
theorem xiHeatHankelForm_joint_degree_time_coercive :
    ∃ τ₀ : ℝ, ∀ (N : ℕ) (τ : ℝ), τ ≤ min τ₀ (xiHeatJointLogTime N) →
      ∀ a : Fin N → ℝ,
        (xiHeatSamplingEnergyFloor N / 2) * (∑ j, a j ^ 2) ≤
          xiHeatHankelForm N (xiHeatScaledCoefficients a τ) (Real.exp τ) := by
  obtain ⟨τ₀, hτ₀⟩ := eventually_atBot.mp xiHeatHankelForm_eventually_joint_lower_bound
  refine ⟨τ₀, ?_⟩
  intro N τ hτ a
  have htime : τ ≤ xiHeatJointLogTime N := hτ.trans (min_le_right _ _)
  have hratio : 0 < xiHeatSamplingEnergyFloor N / (2 * xiHeatJointDebtConstant N) :=
    div_pos (xiHeatSamplingEnergyFloor_pos N) (mul_pos (by positivity) (xiHeatJointDebtConstant_pos N))
  have hexp : Real.exp (τ / 4) ≤
      xiHeatSamplingEnergyFloor N / (2 * xiHeatJointDebtConstant N) := by
    rw [← Real.exp_log hratio]
    apply Real.exp_le_exp.mpr
    dsimp only [xiHeatJointLogTime] at htime
    linarith only [htime]
  have hsmall := (le_div_iff₀
    (mul_pos (show (0 : ℝ) < 2 by positivity) (xiHeatJointDebtConstant_pos N))).mp hexp
  have hdom : xiHeatFiniteQuarterConstant N * Real.exp (τ / 4) * xiHeatThreeHalvesMass ≤
      xiHeatJointDebtConstant N * Real.exp (τ / 4) := by
    dsimp only [xiHeatJointDebtConstant]
    nlinarith only [Real.exp_pos (τ / 4)]
  have hmargin : xiHeatSamplingEnergyFloor N / 2 ≤ xiHeatSamplingEnergyFloor N -
      xiHeatFiniteQuarterConstant N * Real.exp (τ / 4) * xiHeatThreeHalvesMass := by
    nlinarith only [hsmall, hdom]
  exact (mul_le_mul_of_nonneg_right hmargin
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
      (hτ₀ τ (hτ.trans (min_le_left _ _)) N a)

end
end RHTower
