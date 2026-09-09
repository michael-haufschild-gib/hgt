import GaloisForLFunctions.HTGeometry.ConservativeDissipativeMasterFlow
import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityFisherBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

/-!
# Fisher coercivity along actual conservative–dissipative trajectories

The energy evolution mechanism of Schaffer–Exl (arXiv:2609.04530) combines
with the corpus's thermodynamic uncertainty inequality. The resulting
positive master trajectories dissipate at least half the Fisher current
cost. This cost has exactly the detailed-balance zero set, and its time
integral is bounded by twice the actual relative-energy drop.
-/
open scoped BigOperators NNReal
open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Weighted Fisher current cost of the constructed transport network. -/
def entropyFisherCost (a : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, entropyConductance a i j *
    pseudoEntropyProductionValue (Real.exp (x i)) (Real.exp (x j))

theorem entropyFisherCost_nonneg (a : ι → ι → ℝ) (x : ι → ℝ) : 0 ≤ entropyFisherCost a x := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (entropyConductance_nonneg a i j)
      (pseudoEntropyProductionValue_nonneg (Real.exp_pos _) (Real.exp_pos _))

/-- The previously formalized thermodynamic uncertainty inequality controls the whole network. -/
theorem entropyFisherCost_le_production (a : ι → ι → ℝ) (x : ι → ℝ) :
    entropyFisherCost a x ≤ ∑ i, ∑ j, entropyConductance a i j *
      entropyProductionValue (Real.exp (x i)) (Real.exp (x j)) := by
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left
      (pseudoEntropyProductionValue_le_entropyProductionValue (Real.exp_pos _) (Real.exp_pos _))
      (entropyConductance_nonneg a i j)

/-- Fisher current cost has exactly the established detailed-balance zero set. -/
theorem entropyFisherCost_eq_zero_iff (a : ι → ι → ℝ) (r x : ι → ℝ) :
    entropyFisherCost a x = 0 ↔ relativeEntropyField a r x = 0 := by
  rw [relativeEntropyField_eq_zero_iff, entropyFisherCost]
  have hp : ∀ i j, 0 ≤ entropyConductance a i j *
      pseudoEntropyProductionValue (Real.exp (x i)) (Real.exp (x j)) := fun i j =>
    mul_nonneg (entropyConductance_nonneg a i j)
      (pseudoEntropyProductionValue_nonneg (Real.exp_pos _) (Real.exp_pos _))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hp i j)]
  simp only [Finset.mem_univ, forall_true_left]
  simp_rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp _ j)]
  simp only [Finset.mem_univ, forall_true_left, mul_eq_zero, entropyConductance_eq_zero_iff,
    pseudoEntropyProductionValue_eq_zero_iff_eq (Real.exp_pos _) (Real.exp_pos _),
    Real.exp_injective.eq_iff]

/-- Fisher cost is continuous at every logarithmic state, including zero currents. -/
theorem continuous_entropyFisherCost (a : ι → ι → ℝ) : Continuous (entropyFisherCost a) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  apply continuous_const.mul
  unfold pseudoEntropyProductionValue
  apply Continuous.div
  · exact continuous_const.mul (((Real.continuous_exp.comp (continuous_apply i)).sub (Real.continuous_exp.comp (continuous_apply j))).pow 2)
  · exact (Real.continuous_exp.comp (continuous_apply i)).add (Real.continuous_exp.comp (continuous_apply j))
  · intro x
    exact (add_pos (Real.exp_pos (x i)) (Real.exp_pos (x j))).ne'

/-- Actual entropy dissipation controls the instantaneous Fisher current cost. -/
theorem masterLogFlow_deriv_energy_le_fisher (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    deriv (fun s => relativeEntropyEnergy r (masterLogFlow a r x s)) t ≤
      -((2 : ℝ)⁻¹) * entropyFisherCost a (masterLogFlow a r x t) := by
  rw [(hasDerivAt_masterLogFlow_energy a r x t).deriv]
  exact mul_le_mul_of_nonpos_left (entropyFisherCost_le_production a _)
    (neg_nonpos.mpr (by positivity))

/-- Vanishing instantaneous energy loss is exactly nonlinear stationarity. -/
theorem masterLogFlow_deriv_energy_eq_zero_iff (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    deriv (fun s => relativeEntropyEnergy r (masterLogFlow a r x s)) t = 0 ↔
      relativeEntropyField a r (masterLogFlow a r x t) = 0 := by
  rw [(hasDerivAt_masterLogFlow_energy a r x t).deriv, mul_eq_zero]
  simp only [neg_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  rw [entropyProduction_eq_zero_iff, relativeEntropyField_eq_zero_iff]

/-- Accumulated Fisher current cost is bounded by twice the actual free-energy drop. -/
theorem masterLogFlow_integral_fisher_le_energy_drop (a : ι → ι → ℝ) (r x : ι → ℝ) (T : ℝ≥0) :
    (∫ t in (0 : ℝ)..(T : ℝ), entropyFisherCost a (masterLogFlow a r x t)) ≤
      2 * (relativeEntropyEnergy r x - relativeEntropyEnergy r (masterLogFlow a r x T)) := by
  let E : ℝ → ℝ := fun t => relativeEntropyEnergy r (masterLogFlow a r x t)
  let D : ℝ → ℝ := fun t => -((2 : ℝ)⁻¹) * ∑ i, ∑ j, entropyConductance a i j *
    entropyProductionValue (Real.exp (masterLogFlow a r x t i))
      (Real.exp (masterLogFlow a r x t j))
  have he (t : ℝ) (ht : 0 ≤ t) : HasDerivAt E (D t) t :=
    hasDerivAt_masterLogFlow_energy a r x ⟨t, ht⟩
  have hc : ContinuousOn (fun t => -(2 * E t)) (Icc 0 (T : ℝ)) := by
    intro t ht
    exact (((he t ht.1).const_mul 2).neg.continuousAt).continuousWithinAt
  have hf : IntegrableOn (fun t => entropyFisherCost a (masterLogFlow a r x t)) (Icc 0 (T : ℝ)) := by
    apply ContinuousOn.integrableOn_Icc
    exact (continuous_entropyFisherCost a).comp_continuousOn
      ((continuousOn_masterLogFlow a r x).mono (fun t ht => ht.1))
  have hb := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le T.coe_nonneg hc
    (fun t ht => ((he t ht.1.le).const_mul 2).neg.hasDerivWithinAt) hf
    (fun t ht => show entropyFisherCost a (masterLogFlow a r x t) ≤ -(2 * D t) from by
      dsimp [D]
      convert entropyFisherCost_le_production a (masterLogFlow a r x t) using 1
      ring)
  have hz : E 0 = relativeEntropyEnergy r x := by simp only [E, masterLogFlow_zero]
  rw [hz] at hb
  convert hb using 1
  dsimp [E]
  ring

end
end GaloisForLFunctions.HTGeometry.SchafferExl
