import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Defect
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Transition

/-! # Vanishing collision excess in the elementary transition window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary

open Finset Filter Real Crossover
open ExactSubsystems.ThermalShells.Packets.Occupation
open scoped Topology

/-- The temperature window approaches the harmonic prime exponent. -/
theorem index_limit (c : ℝ) :
    Tendsto (fun N : ℕ => drift c N/log N) atTop (𝓝 0) := by
  have h := ((displacement_small c).comp logEnergy_growth).mul
    ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp logEnergy_growth)
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [logEnergy_growth.eventually_gt_atTop 0,eventually_ge_atTop 2] with N hL hN
  have p : 0<log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  change drift c N/log (log N)*((log (log N))^1*exp (-log (log N)))=_
  rw [pow_one,exp_neg,exp_log p]
  field_simp [(show 0<log (log (N:ℝ)) from hL).ne',p.ne']

theorem mass_growth (c : ℝ) :
    Tendsto (fun N : ℕ => powerMass (drift c N/log N) N) atTop atTop := by
  have h := Tendsto.pos_mul_atTop (by positivity : 0<1+exp c) (transition_masses c).1 logEnergy_growth
  apply h.congr'
  filter_upwards [logEnergy_growth.eventually_gt_atTop 0] with N hL
  exact div_mul_cancel₀ _ (show 0<log (log (N:ℝ)) from hL).ne'

/-- The restored ordinary heat mass approaches the ordered mass on actual
integer shells, with a finite error controlled by collisions. -/
theorem excess_limit (m : ℕ) (c : ℝ) :
    Tendsto (fun N : ℕ => excess m (drift c N/log N) N) atTop (𝓝 0) := by
  let K : ℝ := m.factorial
  have Kpos : 1≤K := by
    change (1:ℝ) ≤ (m.factorial:ℝ)
    exact_mod_cast (show 1 ≤ m.factorial from Nat.factorial_pos m)
  have upper := ((mass_growth c).const_div_atTop 1).const_mul ((K-1)*(m.choose 2:ℝ))
  rw [mul_zero] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper
  · exact Eventually.of_forall fun _ => excess_nonneg _ _ _
  · filter_upwards [(index_limit c).eventually_le_const zero_lt_one] with N ha
    let a := drift c N/log N
    have h := repeat_le_max (primeProbability a N) (primeProbability_nonneg a N)
      (primeProbability_sum a N) m (primeProbability_le (show a≤1 from ha) N)
    exact (excess_le_repeat m a N).trans ((mul_le_mul_of_nonneg_left h
      (sub_nonneg.mpr Kpos)).trans_eq (mul_assoc _ _ _).symm)

#print axioms index_limit
#print axioms mass_growth
#print axioms excess_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary
