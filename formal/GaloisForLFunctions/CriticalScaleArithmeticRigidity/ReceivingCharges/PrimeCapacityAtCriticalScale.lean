import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceCapacityGrowth
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingConstantOfTheTiltedSpline

/-!
# Prime dilation capacity is smaller than the critical overlap

The doubly logarithmic capacity is negligible compared with every
positive eighth-root critical schedule. Even its exact minimizing
packet at nonzero fixed charge therefore costs more than the reciprocal
overlap scale.
-/

noncomputable section
open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity
open ArithmeticCouplingTheory ArithmeticHodgeTheoryOfDegenerations

private theorem tendsto_log_log_div_critical_overlap {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.log (Real.log N) / c N) atTop (𝓝 0) := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hinv : Tendsto (fun N : ℕ => Real.log N / c N ^ 8) atTop (𝓝 R⁻¹) := by
    simpa only [inv_div] using hcrit.inv₀ hR.ne'
  have hlog := (Real.continuousAt_log (inv_ne_zero hR.ne')).tendsto.comp hinv
  have hsmall : Tendsto (fun N => Real.log (c N) / c N) atTop (𝓝 (0 : ℝ)) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcinf
  have h := (hlog.div_atTop hcinf).add (hsmall.const_mul 8)
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  dsimp only [Function.comp_def]
  rw [Real.log_div hL.ne' (pow_ne_zero 8 hc0.ne'), Real.log_pow]
  push_cast
  ring

/-- The full receiving capacity is negligible relative to every positive critical overlap. -/
theorem tendsto_primeIncidenceReceivingCapacity_div_critical_overlap {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N / c N)
      atTop (𝓝 0) := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  obtain ⟨C, _, hb⟩ := primeIncidenceReceivingCapacity_log_log_bounded
  have he : Tendsto (fun N : ℕ =>
      (primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N -
        Real.log (Real.log N)) / c N) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N => C / c N) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop hcinf
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hc0]
    exact div_le_div_of_nonneg_right (hb N hN) hc0.le
  have h := he.add (tendsto_log_log_div_critical_overlap hc hR hcrit)
  simp only [zero_add] at h
  exact h.congr fun N => by ring

private theorem full_prime_capacity_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N := by
  apply primeIncidenceReceivingCapacity_pos
  · exact ⟨2, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hN⟩, Nat.prime_two⟩⟩
  · exact fun p hp => (mem_filter.mp hp).2
  · exact fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2

/-- Nonzero fixed charge has minimum dilation cost strictly above the reciprocal critical scale. -/
theorem tendsto_critical_overlap_mul_prime_charge_cost {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun N : ℕ => c N *
      (t ^ 2 / primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N)) atTop atTop := by
  have hz := tendsto_primeIncidenceReceivingCapacity_div_critical_overlap hc hR hcrit
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  apply tendsto_atTop.mpr
  intro A
  let B := max A 0 + 1
  have hB : 0 < B := by dsimp only [B]; linarith only [le_max_right A 0]
  have hAB : A ≤ B := by dsimp only [B]; linarith only [le_max_left A 0]
  filter_upwards [eventually_ge_atTop 2,
    hz.eventually (gt_mem_nhds (div_pos ht2 hB))] with N hN hsmall
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hC := full_prime_capacity_pos hN
  have hmul := (div_lt_div_iff₀ hc0 hB).mp hsmall
  have hb : B < c N * (t ^ 2 /
      primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N) := by
    rw [mul_div_assoc, lt_div_iff₀ hC]
    nlinarith only [hmul]
  exact hAB.trans hb.le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity

#print axioms GaloisForLFunctions.CriticalScaleArithmeticRigidity.tendsto_primeIncidenceReceivingCapacity_div_critical_overlap
#print axioms GaloisForLFunctions.CriticalScaleArithmeticRigidity.tendsto_critical_overlap_mul_prime_charge_cost
