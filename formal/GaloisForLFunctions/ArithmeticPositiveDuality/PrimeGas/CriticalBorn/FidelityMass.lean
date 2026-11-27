import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.LogEnergy
import GaloisForLFunctions.RHTower.RouteEGibbsRapidity

/-! # Elementary prime sums controlling reflected heat overlaps -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset Real
open scoped Topology

/-- Total elementary mass for a convergent power index. -/
def primeTotal (a : ℝ) := ∑' n : ℕ, if n.Prime then (n:ℝ)^(a-1) else 0

theorem powerMass_limit {a : ℝ} (ha : a<0) : Tendsto (powerMass a) atTop (𝓝 (primeTotal a)) := by
  have hs : Summable (fun n : ℕ => (n:ℝ)^(a-1)) := Real.summable_nat_rpow.mpr (by linarith only [ha])
  have summ : Summable (fun n : ℕ => if n.Prime then (n:ℝ)^(a-1) else 0) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro n; split_ifs <;> positivity
    · intro n; split_ifs <;> first | exact le_rfl | positivity
  have idx : Tendsto (fun x : ℝ => ⌊x⌋₊+1) atTop atTop :=
    tendsto_atTop_mono (fun x => Nat.le_succ ⌊x⌋₊) tendsto_nat_floor_atTop
  apply (summ.hasSum.tendsto_sum_nat.comp idx).congr'
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  have xp : 0≤x := by linarith only [hx]
  have sets : (range (⌊x⌋₊+1)).filter Nat.Prime = primes (cutoff x) := by
    ext p
    simp only [mem_filter,mem_range,Nat.lt_succ_iff,Nat.le_floor_iff xp,mem_cutoff hx,and_comm]
  change (∑ n ∈ range (⌊x⌋₊+1), if n.Prime then (n:ℝ)^(a-1) else 0) = _
  rw [←sum_filter,sets,powerMass]

theorem primeTotal_pos {a : ℝ} (ha : a<0) : 0<primeTotal a := by
  have low := ge_of_tendsto (powerMass_limit ha)
    ((eventually_ge_atTop (2:ℝ)).mono (fun x hx => powerMass_mono a hx))
  exact (powerMass_pos a 2).trans_le low

theorem harmonic_mass_ratio : Tendsto (fun x => powerMass 0 x / log (log x)) atTop (𝓝 1) := by
  have grow := tendsto_log_atTop.comp tendsto_log_atTop
  have h := (harmonic_mass_residual.div_atTop grow).add_const 1
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [grow.eventually_gt_atTop 0] with x hx
  change 0 < log (log x) at hx
  change (powerMass 0 x-log (log x))/log (log x)+1=_
  field_simp [hx.ne']
  exact sub_add_cancel _ _

/-- Logarithmic factors in the overlap decay rate are negligible
against every positive power of the upper label. -/
theorem log_prefactor_vanishes {d : ℝ} (hd : 0<d) :
    Tendsto (fun x : ℝ => (log (log x))^2 * log x / x^d) atTop (𝓝 0) := by
  have hi := _root_.RHTower.tendsto_logRpow_div_rpow hd (3:ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact div_nonneg (mul_nonneg (sq_nonneg _) (log_pos hx).le) (rpow_pos_of_pos (one_pos.trans hx) _).le
  · filter_upwards [tendsto_log_atTop.eventually_gt_atTop 1,eventually_gt_atTop (1:ℝ)] with x hl hx
    apply div_le_div_of_nonneg_right _ (rpow_pos_of_pos (one_pos.trans hx) _).le
    have ll := (log_le_sub_one_of_pos (one_pos.trans hl)).trans (sub_le_self _ zero_le_one)
    have ll0 := (log_pos hl).le
    have cube : (log x)^(3:ℝ) = (log x)^3 := by norm_cast
    rw [cube]
    calc
      (log (log x))^2*log x ≤ (log x)^2 * log x :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ll0 ll _) (one_pos.trans hl).le
      _ = _ := by ring

theorem powerMass_index_mono {a b : ℝ} (h : a≤b) (x : ℝ) : powerMass a x ≤ powerMass b x := by
  apply sum_le_sum
  intro p hp
  have prime := (Nat.mem_primesBelow.mp hp).2
  exact rpow_le_rpow_of_exponent_le (by exact_mod_cast prime.one_lt.le) (sub_le_sub_right h 1)

#print axioms powerMass_limit
#print axioms primeTotal_pos
#print axioms harmonic_mass_ratio
#print axioms log_prefactor_vanishes
#print axioms powerMass_index_mono

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
