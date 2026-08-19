import GaloisForLFunctions.RHTower.Sieve.RouteTThresholdLimits

/-!
# The Granville–Soundararajan schedule

The cutoff and the tolerance of the tail estimate, with the elementary facts the assembly needs:
the cutoff is above `exp((log z)^{0.99})`, below `z`, at least two, and every block top above it has
`log i ≥ (log z)^{0.99}`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The Granville–Soundararajan cutoff of the schedule. -/
def gsCutoff (z : ℕ) : ℕ := ⌈Real.exp ((Real.log (z : ℝ)) ^ (0.99 : ℝ))⌉₊

/-- The tolerance of the schedule. -/
def gsRho (z : ℕ) : ℝ := 1 / (9 * (2 + Real.log (z : ℝ)))

theorem log_tendsto_atTop_nat : Tendsto (fun z : ℕ => Real.log (z : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem exp_le_gsCutoff (z : ℕ) :
    Real.exp ((Real.log (z : ℝ)) ^ (0.99 : ℝ)) ≤ ((gsCutoff z : ℕ) : ℝ) :=
  Nat.le_ceil _

theorem two_le_gsCutoff {z : ℕ} (hz : 0 < Real.log (z : ℝ)) : 2 ≤ gsCutoff z := by
  have hpow : (0 : ℝ) < (Real.log (z : ℝ)) ^ (0.99 : ℝ) := Real.rpow_pos_of_pos hz _
  have hlt : (1 : ℝ) < Real.exp ((Real.log (z : ℝ)) ^ (0.99 : ℝ)) := by
    have := Real.add_one_le_exp ((Real.log (z : ℝ)) ^ (0.99 : ℝ))
    linarith
  have h1 : 1 < gsCutoff z := by
    rw [gsCutoff, Nat.lt_ceil]
    exact_mod_cast hlt
  omega

theorem gsCutoff_le {z : ℕ} (hz : 1 ≤ Real.log (z : ℝ)) (hz0 : 0 < z) : gsCutoff z ≤ z := by
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz0
  have hpow : (Real.log (z : ℝ)) ^ (0.99 : ℝ) ≤ Real.log (z : ℝ) := by
    have h1 : (Real.log (z : ℝ)) ^ (0.99 : ℝ) ≤ (Real.log (z : ℝ)) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
    rwa [Real.rpow_one] at h1
  have hexp : Real.exp ((Real.log (z : ℝ)) ^ (0.99 : ℝ)) ≤ (z : ℝ) := by
    have h1 : Real.exp ((Real.log (z : ℝ)) ^ (0.99 : ℝ)) ≤ Real.exp (Real.log (z : ℝ)) :=
      Real.exp_le_exp.2 hpow
    rwa [Real.exp_log hzR] at h1
  rw [gsCutoff, Nat.ceil_le]
  exact hexp

theorem gsRho_pos {z : ℕ} (hz : 0 ≤ Real.log (z : ℝ)) : 0 < gsRho z := by
  rw [gsRho]
  have : (0 : ℝ) < 9 * (2 + Real.log (z : ℝ)) := by linarith
  positivity

theorem log_ge_of_ge_gsCutoff {z i : ℕ} (h : gsCutoff z ≤ i) :
    (Real.log (z : ℝ)) ^ (0.99 : ℝ) ≤ Real.log (i : ℝ) := by
  have hc := exp_le_gsCutoff z
  have hiR : ((gsCutoff z : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast h
  have hle : Real.exp ((Real.log (z : ℝ)) ^ (0.99 : ℝ)) ≤ (i : ℝ) := le_trans hc hiR
  have hlog := Real.log_le_log (Real.exp_pos _) hle
  rwa [Real.log_exp] at hlog

theorem nine_mul_gsRho_mul {z : ℕ} (hz : 0 ≤ Real.log (z : ℝ)) :
    9 * gsRho z * (2 + Real.log (z : ℝ)) = 1 := by
  have hne : (2 : ℝ) + Real.log (z : ℝ) ≠ 0 := by linarith
  rw [gsRho]
  field_simp

theorem one_div_gsRho {z : ℕ} (hz : 0 ≤ Real.log (z : ℝ)) :
    1 / gsRho z = 9 * (2 + Real.log (z : ℝ)) := by
  have hne : (9 : ℝ) * (2 + Real.log (z : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < 9 * (2 + Real.log (z : ℝ)) := by linarith
    linarith
  rw [gsRho, one_div_one_div]

end

end RHTower.Sieve
