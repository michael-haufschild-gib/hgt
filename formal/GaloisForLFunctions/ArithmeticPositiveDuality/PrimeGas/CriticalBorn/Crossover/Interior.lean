import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Quadrature
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.LogEnergy

/-! # Uniformly negligible heat tilts below an interior logarithmic-energy threshold -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover

open Finset Filter Real
open scoped Topology

/-- A tilt acts on the harmonic prime weights by a factor bounded
between the two extreme exponential tilts of the packet. -/
theorem finite_tilt_bounds (a : ℝ) {y : ℝ} (hy : 2≤y) :
    exp (-(|a| * log y))*powerMass 0 y ≤ powerMass a y ∧
    powerMass a y ≤ exp (|a| * log y)*powerMass 0 y := by
  have bounds (p : ℕ) (hp : p∈primes (cutoff y)) :
      exp (-(|a| * log y))*(p:ℝ)⁻¹ ≤ (p:ℝ)^(a-1) ∧
        (p:ℝ)^(a-1) ≤ exp (|a| * log y)*(p:ℝ)⁻¹ := by
    obtain ⟨pr,py⟩ := (mem_cutoff hy).mp hp
    have pp : 0<(p:ℝ) := Nat.cast_pos.mpr pr.pos
    have lp := (log_pos (show (1:ℝ)<p by exact_mod_cast pr.one_lt)).le
    have h : |log (p:ℝ)*a| ≤ |a| * log y := by
      rw [abs_mul,abs_of_nonneg lp,mul_comm]
      exact mul_le_mul_of_nonneg_left (log_le_log pp py) (abs_nonneg _)
    rw [rpow_sub pp,rpow_one,rpow_def_of_pos pp,div_eq_mul_inv]
    exact ⟨mul_le_mul_of_nonneg_right (exp_le_exp.mpr (abs_le.mp h).1) (inv_nonneg.mpr pp.le),
      mul_le_mul_of_nonneg_right (exp_le_exp.mpr (abs_le.mp h).2) (inv_nonneg.mpr pp.le)⟩
  simp only [powerMass,zero_sub,rpow_neg_one,mul_sum]
  exact ⟨sum_le_sum (fun p hp => (bounds p hp).1),sum_le_sum (fun p hp => (bounds p hp).2)⟩

/-- Any tilt whose maximal log-weight change tends to zero preserves
the harmonic mass asymptotically. -/
theorem negligible_tilt {a y : ℕ → ℝ} (hy : Tendsto y atTop atTop)
    (h : Tendsto (fun n => |a n| * log (y n)) atTop (𝓝 0)) :
    Tendsto (fun n => powerMass (a n) (y n)/powerMass 0 (y n)) atTop (𝓝 1) := by
  have lo := continuous_exp.continuousAt.tendsto.comp h.neg
  have hi := continuous_exp.continuousAt.tendsto.comp h
  rw [neg_zero,exp_zero] at lo
  rw [exp_zero] at hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo hi
  · filter_upwards [hy.eventually_ge_atTop 2] with n hn
    exact (le_div_iff₀ (powerMass_pos 0 _)).mpr (finite_tilt_bounds (a n) hn).1
  · filter_upwards [hy.eventually_ge_atTop 2] with n hn
    exact (div_le_iff₀ (powerMass_pos 0 _)).mpr (finite_tilt_bounds (a n) hn).2

def interiorCutoff (u : ℝ) (N : ℕ) := logEnergyCutoff u (log (log N))

theorem interior_growth {u : ℝ} (hu : 0<u) : Tendsto (interiorCutoff u) atTop atTop :=
  tendsto_exp_atTop.comp (tendsto_exp_atTop.comp
    ((_root_.RHTower.tendsto_const_mul_atTop_of_pos hu).comp logEnergy_growth))

private theorem tilt_size (c : ℝ) {u : ℝ} (hu : u<1) :
    Tendsto (fun n : ℕ => |drift c n/log n| * log (interiorCutoff u n)) atTop (𝓝 0) := by
  let b := 1-u
  have bp : 0<b := sub_pos.mpr hu
  have grow := (_root_.RHTower.tendsto_const_mul_atTop_of_pos bp).comp logEnergy_growth
  have fade := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp grow).div_const b
  have lim := ((displacement_small c).comp logEnergy_growth).mul fade
  rw [zero_div,mul_zero] at lim
  apply lim.congr'
  filter_upwards [logEnergy_growth.eventually_gt_atTop 0,
    ((displacement_growth c).comp logEnergy_growth).eventually_ge_atTop 0,
    eventually_ge_atTop 2] with n lpos wp n2
  let L := log (log n)
  have lN := log_pos (show (1:ℝ)<n by exact_mod_cast (by omega : 1<n))
  have idlog : log n = exp L := (exp_log lN).symm
  change displacement c L/L*((b*L)^1*exp (-(b*L))/b)=_
  change 0≤displacement c L at wp
  change 0<L at lpos
  simp only [drift,interiorCutoff,logEnergyCutoff,log_exp,abs_div,abs_of_pos lN,pow_one]
  rw [show -(b*L) = u*L-L by dsimp [b]; ring,exp_sub]
  change displacement c L/L*(b*L*(exp (u*L)/exp L)/b)=|displacement c L|/log n*exp (u*L)
  rw [abs_of_nonneg wp,idlog]
  field_simp [bp.ne',lpos.ne',(exp_pos _).ne']

theorem interior_tilts (c : ℝ) {u : ℝ} (hu : 0<u) (hu' : u<1) :
    Tendsto (fun N : ℕ => powerMass (drift c N/log N) (interiorCutoff u N)/
      powerMass 0 (interiorCutoff u N)) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => powerMass (-(drift c N)/log N) (interiorCutoff u N)/
      powerMass 0 (interiorCutoff u N)) atTop (𝓝 1) := by
  have h := tilt_size c hu'
  refine ⟨negligible_tilt (interior_growth hu) h,negligible_tilt (interior_growth hu) ?_⟩
  simpa only [neg_div,abs_neg] using h

#print axioms finite_tilt_bounds
#print axioms negligible_tilt
#print axioms interior_tilts

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover
