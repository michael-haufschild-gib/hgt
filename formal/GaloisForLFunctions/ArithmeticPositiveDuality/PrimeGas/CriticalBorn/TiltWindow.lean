import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.CutoffMass
import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence
import GaloisForLFunctions.RHTower.PrimeClockCriticalProfile
import Mathlib.Analysis.Calculus.DSlope

/-! # Finite corrections to harmonic mass in the inverse-energy window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset Real MeasureTheory
open scoped Topology Interval

/-- Exponential divided difference with its derivative value at zero. -/
def tiltKernel (w : ℝ) := dslope (fun u : ℝ => exp (w*u)) 0

private theorem kernel_continuous (w : ℝ) : Continuous (tiltKernel w) := by
  rw [←continuousOn_univ]
  exact (continuousOn_dslope Filter.univ_mem).mpr ⟨by fun_prop,by fun_prop⟩

/-- Correction to the harmonic mass for an index w/log N. -/
def tiltCorrection (w : ℝ) (N : ℕ) :=
  powerMass (w/log N) N - powerMass 0 N

private theorem prime_set {N : ℕ} (hN : 2≤N) : primes (cutoff N)=Nat.primesLE N := by
  ext p
  rw [mem_cutoff (by exact_mod_cast hN : (2:ℝ)≤N),Nat.mem_primesLE]
  simp only [Nat.cast_le]
  exact and_comm

private theorem window_eq (w : ℝ) {N : ℕ} (hN : 2≤N) :
    _root_.RHTower.mertensPrimeWindow (tiltKernel w) N / log N = tiltCorrection w N := by
  classical
  have ln := log_pos (show (1:ℝ)<N by exact_mod_cast (by omega : 1<N))
  have sets : (Icc 0 N).filter Nat.Prime = Nat.primesLE N := by
    ext p; simp only [mem_filter,mem_Icc,zero_le,true_and,Nat.mem_primesLE]
  rw [tiltCorrection,powerMass,powerMass,prime_set hN,←sum_sub_distrib,
    _root_.RHTower.mertensPrimeWindow,sum_div]
  calc
    _ = ∑ n ∈ Icc 0 N, if n.Prime then
        tiltKernel w (log n/log N)*(log n/n)/log N else 0 := by
      apply sum_congr rfl
      intro n _
      by_cases h : n.Prime <;> simp only [_root_.RHTower.mertensPrimeWeight,h,if_true,if_false,mul_zero,zero_div]
    _ = _ := by
      rw [←sum_filter,sets]
      apply sum_congr rfl
      intro p hp
      have pr := (Nat.mem_primesLE.mp hp).2
      have pp : 0<(p:ℝ) := Nat.cast_pos.mpr pr.pos
      have lp := log_pos (show (1:ℝ)<p by exact_mod_cast pr.one_lt)
      rw [tiltKernel,dslope_of_ne _ (div_ne_zero lp.ne' ln.ne'),slope_def_field,
        mul_zero,exp_zero,sub_zero,zero_sub,rpow_neg_one,Real.rpow_sub pp,rpow_one,
        rpow_def_of_pos pp]
      rw [show log (p:ℝ)*(w/log N)=w*(log p/log N) by ring]
      field_simp [lp.ne',ln.ne',pp.ne']

/-- Individual corrections on either side of the critical index converge. -/
theorem tiltCorrection_limit (w : ℝ) : Tendsto (tiltCorrection w) atTop
    (𝓝 (∫ u in (0:ℝ)..1, tiltKernel w u)) := by
  apply (_root_.RHTower.tendsto_mertensPrimeWindow_div_log (kernel_continuous w).continuousOn).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact window_eq w hN

/-- The sum of the two mass corrections is exactly the unnormalized
squared distance of the reflected prime amplitudes. -/
theorem tilt_pair_energy (c : ℝ) {N : ℕ} (hN : 2≤N) :
    tiltCorrection (2*c) N + tiltCorrection (-(2*c)) N =
      _root_.RHTower.primeClockCutoffEnergy N (c/log N) := by
  simp only [tiltCorrection,powerMass,prime_set hN,←sum_sub_distrib,←sum_add_distrib,
    _root_.RHTower.primeClockCutoffEnergy]
  apply sum_congr rfl
  intro p hp
  have pp : 0<(p:ℝ) := Nat.cast_pos.mpr (Nat.mem_primesLE.mp hp).2.pos
  let v := c/log N
  have sqr (r : ℝ) : ((p:ℝ)^r)^2 = (p:ℝ)^(r+r) := by rw [sq,rpow_add pp]
  have cross : (p:ℝ)^(-(1/2+v))*(p:ℝ)^(-(1/2-v))=(p:ℝ)^(-1:ℝ) := by
    rw [←rpow_add pp]
    congr 1
    ring
  change _ = ((p:ℝ)^(-(1/2+v))-(p:ℝ)^(-(1/2-v)))^2
  rw [sub_sq,sqr,sqr]
  have ea : -(1/2+v) + -(1/2+v) = -(2*c)/log N-1 := by dsimp [v]; ring
  have eb : -(1/2-v) + -(1/2-v) = 2*c/log N-1 := by dsimp [v]; ring
  rw [ea,eb]
  simp only [zero_sub]
  linear_combination 2*cross

#print axioms tiltCorrection_limit
#print axioms tilt_pair_energy

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
