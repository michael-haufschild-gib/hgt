import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Dilution
import GaloisForLFunctions.HTGeometry.SphericalPatchTube

/-! # Hilbert distance between ordinary and multiplied prime states -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary

open Finset Filter Real Crossover
open GaloisForLFunctions.HTGeometry
open scoped Topology

/-- Ordinary wave with its amplitude scaled by the square root of the maximal fiber size. -/
def restored (m : ℕ) (s : ℂ) (x : ℝ) := sqrt (m.factorial:ℝ) • wave m s x

private theorem root_gap {M K : ℝ} (hM : 0≤M) (h : M≤K) :
    (sqrt K-sqrt M)^2 ≤ K-M := by
  have hprod := mul_le_mul_of_nonneg_right (sqrt_le_sqrt h) (sqrt_nonneg M)
  nlinarith only [hprod,sq_sqrt hM,sq_sqrt (hM.trans h)]

private theorem gap_on {m : ℕ} {x : ℝ} (s : ℂ) {n : ℕ+} (hn : n∈shells m x) :
    ‖(restored m s x-Composite.wave m s x) n‖^2 ≤
      ((m.factorial:ℝ)-multiplicity m x n)*exp (((1-2*s.re)-1)*energy n) := by
  change ‖(sqrt (m.factorial:ℝ)) • wave m s x n-Composite.wave m s x n‖^2 ≤ _
  rw [wave_apply,if_pos hn,Composite.wave_apply,Complex.real_smul,←sub_mul,←Complex.ofReal_sub,
    norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,heat_square]
  exact mul_le_mul_of_nonneg_right (root_gap (Nat.cast_nonneg _)
    (by exact_mod_cast (multiplicity_bounds hn).2)) (exp_pos _).le

private theorem gap_off {m : ℕ} {x : ℝ} (s : ℂ) {n : ℕ+} (hn : n∉shells m x) :
    ‖(restored m s x-Composite.wave m s x) n‖^2=0 := by
  have hm : multiplicity m x n=0 := by
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro q hq e
    exact hn (e ▸ mem_image_of_mem productLabel hq)
  change ‖(sqrt (m.factorial:ℝ)) • wave m s x n-Composite.wave m s x n‖^2=0
  rw [wave_apply,if_neg hn,Composite.wave_apply,hm]
  simp

/-- The discrepancy between the two physical vectors is bounded by the
excess in total occupation mass, uniformly in the imaginary heat time. -/
theorem restored_distance (m : ℕ) (s : ℂ) (x : ℝ) :
    ‖restored m s x-Composite.wave m s x‖^2 ≤
      (m.factorial:ℝ)*mass m (1-2*s.re) x-(powerMass (1-2*s.re) x)^m := by
  rw [lp_norm_sq_eq_tsum,tsum_eq_sum (s := shells m x) (fun _ hn => gap_off s hn)]
  calc
    _ ≤ ∑ n ∈ shells m x, ((m.factorial:ℝ)-multiplicity m x n)*exp (((1-2*s.re)-1)*energy n) :=
      sum_le_sum fun _ hn => gap_on s hn
    _ = _ := by
      rw [←weighted_total m (1-2*s.re) x,mass,mul_sum,←sum_sub_distrib]
      exact sum_congr rfl fun _ _ => sub_mul _ _ _

/-- Normalize a gas wave by its Hilbert norm. -/
def unitWave (u : Gas) := ‖u‖⁻¹ • u

private theorem ordinary_ne (m : ℕ) (s : ℂ) (x : ℝ) : wave m s x≠0 := by
  intro h
  have z := wave_mass m s x
  rw [h,norm_zero,zero_pow (by norm_num : 2≠0)] at z
  exact (mass_pos _ _ _).ne' z.symm

private theorem comp_ne (m : ℕ) (s : ℂ) (x : ℝ) : Composite.wave m s x≠0 := by
  intro h
  have z := Composite.wave_mass m s x
  rw [h,norm_zero,zero_pow (by norm_num : 2≠0),rawWave_sq] at z
  exact (pow_pos (powerMass_pos _ _) m).ne' z.symm

private theorem normalize_restored (m : ℕ) (s : ℂ) (x : ℝ) :
    unitWave (restored m s x)=unitWave (wave m s x) := by
  have hp : 0<sqrt (m.factorial:ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos m))
  rw [unitWave,restored,norm_smul,Real.norm_of_nonneg hp.le,smul_smul,unitWave,mul_inv_rev,mul_assoc,
    inv_mul_cancel₀ hp.ne',mul_one]

/-- Quantitative Hilbert comparison for every finite prime set in the cutoff family. -/
theorem unit_distance_le (m : ℕ) (s : ℂ) (x : ℝ) :
    ‖unitWave (Composite.wave m s x)-unitWave (wave m s x)‖ ≤ 2*sqrt (excess m (1-2*s.re) x) := by
  have hp : 0<sqrt (m.factorial:ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos m))
  have hr : restored m s x ≠ 0 := smul_ne_zero hp.ne' (ordinary_ne m s x)
  have scaled : ‖restored m s x-Composite.wave m s x‖/‖Composite.wave m s x‖ ≤
      sqrt (excess m (1-2*s.re) x) := by
    apply le_sqrt_of_sq_le
    rw [div_pow,Composite.wave_mass,rawWave_sq]
    refine (div_le_div_of_nonneg_right (restored_distance m s x) (pow_pos (powerMass_pos _ _) m).le).trans_eq ?_
    rw [sub_div,div_self (pow_pos (powerMass_pos _ _) m).ne',excess]
  rw [←normalize_restored m s x]
  calc
    _ ≤ 2*‖Composite.wave m s x-restored m s x‖/‖Composite.wave m s x‖ :=
      norm_normalize_sub_normalize_le (comp_ne m s x) hr
    _ ≤ _ := by rw [norm_sub_rev,mul_div_assoc]; exact mul_le_mul_of_nonneg_left scaled (by norm_num)

/-- Ordinary occupation states and coherently multiplied states approach
one another in Hilbert norm through the window, for arbitrary clock times. -/
theorem unit_distance_limit (m : ℕ) (c : ℝ) (t : ℕ → ℝ) :
    Tendsto (fun N : ℕ => let s := indexParameter (drift c N/log N) (t N)
      ‖unitWave (Composite.wave m s N)-unitWave (wave m s N)‖) atTop (𝓝 0) := by
  have upper := (Real.continuous_sqrt.continuousAt.tendsto.comp (excess_limit m c)).const_mul 2
  rw [sqrt_zero,mul_zero] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds upper (fun _ => norm_nonneg _) _
  intro N
  let a := drift c N/log N
  have idx : 1-2*(indexParameter a (t N)).re=a := by simp [indexParameter]; ring
  change ‖unitWave (Composite.wave m (indexParameter a (t N)) N)-
    unitWave (wave m (indexParameter a (t N)) N)‖ ≤ 2*sqrt (excess m a N)
  simpa only [idx] using unit_distance_le m (indexParameter a (t N)) N

#print axioms restored_distance
#print axioms unit_distance_le
#print axioms unit_distance_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary
