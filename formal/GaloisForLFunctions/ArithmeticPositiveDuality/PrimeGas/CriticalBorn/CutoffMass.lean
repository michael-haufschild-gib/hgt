import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Fourier
import GaloisForLFunctions.RHTower.PrimeRpowSumAsymptotic
import GaloisForLFunctions.RHTower.RVCumulantAverage
import GaloisForLFunctions.RHTower.PrimeKaramataShell

/-! # Scale ratios of finite elementary power masses -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Real Filter Finset
open scoped Topology

/-- Index of the elementary packet cut off at the real energy label x.
The shell 2 is retained at every index. -/
def cutoff (x : ℝ) := ⌊x⌋₊ - 2

def powerMass (a x : ℝ) := ∑ p ∈ primes (cutoff x), (p : ℝ)^(a-1)

theorem powerMass_pos (a x : ℝ) : 0 < powerMass a x := by
  apply sum_pos' (fun p _ => rpow_nonneg (Nat.cast_nonneg p) _)
  exact ⟨2,Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩,rpow_pos_of_pos (by norm_num) _⟩

theorem mem_cutoff {p : ℕ} {x : ℝ} (hx : 2 ≤ x) :
    p ∈ primes (cutoff x) ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  have h₂ : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith only [hx] : 0≤x)).2 (by exact_mod_cast hx)
  rw [primes,Nat.mem_primesBelow,←Nat.le_floor_iff (by linarith only [hx] : 0≤x)]
  unfold cutoff
  constructor
  · rintro ⟨h,hp⟩; exact ⟨hp,by omega⟩
  · rintro ⟨hp,h⟩; exact ⟨by omega,hp⟩

private theorem powerMass_eq (a : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    powerMass a x = (2:ℝ)^(a-1) + _root_.RHTower.primeRpowSumIoc a x := by
  classical
  let Q := (Ioc 2 ⌊x⌋₊).filter Nat.Prime
  have sets : primes (cutoff x) = insert 2 Q := by
    ext p
    simp only [mem_cutoff hx,←Nat.le_floor_iff (by linarith only [hx] : 0≤x),mem_insert,Q,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨hp,h⟩
      by_cases h₂ : p = 2
      · exact Or.inl h₂
      · exact Or.inr ⟨⟨by have := hp.two_le; omega,h⟩,hp⟩
    · rintro (rfl | ⟨⟨_,h⟩,hp⟩)
      · exact ⟨Nat.prime_two,(Nat.le_floor_iff (by linarith only [hx] : 0≤x)).2 (by exact_mod_cast hx)⟩
      · exact ⟨hp,h⟩
  have absent : 2 ∉ Q := by simp [Q]
  rw [powerMass,sets,sum_insert absent,_root_.RHTower.primeRpowSumIoc,←sum_filter]
  norm_cast

/-- Adding back the elementary shell 2 leaves the real prime-sum
asymptotic unchanged. -/
theorem powerMass_asymptotic {a : ℝ} (ha : 0<a) (ha' : a<1) :
    Tendsto (fun x : ℝ => powerMass a x*(a*log x)/x^a) atTop (𝓝 1) := by
  have tiny := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have h := (tiny.const_mul ((2:ℝ)^(a-1)*a)).add (_root_.RHTower.tendsto_primeRpowSumIoc ha ha')
  rw [mul_zero,zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  rw [powerMass_eq a hx]
  ring

/-- A fixed fractional subinterval of the energy labels carries a
nonzero limiting fraction of the elementary mass. -/
theorem powerMass_ratio {a c : ℝ} (ha : 0<a) (ha' : a<1) (hc : 0<c) :
    Tendsto (fun x : ℝ => powerMass a (c*x)/powerMass a x) atTop (𝓝 (c^a)) := by
  have hcX := _root_.RHTower.tendsto_const_mul_atTop_of_pos hc
  have h := powerMass_asymptotic ha ha'
  have ratio := ((h.comp hcX).div h one_ne_zero).mul (_root_.RHTower.tendsto_log_shift_ratio (log c))
  have scaled := ratio.const_mul (c^a)
  rw [div_one,one_mul,mul_one] at scaled
  apply scaled.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),hcX.eventually_gt_atTop 1] with x hx hcx
  change c^a * ((powerMass a (c*x)*(a*log (c*x))/(c*x)^a /
    (powerMass a x*(a*log x)/x^a))*(log x/(log x+log c))) = _
  have xp := one_pos.trans hx
  have lp := (log_pos hx).ne'
  have lc := (log_pos hcx).ne'
  rw [log_mul hc.ne' xp.ne',mul_rpow hc.le xp.le]
  rw [log_mul hc.ne' xp.ne'] at lc
  rw [add_comm (log x) (log c)]
  field_simp [(powerMass_pos a x).ne',ha.ne',lp,lc,(rpow_pos_of_pos hc a).ne',(rpow_pos_of_pos xp a).ne']

#print axioms powerMass_pos
#print axioms mem_cutoff
#print axioms powerMass_asymptotic
#print axioms powerMass_ratio

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
