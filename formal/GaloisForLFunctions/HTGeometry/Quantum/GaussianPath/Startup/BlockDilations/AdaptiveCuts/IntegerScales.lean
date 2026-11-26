import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Integer packet scales for weak bonds on superlinear time windows -/

open Real Filter
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section

/-- An integer within a factor of two of the sixty-fourth root. -/
def sizeRoot (K : ℕ) := Nat.nthRoot 64 K

theorem root_bounds {K : ℕ} (hK : 0<K) :
    1≤sizeRoot K ∧ sizeRoot K^64≤K ∧ K≤(2*sizeRoot K)^64 := by
  have hp : 1≤sizeRoot K := (Nat.le_nthRoot_iff (by decide : 64≠0)).mpr (by simpa using hK)
  have hh := Nat.lt_pow_nthRoot_add_one (by decide : 64≠0) K
  exact ⟨hp,Nat.pow_nthRoot_le_iff.mpr (Or.inl (by decide)),hh.le.trans
    (Nat.pow_le_pow_left (by change sizeRoot K+1≤2*sizeRoot K; omega) _)⟩

theorem sizeRoot_tendsto : Tendsto sizeRoot atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  exact (eventually_ge_atTop (j^64)).mono fun _ => (Nat.le_nthRoot_iff (by decide : 64≠0)).mpr

/-- Logarithms of system size are bounded by a linear function of the
root. Thus every fixed power of K is paid for by exp(c q²). -/
theorem log_size_le {K : ℕ} (hK : 0<K) :
    log (K:ℝ)≤128*(sizeRoot K:ℝ) := by
  obtain ⟨hq,_,hhi⟩ := root_bounds hK
  have hq' : (0:ℝ)<sizeRoot K := Nat.cast_pos.mpr hq
  have h := Real.log_le_log (Nat.cast_pos.mpr hK) (Nat.cast_le.mpr hhi)
  rw [Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Real.log_pow] at h
  have hp := Real.log_le_sub_one_of_pos (mul_pos two_pos hq')
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h,hp]

theorem log_root_eventually {a : ℝ} (ha : 0<a) (b c : ℝ) :
    ∀ᶠ K : ℕ in atTop, b*log (K:ℝ)+c≤a*(sizeRoot K:ℝ)^2 := by
  let d := 128*|b|+|c|
  have hd : 0≤d := by dsimp only [d]; positivity
  have ht := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp sizeRoot_tendsto
  filter_upwards [eventually_gt_atTop 0,ht.eventually (eventually_ge_atTop (d/a))] with K hK hq
  let q : ℝ := sizeRoot K
  have hq₁ : 1≤q := by exact_mod_cast (root_bounds hK).1
  have hl := log_nonneg (show 1≤(K:ℝ) by exact_mod_cast hK)
  have h₁ := mul_le_mul (le_abs_self b) (log_size_le hK) hl (abs_nonneg b)
  have h₂ := (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) hq₁)
  have h₃ := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).mp hq) (zero_le_one.trans hq₁)
  change d*q≤q*a*q at h₃
  dsimp only [d] at h₃
  change b*log (K:ℝ)≤|b|*(128*q) at h₁
  nlinarith only [h₁,h₂,h₃]

/-- A buffer contains q⁶² candidate bonds; the number of buffers is
of order q² for every system size, including incomplete final buffers. -/
theorem packet_quotient {K : ℕ} (hK : 0<K) :
    let q : ℝ := sizeRoot K
    let L := 3*q^62
    q^2/3≤K/L ∧ (K:ℝ)/L≤(2:ℝ)^64*q^2/3 := by
  intro q L
  obtain ⟨hpos,hlo,hhi⟩ := root_bounds hK
  have hq : 0<q := Nat.cast_pos.mpr hpos
  have hL : 0<L := by dsimp only [L]; positivity
  have h₁ : q^64≤(K:ℝ) := by exact_mod_cast hlo
  have h₂ : (K:ℝ)≤(2*q)^64 := by exact_mod_cast hhi
  constructor
  · apply (le_div_iff₀ hL).mpr
    convert h₁ using 1 <;> dsimp only [L] <;> ring
  · apply (div_le_iff₀ hL).mpr
    apply h₂.trans_eq
    dsimp only [L]; ring

#print axioms root_bounds
#print axioms log_root_eventually
#print axioms packet_quotient
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
