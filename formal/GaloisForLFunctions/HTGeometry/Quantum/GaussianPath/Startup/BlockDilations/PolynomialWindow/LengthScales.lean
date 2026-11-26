import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Packet lengths for a summable grid and a polynomial physical horizon -/

open Real Filter Topology
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section

/-- The number of spatial packets lies between the real quotient and
its successor, including the last partial packet. -/
theorem packet_number {n L : ℕ} (hL : 0<L) :
    let K : ℝ := (n+2:ℕ)
    let b := (n+1)/L+1
    K/L≤(b:ℝ) ∧ (b:ℝ)≤K/L+1 ∧ (((n+2)/L+1:ℕ):ℝ)≤K/L+1 := by
  intro K b
  have hL' : (0:ℝ)<L := Nat.cast_pos.mpr hL
  have h₁ : n+2≤b*L := by
    simpa only [b,Nat.mul_comm L] using Nat.lt_mul_div_succ (n+1) hL
  refine ⟨(div_le_iff₀ hL').mpr (by exact_mod_cast h₁),?_,?_⟩
  · change (((n+1)/L+1:ℕ):ℝ)≤K/L+1
    rw [Nat.cast_add,Nat.cast_one]
    exact add_le_add (Nat.cast_div_le.trans (div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (by omega : n+1≤n+2)) hL'.le)) le_rfl
  · rw [Nat.cast_add,Nat.cast_one]
    exact add_le_add Nat.cast_div_le le_rfl

/-- Choose about M log K packets. For all large K their lengths exceed
any fixed threshold and the ratio K/L is between M log K and twice it. -/
theorem eventual_balanced_length {M : ℝ} (hM : 0<M) (L₀ q₀ : ℝ) :
    ∀ᶠ K : ℕ in atTop,
      let L := ⌊(K:ℝ)/(M*log K)⌋₊
      0<L ∧ L₀≤(L:ℝ) ∧ q₀≤(K:ℝ)/L ∧ M*log K≤(K:ℝ)/L ∧
        (K:ℝ)/L≤2*(M*log K) := by
  have ht : Tendsto (fun K : ℕ => log (K:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hq := ht.eventually (eventually_ge_atTop (q₀/M))
  have hzero : Tendsto (fun K : ℕ => log (K:ℝ)/(K:ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
    simpa [Function.comp_def] using h
  let U := max 2 (L₀+1)
  have hU : 0<U := lt_of_lt_of_le two_pos (le_max_left ..)
  have hsmall := hzero.eventually_lt_const (show 0<1/(M*U) by positivity)
  filter_upwards [hq,hsmall,eventually_gt_atTop 1] with K hk hsmall hK
  have hK' : 1<(K:ℝ) := by exact_mod_cast hK
  have hKp := zero_lt_one.trans hK'
  have hd := mul_pos hM (log_pos hK')
  let z := (K:ℝ)/(M*log K)
  have huz : U≤z := by
    apply (le_div_iff₀ hd).mpr
    have h := (div_lt_div_iff₀ hKp (mul_pos hM hU)).mp hsmall
    linarith only [h]
  have hz₂ : 2≤z := (le_max_left ..).trans huz
  have hf := Nat.lt_floor_add_one z
  have hl : z/2≤(⌊z⌋₊:ℝ) := by linarith only [hf,hz₂]
  have hlp : 0<(⌊z⌋₊:ℝ) := (by linarith only [hz₂] : 0<z/2).trans_le hl
  have hh : M*log K≤(K:ℝ)/⌊z⌋₊ := by
    apply (le_div_iff₀ hlp).mpr
    rw [mul_comm]
    exact (le_div_iff₀ hd).mp (Nat.floor_le (by linarith only [hz₂] : 0≤z))
  refine ⟨Nat.cast_pos.mp hlp,by linarith only [show L₀+1≤z from (le_max_right ..).trans huz,hf],
    (by linarith only [(div_le_iff₀ hM).mp hk] : q₀≤M*log K).trans hh,hh,?_⟩
  apply (div_le_iff₀ hlp).mpr
  have h := (div_le_iff₀ hd).mp (show z≤2*(⌊z⌋₊:ℝ) by linarith only [hl])
  linarith only [h]

#print axioms packet_number
#print axioms eventual_balanced_length
end
end GaloisForLFunctions.HTGeometry.BlockDilations
