import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum

/-! # A linear lower bound for the order of an exponentially large response basis -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.NecessaryOrder
noncomputable section

/-- Isolate one positive term in the binomial expansion at 1/128. -/
private theorem choose_le_exp (M L : ℕ) (h : L ≤ M) :
    (M.choose L:ℝ)≤(2:ℝ)^(7*L)*Real.exp ((M:ℝ)/128) := by
  let r : ℝ := 1/128
  have hr : 0≤r := by norm_num [r]
  have hterm : r^L*(M.choose L:ℝ)≤(r+1)^M := by
    rw [add_pow]
    simpa only [one_pow,mul_one] using (Finset.single_le_sum
      (f:=fun i => r^i*(1:ℝ)^(M-i)*(M.choose i:ℝ)) (fun i _ => by positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
  have he : (r+1)^M≤Real.exp ((M:ℝ)/128) := by
    calc _ ≤ (Real.exp r)^M := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp r) _
         _ = _ := by rw [←Real.exp_nat_mul]; congr 1; dsimp only [r]; ring
  have hc : (2:ℝ)^(7*L)*r^L=1 := by rw [pow_mul,←mul_pow]; norm_num [r]
  calc _ = (2:ℝ)^(7*L)*(r^L*(M.choose L:ℝ)) := by rw [←mul_assoc,hc,one_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_left (hterm.trans he) (by positivity)

/-- With at most 12 coordinates per spin, all multisets of order at most N/9
together supply at most half the required rows once N≥54. -/
theorem choose_le_half_dimension {n m L : ℕ} (hn : 53≤n) (hm : m≤12*(n+1)) (hL : 9*L≤n+1) :
    (m+L).choose L≤2^n := by
  have hm' : (m:ℝ)≤12*((n:ℝ)+1) := by exact_mod_cast hm
  have hL' : 9*(L:ℝ)≤(n:ℝ)+1 := by exact_mod_cast hL
  have hn' : (53:ℝ)≤n := by exact_mod_cast hn
  have hgap : 0≤(n:ℝ)-7*L := by linarith only [hL',hn']
  have hl : (1/2:ℝ)≤Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : 0<(2:ℝ))
    norm_num at h ⊢
    exact h
  have hprice : (7*(L:ℝ))*Real.log 2+((m:ℝ)+L)/128≤(n:ℝ)*Real.log 2 := by
    linarith only [mul_le_mul_of_nonneg_left hl hgap,hL',hm',hn']
  have hlog (a : ℕ) : Real.exp ((a:ℝ)*Real.log 2)=(2:ℝ)^a := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have h := choose_le_exp (m+L) L (Nat.le_add_left _ _)
  have he : (2:ℝ)^(7*L)*Real.exp (((m+L:ℕ):ℝ)/128)≤(2:ℝ)^n := by
    rw [←hlog (7*L),←Real.exp_add,←hlog n,Real.exp_le_exp]
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add] using hprice
  exact_mod_cast h.trans he

#print axioms choose_le_half_dimension
end
end GaloisForLFunctions.HTGeometry.SpectralJets.NecessaryOrder
