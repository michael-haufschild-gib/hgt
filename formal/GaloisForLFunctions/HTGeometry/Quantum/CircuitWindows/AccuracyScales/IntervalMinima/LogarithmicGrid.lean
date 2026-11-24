import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Finite multiplicative mesh for doubly exponential waiting times -/

open Real Filter Set
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
noncomputable section

/-- At mesh index i the duration plus one equals exp(i/Dᵇ). Including
one keeps the same mesh valid for crossings with zero waiting time. -/
def logMesh (N b i : ℕ) : ℝ := exp ((i:ℝ)/(2:ℝ)^(b*N))-1

/-- An exponential number of endpoints rounds every wait up to the
double-exponential deadline with logarithmic excess at most D⁻ᵇ. -/
theorem round_wait {N : ℕ} (hN : 1 ≤ N) (C b : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hcap : x ≤ (2:ℝ)^((2^N)^C : ℕ)) :
    ∃ i < 2^((C+b+2)*N), x ≤ logMesh N b i ∧
      1+logMesh N b i ≤ (1+x)*exp (1/(2:ℝ)^(b*N)) := by
  let d : ℕ := (2^N)^C
  let M := (2:ℝ)^(b*N)
  let y := log (1+x)*M
  let i := ⌈y⌉₊
  have hM : 0 < M := by dsimp only [M]; positivity
  have hpos : 0 < 1+x := by linarith only [hx]
  have hy : 0 ≤ y := mul_nonneg (log_nonneg (by linarith only [hx])) hM.le
  have hi : y ≤ (i:ℝ) := Nat.le_ceil y
  have hi' : (i:ℝ) < y+1 := Nat.ceil_lt_add_one hy
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by dsimp only [d]; positivity)
  have hbig : 1 ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
  have harg : 1+x ≤ 2*(2:ℝ)^d := by change x ≤ (2:ℝ)^d at hcap; linarith only [hcap,hbig]
  have hlog := log_le_log hpos harg
  rw [log_mul (by norm_num) (by positivity),log_pow] at hlog
  have hlog₂ := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hdl : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hL : log (1+x) ≤ 2*(d:ℝ) := by
    linarith only [hlog,hlog₂,mul_le_mul_of_nonneg_left hlog₂ (Nat.cast_nonneg (α:=ℝ) d),hdl]
  have hprod : (d:ℝ)*M = (2:ℝ)^((C+b)*N) := by
    simp only [d,M,Nat.cast_pow,Nat.cast_ofNat,←pow_mul,←pow_add]
    congr 1
    ring
  have hh : (1:ℝ) ≤ (2:ℝ)^((C+b)*N) := one_le_pow₀ (by norm_num)
  have hidx : i < 2^((C+b+2)*N) := by
    have h := mul_le_mul_of_nonneg_right hL hM.le
    change y ≤ 2*(d:ℝ)*M at h
    rw [mul_assoc,hprod] at h
    have h' : (i:ℝ) < 4*(2:ℝ)^((C+b)*N) := by linarith only [hi',h,hh]
    have ht : 2+((C+b)*N) ≤ (C+b+2)*N := by rw [Nat.add_mul (C+b) 2 N]; omega
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) ht
    rw [pow_add,show (2:ℝ)^2=4 by norm_num] at hp
    exact_mod_cast h'.trans_le hp
  refine ⟨i,hidx,?_,?_⟩
  · have h₁ : log (1+x) ≤ (i:ℝ)/M := (le_div_iff₀ hM).mpr hi
    have h := exp_le_exp.mpr h₁
    rw [exp_log hpos] at h
    change x ≤ exp ((i:ℝ)/M)-1
    linarith only [h]
  · have h₁ : (i:ℝ)/M ≤ log (1+x)+1/M := (div_le_iff₀ hM).mpr (by
      rw [add_mul,div_mul_cancel₀ _ hM.ne']; exact hi'.le)
    have h := exp_le_exp.mpr h₁
    rw [exp_add,exp_log hpos] at h
    change 1+(exp ((i:ℝ)/M)-1) ≤ _
    linarith only [h]

#print axioms round_wait
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
