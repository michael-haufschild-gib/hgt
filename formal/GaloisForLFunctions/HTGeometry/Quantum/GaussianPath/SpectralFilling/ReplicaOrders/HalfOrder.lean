import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PositiveDensityBudget
import Mathlib.Data.Nat.Factorial.BigOperators

/-! # Entropy available at half the Hilbert dimension in replica order -/
open Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section

/-- Grouping the first and last h factors gains a factor 8⁻ʰ
for the uniform moment of order 2h on 4h levels. -/
private theorem factorial_ratio (h : ℕ) (hh : 0 < h) :
    ((2*h).factorial:ℝ)/((4*h:ℕ):ℝ)^(2*h) ≤ (1/8:ℝ)^h := by
  have hf : (2*h).factorial ≤ h^h*(2*h)^h := by
    rw [two_mul,←Nat.factorial_mul_ascFactorial]
    exact Nat.mul_le_mul (Nat.factorial_le_pow h) (Nat.ascFactorial_le_pow_add h h)
  have hf' : ((2*h).factorial:ℝ) ≤ (h:ℝ)^h*(2*(h:ℝ))^h := by exact_mod_cast hf
  push_cast
  apply (div_le_iff₀ (by positivity)).mpr
  apply hf'.trans_eq
  rw [pow_mul,←mul_pow,←mul_pow]
  congr 1
  ring

/-- At trace threshold 7/8 the finite-time moment correction fits beneath
the circuit-net entropy once T times the replica gap reaches 4√h. -/
theorem half_order_price (h : ℕ) (hh : 4 ≤ h) {T γ : ℝ}
    (hγ : 0 < γ) (hT : 4*√(h:ℝ)/γ ≤ T) :
    let D := 4*h
    let q := 2*h
    8*(((q.factorial:ℝ)/(D:ℝ)^q)+exp (-(T*γ)^2/2))/(7/8:ℝ)^(2*q) ≤
      zeroGateArcDensity D (7/10) := by
  intro D q
  have ht := (div_le_iff₀ hγ).mp hT
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 4*√(h:ℝ)) ht 2
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg h)] at hs
  have hl := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)) (Nat.cast_nonneg h)
  have hm : exp (-(T*γ)^2/2) ≤ (1/8:ℝ)^h := by
    calc _ ≤ exp (-((h:ℝ)*log 8)) := exp_le_exp.mpr (by linarith only [hs,hl,Nat.cast_nonneg h])
         _ = _ := by rw [exp_neg,exp_nat_mul,exp_log (by norm_num),one_div,inv_pow]
  have h₁ := add_le_add (factorial_ratio h (by omega)) hm
  have hprice : 8*(((q.factorial:ℝ)/(D:ℝ)^q)+exp (-(T*γ)^2/2))/(7/8:ℝ)^(2*q)
      ≤ 16*((1/8:ℝ)/(7/8:ℝ)^4)^h := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ (by norm_num : (0:ℝ) ≤ 8))
      (by positivity : 0 ≤ (7/8:ℝ)^(2*q))).trans_eq
    rw [show 2*q=4*h by dsimp only [q]; omega,pow_mul,div_pow]
    ring
  apply hprice.trans
  have hrat := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ (1/8)/(7/8)^4)
    (by norm_num : (1/8:ℝ)/(7/8)^4 ≤ (7/10)^4) h
  rw [←pow_mul] at hrat
  have hpow := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 7/10) (by norm_num)
    (Nat.sub_le D 1)
  exact mul_le_mul (by exact_mod_cast (by dsimp only [D]; omega : 16 ≤ D)) (hrat.trans hpow)
    (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)

#print axioms half_order_price
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
