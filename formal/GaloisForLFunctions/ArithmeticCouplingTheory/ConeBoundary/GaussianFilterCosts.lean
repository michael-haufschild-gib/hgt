import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian clock-filter cost and decay scales

Polynomial costs per factor and a fifth-power bound on the number of factors
give a sixth-power exponential interpolation cost. Seventh-power clock
amplification exceeds that cost, while an eighth-power Gaussian cutoff
suppresses the remaining tail.
-/

open Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

/-- Every fixed polynomial factor has a linear-exponential majorant on the positive ray. -/
lemma polynomial_le_exp_linear {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (k : ℕ) :
    C*x^k ≤ Real.exp ((C+(k:ℝ))*x) := by
  have hCe : C ≤ Real.exp C := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp C)
  have hxe : x ≤ Real.exp x := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp x)
  calc
    C*x^k ≤ Real.exp C*(Real.exp x)^k := mul_le_mul hCe
      (pow_le_pow_left₀ (zero_le_one.trans hx) hxe k) (pow_nonneg (zero_le_one.trans hx) k)
      (Real.exp_pos C).le
    _ = Real.exp (C+(k:ℝ)*x) := by rw [← Real.exp_nat_mul,← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hx hC])

/-- At most `C x^5` normalized factors, each of cost `exp(Ax)`, cost `exp(ACx^6)` in total. -/
lemma gaussian_clock_product_cost {A C x : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x)
    {k : ℕ} (hk : (k:ℝ) ≤ C*x^5) :
    (Real.exp (A*x))^k ≤ Real.exp (A*C*x^6) := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hk (mul_nonneg hA hx)
  nlinarith only [hh]

/-- Seventh-power amplification dominates the sixth-power interpolation cost. -/
lemma tendsto_exp_six_sub_seven (C : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.exp (C*x^6-a*x^7)) atTop (nhds 0) := by
  have hbound : ∀ᶠ x : ℝ in atTop, C*x^6-a*x^7 ≤ -x := by
    filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop ((|C|+1)/a)] with x hx1 hxA
    have hx0 : 0 ≤ x := zero_le_one.trans hx1
    have hcoef : |C|+1 ≤ a*x := by
      have hh := (div_le_iff₀ ha).mp hxA
      simpa only [mul_comm] using hh
    have hm := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hx0 6)
    have hC := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hx0 6)
    have hpow : x ≤ x^6 := le_self_pow₀ hx1 (by norm_num)
    nlinarith only [hm,hC,hpow]
  have ht : Tendsto (fun x : ℝ => C*x^6-a*x^7) atTop atBot :=
    tendsto_atBot_mono' atTop hbound tendsto_neg_atTop_atBot
  exact Real.tendsto_exp_atBot.comp ht

/-- The Gaussian eighth-power cutoff dominates both interpolation and clock amplification. -/
lemma tendsto_exp_six_seven_sub_eight (C b : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun x : ℝ => Real.exp (C*x^6+b*x^7-τ*x^8)) atTop (nhds 0) := by
  have hbound : ∀ᶠ x : ℝ in atTop, C*x^6+b*x^7-τ*x^8 ≤ -x := by
    filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop ((|C|+|b|+1)/τ)] with x hx1 hxT
    have hx0 : 0 ≤ x := zero_le_one.trans hx1
    have hcoef : |C|+|b|+1 ≤ τ*x := by
      have hh := (div_le_iff₀ hτ).mp hxT
      simpa only [mul_comm] using hh
    have h67 : x^6 ≤ x^7 := pow_le_pow_right₀ hx1 (by norm_num)
    have hC : C*x^6 ≤ |C| *x^7 :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hx0 6)).trans
        (mul_le_mul_of_nonneg_left h67 (abs_nonneg C))
    have hb := mul_le_mul_of_nonneg_right (le_abs_self b) (pow_nonneg hx0 7)
    have hm := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hx0 7)
    have hpow : x ≤ x^7 := le_self_pow₀ hx1 (by norm_num)
    nlinarith only [hC,hb,hm,hpow]
  have ht : Tendsto (fun x : ℝ => C*x^6+b*x^7-τ*x^8) atTop atBot :=
    tendsto_atBot_mono' atTop hbound tendsto_neg_atTop_atBot
  exact Real.tendsto_exp_atBot.comp ht

#print axioms polynomial_le_exp_linear
#print axioms tendsto_exp_six_sub_seven
#print axioms tendsto_exp_six_seven_sub_eight
#print axioms gaussian_clock_product_cost
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
