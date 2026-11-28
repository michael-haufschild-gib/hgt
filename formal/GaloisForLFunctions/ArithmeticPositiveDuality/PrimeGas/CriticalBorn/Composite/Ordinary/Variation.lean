import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Defect

/-! # Total variation on actual product labels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary

open Finset Real

/-- Ordinary and ordered Born probabilities on a reachable product label. -/
def plainWeight (m : ℕ) (a x : ℝ) (n : ℕ+) := exp ((a-1)*energy n)/mass m a x

def orderedWeight (m : ℕ) (a x : ℝ) (n : ℕ+) :=
  (multiplicity m x n:ℝ)*exp ((a-1)*energy n)/(powerMass a x)^m

theorem plainWeight_sum (m : ℕ) (a x : ℝ) : ∑ n ∈ shells m x, plainWeight m a x n=1 := by
  simp only [plainWeight,←sum_div]
  exact div_self (mass_pos m a x).ne'

theorem orderedWeight_sum (m : ℕ) (a x : ℝ) : ∑ n ∈ shells m x, orderedWeight m a x n=1 := by
  simp only [orderedWeight,←sum_div,weighted_total,div_self (pow_pos (powerMass_pos a x) m).ne']

private theorem ordered_nonneg (m : ℕ) (a x : ℝ) (n : ℕ+) : 0 ≤ orderedWeight m a x n :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (exp_pos _).le) (pow_pos (powerMass_pos a x) m).le

private theorem dominate {m : ℕ} (a x : ℝ) {n : ℕ+} (hn : n∈shells m x) :
    orderedWeight m a x n/(1+excess m a x) ≤ plainWeight m a x n := by
  have p := (pow_pos (powerMass_pos a x) m).ne'
  have K : 0<(m.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have ratio : 1+excess m a x=(m.factorial:ℝ)*mass m a x/(powerMass a x)^m := by
    unfold excess
    ring
  rw [ratio,orderedWeight,plainWeight,div_div_div_cancel_right₀ p]
  apply (div_le_div_iff₀ (mul_pos K (mass_pos m a x)) (mass_pos m a x)).mpr
  have h := mul_le_mul_of_nonneg_right (show (multiplicity m x n:ℝ) ≤ m.factorial by
    exact_mod_cast (multiplicity_bounds hn).2) (mul_nonneg (exp_pos ((a-1)*energy n)).le (mass_pos m a x).le)
  linarith only [h]

/-- Twice the total variation is bounded by the missing common mass
on the two integer-label laws, including a sector with zero excess. -/
theorem variation_le (m : ℕ) (a x : ℝ) :
    ∑ n ∈ shells m x, |plainWeight m a x n-orderedWeight m a x n| ≤
      2*(excess m a x/(1+excess m a x)) := by
  let e := excess m a x
  let R := 1+e
  let P := plainWeight m a x
  let Q := orderedWeight m a x
  have ep : 0≤e := excess_nonneg m a x
  have rp : 0<R := by dsimp [R]; positivity
  have rem : 1-1/R=e/R := by field_simp [rp.ne']; dsimp [R]; ring
  have point (n : ℕ+) (hn : n∈shells m x) :
      |P n-Q n| ≤ (P n-Q n/R)+(Q n-Q n/R) := by
    have hp : 0≤P n-Q n/R := sub_nonneg.mpr (dominate a x hn)
    have hq : 0≤Q n-Q n/R := sub_nonneg.mpr (div_le_self (ordered_nonneg m a x n) (by dsimp [R]; linarith))
    rw [show P n-Q n=(P n-Q n/R)-(Q n-Q n/R) by ring]
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hp,abs_of_nonneg hq])
  refine (sum_le_sum point).trans_eq ?_
  simp only [sum_add_distrib,sum_sub_distrib,←sum_div,P,Q,plainWeight_sum,orderedWeight_sum,rem]
  ring

/-- Every bounded diagonal measurement inherits the same comparison,
uniformly over choices of the observable at each cutoff. -/
theorem test_difference (m : ℕ) (a x : ℝ) (f : ℕ+ → ℝ) {B : ℝ}
    (hB : 0≤B) (hf : ∀ n ∈ shells m x, |f n|≤B) :
    |(∑ n ∈ shells m x, plainWeight m a x n*f n)-
      ∑ n ∈ shells m x, orderedWeight m a x n*f n| ≤
      B*(2*(excess m a x/(1+excess m a x))) := by
  rw [←sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ n ∈ shells m x, B*|plainWeight m a x n-orderedWeight m a x n| := by
      refine sum_le_sum fun n hn => ?_
      rw [←sub_mul,abs_mul,mul_comm]
      exact mul_le_mul_of_nonneg_right (hf n hn) (abs_nonneg _)
    _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (variation_le m a x) hB

#print axioms variation_le
#print axioms test_difference

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary
