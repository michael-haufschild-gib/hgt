import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Heat
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Weights

/-! # Finite exchange excess of ordinary occupation heat states -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary

open Finset Real
open ExactSubsystems.ThermalShells.Packets.Occupation
open _root_.RHTower (tupleWeight injectiveTupleWeight)

/-- Relative excess of the ordinary mass after restoring the number
of permutations on a shell with distinct primes. -/
def excess (m : ℕ) (a x : ℝ) := (m.factorial:ℝ)*mass m a x/(powerMass a x)^m-1

theorem excess_nonneg (m : ℕ) (a x : ℝ) : 0 ≤ excess m a x := by
  exact sub_nonneg.mpr ((one_le_div (pow_pos (powerMass_pos a x) m)).mpr (mass_bounds m a x).2)

theorem excess_sum (m : ℕ) (a x : ℝ) :
    excess m a x = ∑ n ∈ shells m x,
      ((m.factorial:ℝ)-multiplicity m x n)*(exp ((a-1)*energy n)/(powerMass a x)^m) := by
  have h := (pow_pos (powerMass_pos a x) m).ne'
  calc
    _ = ((m.factorial:ℝ)*mass m a x-(powerMass a x)^m)/(powerMass a x)^m := by
      rw [excess,sub_div,div_self h]
    _ = (∑ n ∈ shells m x, ((m.factorial:ℝ)-multiplicity m x n)*exp ((a-1)*energy n))/
        (powerMass a x)^m := by
      congr 1
      rw [←weighted_total m a x,mass,mul_sum,←sum_sub_distrib]
      exact sum_congr rfl fun _ _ => (sub_mul _ _ _).symm
    _ = _ := by rw [sum_div]; exact sum_congr rfl fun _ _ => mul_div_assoc _ _ _

/-- Only repeated tuples can contribute to the exchange excess. The estimate
uses the exact collision mass of the elementary probability law. -/
theorem excess_le_repeat (m : ℕ) (a x : ℝ) : excess m a x ≤
    ((m.factorial:ℝ)-1)*repeatMass (primeProbability a x) m := by
  classical
  let q := primeProbability a x
  let g := fun n => ((m.factorial:ℝ)-multiplicity m x n)*
    (exp ((a-1)*energy n)/(powerMass a x)^m)
  have gw (n : ℕ+) (hn : n∈shells m x) : g n ≤ multiplicity m x n • g n := by
    rw [nsmul_eq_mul]
    exact le_mul_of_one_le_left (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast
      (multiplicity_bounds hn).2)) (div_nonneg (exp_pos _).le (pow_pos (powerMass_pos a x) m).le))
      (by exact_mod_cast (multiplicity_bounds hn).1)
  have bound (u : Fin m → PrimeAt x) : g (productLabel u) ≤
      ((m.factorial:ℝ)-1)*(tupleWeight q u-injectiveTupleWeight q u) := by
    change ((m.factorial:ℝ)-multiplicity m x (productLabel u))*_ ≤ _
    rw [←tuple_probability]
    by_cases hu : Function.Injective u
    · rw [multiplicity_injective u hu,sub_self,zero_mul,injectiveTupleWeight,if_pos hu,sub_self,mul_zero]
    · rw [injectiveTupleWeight,if_neg hu,sub_zero]
      apply mul_le_mul_of_nonneg_right _ (_root_.RHTower.tupleWeight_nonneg q (primeProbability_nonneg a x) u)
      exact sub_le_sub_left (by exact_mod_cast
        (multiplicity_bounds (mem_image_of_mem productLabel (mem_univ u))).1) _
  calc
    excess m a x = ∑ n ∈ shells m x, g n := excess_sum m a x
    _ ≤ ∑ n ∈ shells m x, multiplicity m x n • g n := sum_le_sum gw
    _ = ∑ u : Fin m → PrimeAt x, g (productLabel u) := sum_fibers m x g
    _ ≤ ∑ u : Fin m → PrimeAt x, ((m.factorial:ℝ)-1)*(tupleWeight q u-injectiveTupleWeight q u) :=
      sum_le_sum fun u _ => bound u
    _ = _ := by
      rw [←mul_sum,sum_sub_distrib,_root_.RHTower.sum_tupleWeight,primeProbability_sum,one_pow,repeatMass]
      rfl

/-- The collision bound holds for every finite cutoff and every heat index. -/
theorem excess_le_collision (m : ℕ) (a x : ℝ) : excess m a x ≤
    ((m.factorial:ℝ)-1)*((m.choose 2:ℝ)*∑ p,(primeProbability a x p)^2) := by
  exact (excess_le_repeat m a x).trans (mul_le_mul_of_nonneg_left
    (repeat_le _ (primeProbability_nonneg a x) (primeProbability_sum a x) m).2
    (sub_nonneg.mpr (by exact_mod_cast Nat.factorial_pos m)))

#print axioms excess_nonneg
#print axioms excess_le_repeat
#print axioms excess_le_collision

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary
