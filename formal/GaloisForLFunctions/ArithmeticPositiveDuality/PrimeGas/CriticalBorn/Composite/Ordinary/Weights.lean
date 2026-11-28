import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy.Reading
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Collision

/-! # Independent prime sampling on fibers of the product map -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary

open Finset Real

def primeProbability (a x : ℝ) (p : PrimeAt x) :=
  exp ((a-1)*energy (primeLabel p))/powerMass a x

theorem primeProbability_nonneg (a x : ℝ) (p : PrimeAt x) : 0 ≤ primeProbability a x p :=
  div_nonneg (exp_pos _).le (powerMass_pos _ _).le

theorem primeProbability_sum (a x : ℝ) : ∑ p, primeProbability a x p=1 := by
  have one (p : PrimeAt x) : exp ((a-1)*energy (primeLabel p))=(p.val:ℝ)^(a-1) := by
    rw [rpow_def_of_pos (Nat.cast_pos.mpr (Nat.mem_primesBelow.mp p.property).2.pos),mul_comm]
    rfl
  simp only [primeProbability,←sum_div,one]
  rw [sum_coe_sort (primes (cutoff x)) (fun p : ℕ => (p:ℝ)^(a-1))]
  exact div_self (powerMass_pos a x).ne'

/-- Each ordered tuple has the same probability as every other tuple on its shell. -/
theorem tuple_probability {m : ℕ} (a x : ℝ) (u : Fin m → PrimeAt x) :
    _root_.RHTower.tupleWeight (primeProbability a x) u =
      exp ((a-1)*energy (productLabel u))/(powerMass a x)^m := by
  simp only [_root_.RHTower.tupleWeight,primeProbability,prod_div_distrib,prod_const,card_univ,
    Fintype.card_fin,Energy.energy_product,mul_sum,Real.exp_sum]

theorem primeProbability_le {a : ℝ} (ha : a≤1) (x : ℝ) (p : PrimeAt x) :
    primeProbability a x p ≤ 1/powerMass a x := by
  apply div_le_div_of_nonneg_right _ (powerMass_pos _ _).le
  exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ha)
    (log_natCast_nonneg _))

#print axioms primeProbability_sum
#print axioms tuple_probability
#print axioms primeProbability_le

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary
