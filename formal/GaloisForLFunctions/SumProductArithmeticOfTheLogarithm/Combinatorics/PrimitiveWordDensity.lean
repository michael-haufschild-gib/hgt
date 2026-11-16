import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.Combinatorics.NecklaceGrowth
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Primitive words have density one

The proper-divisor error estimate implies that almost every long word
over an alphabet of at least two letters is primitive. The estimate is
uniform at every length and yields the exact asymptotic normalization of
the existing necklace count. This is the exponential-growth mechanism of
Zehavi, Proposition 4.5 and the final dimension comparison in §4.2,
arXiv:2611.18218.
-/

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

open Filter Topology

/-- Relative nonprimitive mass is bounded by a geometric term at half the word length. -/
theorem necklace_relative_error_bound (a n : ℕ) :
    (( (a + 2) ^ (n + 1) - (n + 1) * necklaceCount (a + 2) (n + 1) : ℕ) : ℝ) /
      ((a + 2 : ℕ) : ℝ) ^ (n + 1) ≤
        (((n + 1) / 2 : ℕ) : ℝ) / ((a + 2 : ℕ) : ℝ) ^ ((n + 1) / 2) := by
  have he := necklaceCount_error_le_half_pow (a + 2) n
  rw [max_eq_left (by omega : 1 ≤ a + 2)] at he
  have hp :
      ((a + 2) ^ (n + 1) - (n + 1) * necklaceCount (a + 2) (n + 1)) *
        (a + 2) ^ ((n + 1) / 2) ≤ ((n + 1) / 2) * (a + 2) ^ (n + 1) := by
    calc
      _ ≤ (((n + 1) / 2) * (a + 2) ^ ((n + 1) / 2)) *
          (a + 2) ^ ((n + 1) / 2) := Nat.mul_le_mul_right _ he
      _ = ((n + 1) / 2) * (a + 2) ^ (2 * ((n + 1) / 2)) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
      _ ≤ _ := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) (by omega))
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  exact_mod_cast hp

/-- Almost every long word is primitive: the normalized primitive-orbit count tends to one. -/
theorem tendsto_necklace_primitive_density (a : ℕ) :
    Tendsto (fun n : ℕ =>
      (((n + 1) * necklaceCount (a + 2) (n + 1) : ℕ) : ℝ) /
        ((a + 2 : ℕ) : ℝ) ^ (n + 1)) atTop (𝓝 1) := by
  have hbase : (1 : ℝ) < ((a + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < a + 2)
  have ht : Tendsto (fun n : ℕ => (((n + 1) / 2 : ℕ) : ℝ) /
      ((a + 2 : ℕ) : ℝ) ^ ((n + 1) / 2)) atTop (𝓝 0) := by
    have h := (tendsto_pow_const_div_const_pow_of_one_lt 1 hbase).comp
      ((Nat.tendsto_div_const_atTop (n := 2) (by decide)).comp
        (tendsto_add_atTop_nat 1))
    simpa only [pow_one] using h
  have he : Tendsto (fun n : ℕ =>
      (((a + 2) ^ (n + 1) - (n + 1) * necklaceCount (a + 2) (n + 1) : ℕ) : ℝ) /
        ((a + 2 : ℕ) : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
    squeeze_zero (fun n => by positivity) (necklace_relative_error_bound a) ht
  have hd := tendsto_const_nhds.sub he
  rw [sub_zero] at hd
  convert hd using 1
  funext n
  rw [Nat.cast_sub (mul_necklaceCount_le_pow (a + 2) (n + 1) (Nat.succ_pos n)), Nat.cast_pow]
  field_simp
  ring

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

#print axioms GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.necklace_relative_error_bound
#print axioms GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.tendsto_necklace_primitive_density
