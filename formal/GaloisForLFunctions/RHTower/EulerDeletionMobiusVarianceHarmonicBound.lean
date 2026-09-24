import GaloisForLFunctions.RHTower.EulerDeletionMobiusPeriodCovariance
import GaloisForLFunctions.RHTower.Sieve.GcdSquareHarmonicBound

/-!
# Möbius residue-source complete-period variance bound

The exact gcd-square covariance and universal harmonic Gram bound give a
quantitative bound with no cancellation premise. The bound is used to transfer
complete-period energy to physical windows at the two-log clock.
-/

open Finset ArithmeticFunction
open scoped BigOperators
noncomputable section

namespace RHTower.DeletionPeriodCovariance

def mobiusVariance (N : ℕ) : ℝ :=
  periodCovariance (Finset.Icc 1 N)
    (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℝ))

private theorem gcd_kernel_abs_upper (N : ℕ) :
    mobiusVariance N ≤ (1 / 12 : ℝ) *
      ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        (Nat.gcd p.1 p.2 : ℝ) ^ (2 : ℕ) / ((p.1 : ℝ) * p.2) := by
  let S := Finset.Icc 1 N
  have hterm (m : ℕ) (hm : m ∈ S) (n : ℕ) (hn : n ∈ S) :
      (((ArithmeticFunction.moebius m : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          ((Nat.gcd m n : ℝ) ^ (2 : ℕ) - 1)) /
          ((m : ℝ) * n) ≤
        (Nat.gcd m n : ℝ) ^ (2 : ℕ) / ((m : ℝ) * n) := by
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hgcd : 1 ≤ (Nat.gcd m n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.gcd_pos_of_pos_left n (Finset.mem_Icc.mp hm).1).ne'
    have hmu_m : |((ArithmeticFunction.moebius m : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m))
    have hmu_n : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    have hmu : ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) ≤ 1 := by
      have h : |((ArithmeticFunction.moebius m : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
        rw [abs_mul]
        calc
          |((ArithmeticFunction.moebius m : ℤ) : ℝ)| *
              |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ (1 : ℝ) * 1 :=
                mul_le_mul hmu_m hmu_n (abs_nonneg _) (by norm_num)
          _ = 1 := by ring
      exact (le_abs_self _).trans h
    have hgcd2 : 1 ≤ (Nat.gcd m n : ℝ) ^ (2 : ℕ) := by nlinarith
    apply div_le_div_of_nonneg_right _ (mul_pos hm0 hn0).le
    calc
      _ ≤ (1 : ℝ) * ((Nat.gcd m n : ℝ) ^ (2 : ℕ) - 1) :=
        mul_le_mul_of_nonneg_right hmu (sub_nonneg.mpr hgcd2)
      _ ≤ (Nat.gcd m n : ℝ) ^ (2 : ℕ) := by nlinarith
  unfold mobiusVariance periodCovariance
  change (1 / 12 : ℝ) *
      (∑ m ∈ S, ∑ n ∈ S,
        (((ArithmeticFunction.moebius m : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          ((Nat.gcd m n : ℝ) ^ (2 : ℕ) - 1)) / ((m : ℝ) * n)) ≤ _
  rw [Finset.sum_product]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 12)
  exact Finset.sum_le_sum (fun m hm =>
    Finset.sum_le_sum (fun n hn => hterm m hm n hn))

/-- Absolute-value majorization gives the first quantitative variance bound. -/
theorem mobiusVariance_le_harmonic_sq (N : ℕ) :
    mobiusVariance N ≤
      (N : ℝ) * RHTower.Sieve.harmonicSqBound N ^ (2 : ℕ) / 12 := by
  have hsum := RHTower.Sieve.gcd_square_double_sum_le_harmonic N
  have hsum' :
      (∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        (Nat.gcd p.1 p.2 : ℝ) ^ (2 : ℕ) / ((p.1 : ℝ) * p.2)) ≤
      (N : ℝ) * RHTower.Sieve.harmonicSqBound N ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using hsum
  calc
    mobiusVariance N ≤ (1 / 12 : ℝ) *
        ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
          (Nat.gcd p.1 p.2 : ℝ) ^ (2 : ℕ) / ((p.1 : ℝ) * p.2) :=
      gcd_kernel_abs_upper N
    _ ≤ (1 / 12 : ℝ) *
        ((N : ℝ) * RHTower.Sieve.harmonicSqBound N ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsum' (by norm_num)
    _ = (N : ℝ) * RHTower.Sieve.harmonicSqBound N ^ (2 : ℕ) / 12 := by ring

end RHTower.DeletionPeriodCovariance
