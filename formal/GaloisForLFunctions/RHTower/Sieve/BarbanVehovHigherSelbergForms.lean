import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogOriginalAsymptotics

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Lcm form with one additional complementary logarithm. -/
def barbanVehovSelbergMixedDiagonal (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    barbanVehovWeight N p.1 * barbanVehovWeight N p.2 *
      Real.log ((N : ℝ) / (p.2 : ℝ)) / (Nat.lcm p.1 p.2 : ℝ)

/-- Lcm form with one additional complementary logarithm on each side. -/
def barbanVehovSelbergQuadraticLogDiagonal (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    barbanVehovWeight N p.1 * barbanVehovWeight N p.2 *
      (Real.log ((N : ℝ) / (p.1 : ℝ)) *
        Real.log ((N : ℝ) / (p.2 : ℝ))) /
      (Nat.lcm p.1 p.2 : ℝ)

theorem barbanVehovSelbergMixedDiagonal_eq_originalLogOneTwo (N : ℕ) :
    barbanVehovSelbergMixedDiagonal N = selbergOriginalLogOneTwo N := by
  rw [barbanVehovSelbergMixedDiagonal, Finset.sum_product,
    selbergOriginalLogOneTwo]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [barbanVehovWeight, if_pos (Finset.mem_Icc.mp hm).2,
    barbanVehovWeight, if_pos (Finset.mem_Icc.mp hn).2,
    selbergOriginalCoeff]
  have hmR : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  have hlcm : Nat.lcm m n ≠ 0 := Nat.lcm_ne_zero
    (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
    (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  have hlcmR : (Nat.lcm m n : ℝ) ≠ 0 := by exact_mod_cast hlcm
  have hgcdlcm : (Nat.gcd m n : ℝ) * (Nat.lcm m n : ℝ) =
      (m : ℝ) * (n : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm m n
  push_cast
  field_simp [hmR, hnR, hlcmR]
  calc
    (((μ m : ℤ) : ℝ) * (m : ℝ) * Real.log ((N : ℝ) / (m : ℝ)) *
        ((μ n : ℤ) : ℝ) * (n : ℝ) * Real.log ((N : ℝ) / (n : ℝ)) ^ 2) =
        (((μ m : ℤ) : ℝ) * Real.log ((N : ℝ) / (m : ℝ)) *
          ((μ n : ℤ) : ℝ) * Real.log ((N : ℝ) / (n : ℝ)) ^ 2) *
            ((m : ℝ) * (n : ℝ)) := by ring
    _ = (((μ m : ℤ) : ℝ) * Real.log ((N : ℝ) / (m : ℝ)) *
          ((μ n : ℤ) : ℝ) * Real.log ((N : ℝ) / (n : ℝ)) ^ 2) *
            ((Nat.gcd m n : ℝ) * (Nat.lcm m n : ℝ)) := by rw [hgcdlcm]
    _ = _ := by ring

theorem barbanVehovSelbergQuadraticLogDiagonal_eq_originalLogTwoTwo (N : ℕ) :
    barbanVehovSelbergQuadraticLogDiagonal N = selbergOriginalLogTwoTwo N := by
  rw [barbanVehovSelbergQuadraticLogDiagonal, Finset.sum_product,
    selbergOriginalLogTwoTwo]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [barbanVehovWeight, if_pos (Finset.mem_Icc.mp hm).2,
    barbanVehovWeight, if_pos (Finset.mem_Icc.mp hn).2,
    selbergOriginalCoeff]
  have hmR : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  have hlcm : Nat.lcm m n ≠ 0 := Nat.lcm_ne_zero
    (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
    (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  have hlcmR : (Nat.lcm m n : ℝ) ≠ 0 := by exact_mod_cast hlcm
  have hgcdlcm : (Nat.gcd m n : ℝ) * (Nat.lcm m n : ℝ) =
      (m : ℝ) * (n : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm m n
  push_cast
  field_simp [hmR, hnR, hlcmR]
  calc
    (((μ m : ℤ) : ℝ) * (m : ℝ) * Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
        ((μ n : ℤ) : ℝ) * (n : ℝ) * Real.log ((N : ℝ) / (n : ℝ)) ^ 2) =
        (((μ m : ℤ) : ℝ) * Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
          ((μ n : ℤ) : ℝ) * Real.log ((N : ℝ) / (n : ℝ)) ^ 2) *
            ((m : ℝ) * (n : ℝ)) := by ring
    _ = (((μ m : ℤ) : ℝ) * Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
          ((μ n : ℤ) : ℝ) * Real.log ((N : ℝ) / (n : ℝ)) ^ 2) *
            ((Nat.gcd m n : ℝ) * (Nat.lcm m n : ℝ)) := by rw [hgcdlcm]
    _ = _ := by ring

theorem tendsto_barbanVehovSelbergMixedDiagonal_div_log_sq_one :
    Tendsto (fun N : ℕ =>
      barbanVehovSelbergMixedDiagonal N / Real.log N ^ 2)
      atTop (𝓝 1) := by
  simpa only [barbanVehovSelbergMixedDiagonal_eq_originalLogOneTwo] using
    tendsto_selbergOriginalLogOneTwo_div_log_sq_one

theorem tendsto_barbanVehovSelbergQuadraticLogDiagonal_div_log_cube_four_thirds :
    Tendsto (fun N : ℕ =>
      barbanVehovSelbergQuadraticLogDiagonal N / Real.log N ^ 3)
      atTop (𝓝 (4 / 3 : ℝ)) := by
  simpa only [barbanVehovSelbergQuadraticLogDiagonal_eq_originalLogTwoTwo] using
    tendsto_selbergOriginalLogTwoTwo_div_log_cube_four_thirds

end

end RHTower.Sieve
