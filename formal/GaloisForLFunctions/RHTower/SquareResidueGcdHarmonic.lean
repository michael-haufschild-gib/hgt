import GaloisForLFunctions.RHTower.FareySawtoothMeanSquare

/-!
Weighted square-root gcd harmonic bound. Cauchy--Schwarz combines the
corpus's double-gcd harmonic estimate with a single harmonic sum. Its
constant-weight specialization controls the aggregate non-coprime
frequency cost in centered quadratic-residue sums.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace RHTower

theorem squareResidue_weighted_gcd_harmonic_le (D : ℕ) (w : ℕ → ℝ) :
    (∑ q ∈ Ioc 0 D, ∑ k ∈ Ioc 0 D,
      w q * Real.sqrt ((Nat.gcd q k : ℝ) / q) / k) ≤
      Real.sqrt (∑ q ∈ Ioc 0 D, (w q) ^ 2) * (1 + Real.log D) ^ 2 := by
  let P := (Ioc 0 D) ×ˢ (Ioc 0 D)
  let F : ℕ × ℕ → ℝ := fun p => Real.sqrt ((Nat.gcd p.1 p.2 : ℝ) / (p.1 * p.2))
  let G : ℕ × ℕ → ℝ := fun p => w p.1 / Real.sqrt p.2
  let A := ∑ q ∈ Ioc 0 D, (w q) ^ 2
  let H := ∑ k ∈ Ioc 0 D, (1 : ℝ) / k
  have hprod (q k : ℕ) (hk : 0 < k) :
      F (q, k) * G (q, k) = w q * Real.sqrt ((Nat.gcd q k : ℝ) / q) / k := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hkn : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hkR)
    have hs : Real.sqrt (k : ℝ) * Real.sqrt k = (k : ℝ) := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg k)]
    dsimp [F, G]
    rw [← div_div, Real.sqrt_div (by positivity)]
    calc
      _ = w q * Real.sqrt ((Nat.gcd q k : ℝ) / q) /
          (Real.sqrt k * Real.sqrt k) := by field_simp [hkn]
      _ = _ := by rw [hs]
  have hFG : (∑ p ∈ P, F p * G p) =
      ∑ q ∈ Ioc 0 D, ∑ k ∈ Ioc 0 D,
        w q * Real.sqrt ((Nat.gcd q k : ℝ) / q) / k := by
    rw [show P = (Ioc 0 D) ×ˢ (Ioc 0 D) from rfl, Finset.sum_product]
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro k hk
    exact hprod q k (mem_Ioc.mp hk).1
  have hF2 : (∑ p ∈ P, (F p) ^ 2) =
      ∑ q ∈ Ioc 0 D, ∑ k ∈ Ioc 0 D, (Nat.gcd q k : ℝ) / ((q : ℝ) * k) := by
    calc
      _ = ∑ p ∈ P, (Nat.gcd p.1 p.2 : ℝ) / ((p.1 : ℝ) * p.2) := by
        apply sum_congr rfl
        intro p _
        exact Real.sq_sqrt (by positivity)
      _ = _ := by simp only [P, Finset.sum_product]
  have hG2 : (∑ p ∈ P, (G p) ^ 2) = A * H := by
    have hp (p : ℕ × ℕ) : (G p) ^ 2 = (w p.1) ^ 2 / p.2 := by
      dsimp [G]
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg p.2)]
    simp only [hp, P, A, H, Finset.sum_product, mul_sum, sum_mul, div_eq_mul_inv, one_mul]
    rw [sum_comm]
  have hH : H ≤ 1 + Real.log D := by
    have he : Ioc 0 D = Icc 1 D := by ext k; simp only [mem_Ioc, mem_Icc]; omega
    dsimp [H]
    rw [he]
    exact Sieve.sum_Icc_one_div_le_one_add_log D
  have hA : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hH0 : 0 ≤ H := sum_nonneg fun _ _ => by positivity
  have hlog : 0 ≤ 1 + Real.log D := by have := Real.log_natCast_nonneg D; linarith
  have hc := Finset.sum_mul_sq_le_sq_mul_sq P F G
  rw [hFG, hF2, hG2] at hc
  have hbound : (∑ q ∈ Ioc 0 D, ∑ k ∈ Ioc 0 D,
      w q * Real.sqrt ((Nat.gcd q k : ℝ) / q) / k) ^ 2 ≤
      A * (1 + Real.log D) ^ 4 := by
    apply hc.trans
    calc
      _ ≤ (1 + Real.log D) ^ 3 * (A * (1 + Real.log D)) :=
        mul_le_mul (sum_sum_gcd_div_le D)
          (mul_le_mul_of_nonneg_left hH hA) (mul_nonneg hA hH0) (by positivity)
      _ = _ := by ring
  have hs : (Real.sqrt A * (1 + Real.log D) ^ 2) ^ 2 =
      A * (1 + Real.log D) ^ 4 := by
    rw [mul_pow, Real.sq_sqrt hA]
    ring
  have hn : 0 ≤ Real.sqrt A * (1 + Real.log D) ^ 2 := by positivity
  change _ ≤ Real.sqrt A * (1 + Real.log D) ^ 2
  nlinarith

theorem squareResidue_gcd_harmonic_le (D : ℕ) :
    (∑ q ∈ Ioc 0 D, ∑ k ∈ Ioc 0 D,
      Real.sqrt ((Nat.gcd q k : ℝ) / q) / k) ≤
      Real.sqrt D * (1 + Real.log D) ^ 2 := by
  simpa using squareResidue_weighted_gcd_harmonic_le D (fun _ => 1)

end RHTower
