import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# Sharp unconditional upper bound for half-weighted von Mangoldt mass

Discrete Abel summation upgrades the former `O(sqrt X * log X)` corpus bound to the sharp
Chebyshev-scale estimate `primeMassHalf X ≤ 21 * sqrt X`.  Only `psi(N) ≤ 7N` and the elementary
square-root harmonic sum are used.  This removes a spurious logarithmic loss from mass-cone
terminal fluxes; no PNT remainder or numerical computation enters.
-/

open Finset Real

namespace RHTower

/-- Square-root Abel increments cost at most one inverse square root. -/
theorem mul_inv_sqrt_sub_inv_sqrt_succ_le
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹ -
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) ≤
      (Real.sqrt (n : ℝ))⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ha : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hb : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hnp0
  have hab : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have ha2 : Real.sqrt (n : ℝ) ^ (2 : ℕ) = (n : ℝ) := Real.sq_sqrt hn0.le
  have hb2 : Real.sqrt ((n : ℝ) + 1) ^ (2 : ℕ) = (n : ℝ) + 1 :=
    Real.sq_sqrt hnp0.le
  rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_cast]
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp
  nlinarith

theorem sum_range_vonMangoldt_eq_chebyshevPsi (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n) =
      chebyshevPsi N := by
  rw [show Finset.range (N + 1) = Finset.Icc 0 N by
    ext n
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega]
  rw [Icc_zero_eq_insert, Finset.sum_insert (by simp)]
  have hvm0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    exact not_isPrimePow_zero
  rw [hvm0, zero_add]
  rfl

/-- Abel normal form for the finite half-weighted von Mangoldt mass. -/
theorem primeMassHalf_nat_abel (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n) =
      (Real.sqrt N)⁻¹ * chebyshevPsi N +
        ∑ n ∈ Finset.Icc 1 (N - 1),
          ((Real.sqrt (n : ℝ))⁻¹ -
            (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) * chebyshevPsi n := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hkey := Finset.sum_Ioc_by_parts
    (fun n : ℕ => (Real.sqrt n)⁻¹)
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n) hN
  simp only [smul_eq_mul] at hkey
  rw [hIoc] at hkey
  rw [sum_range_vonMangoldt_eq_chebyshevPsi N] at hkey
  have hvm0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    exact not_isPrimePow_zero
  have hbase :
      (Real.sqrt ((0 + 1 : ℕ) : ℝ))⁻¹ *
        (∑ i ∈ Finset.range (0 + 1), ArithmeticFunction.vonMangoldt i) = 0 := by
    rw [Finset.sum_range_one, hvm0, mul_zero]
  rw [hbase, sub_zero] at hkey
  calc
    (∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n) =
        ∑ n ∈ Finset.Icc 1 N,
          (Real.sqrt n)⁻¹ * ArithmeticFunction.vonMangoldt n := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [div_eq_mul_inv]
            ring
    _ = (Real.sqrt N)⁻¹ * chebyshevPsi N -
        ∑ n ∈ Finset.Ioc 0 (N - 1),
          ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (n : ℝ))⁻¹) *
            (∑ j ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt j) := hkey
    _ = _ := by
      rw [show Finset.Ioc 0 (N - 1) = Finset.Icc 1 (N - 1) by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega]
      rw [sub_eq_add_neg]
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      rw [sum_range_vonMangoldt_eq_chebyshevPsi]
      ring

/-- The finite half-weighted von Mangoldt mass is at most `21 sqrt N`. -/
theorem primeMassHalf_nat_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n) ≤
      21 * Real.sqrt N := by
  rw [primeMassHalf_nat_abel N (by omega)]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hsN2 : Real.sqrt (N : ℝ) ^ (2 : ℕ) = (N : ℝ) := Real.sq_sqrt hN0.le
  have hboundary :
      (Real.sqrt (N : ℝ))⁻¹ * chebyshevPsi N ≤
        7 * Real.sqrt N := by
    have hpsi := chebyshevPsi_le_seven N
    calc
      (Real.sqrt (N : ℝ))⁻¹ * chebyshevPsi N ≤
          (Real.sqrt (N : ℝ))⁻¹ * (7 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hpsi (inv_nonneg.mpr (Real.sqrt_nonneg _))
      _ = 7 * Real.sqrt N := by
        rw [inv_eq_one_div]
        field_simp
        nlinarith
  have hterm : ∀ n ∈ Finset.Icc 1 (N - 1),
      ((Real.sqrt (n : ℝ))⁻¹ - (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) *
          chebyshevPsi n ≤
        7 * (Real.sqrt (n : ℝ))⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnp0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have ha : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have hb : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hnp0
    have hab : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hinv : (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ ≤
        (Real.sqrt (n : ℝ))⁻¹ := by
      rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_cast]
      exact (inv_le_inv₀ hb ha).2 hab
    have hdiff0 : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ -
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := sub_nonneg.mpr hinv
    have hpsi := chebyshevPsi_le_seven n
    calc
      ((Real.sqrt (n : ℝ))⁻¹ - (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) *
          chebyshevPsi n ≤
        ((Real.sqrt (n : ℝ))⁻¹ - (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) *
          (7 * (n : ℝ)) := mul_le_mul_of_nonneg_left hpsi hdiff0
      _ = 7 * ((n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹ -
          (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)) := by ring
      _ ≤ 7 * (Real.sqrt (n : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left
          (mul_inv_sqrt_sub_inv_sqrt_succ_le n hn1) (by norm_num)
  have hsum :
      (∑ n ∈ Finset.Icc 1 (N - 1),
        ((Real.sqrt (n : ℝ))⁻¹ - (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) *
          chebyshevPsi n) ≤ 14 * Real.sqrt N := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (N - 1),
          7 * (Real.sqrt (n : ℝ))⁻¹ := Finset.sum_le_sum hterm
      _ = 7 * ∑ n ∈ Finset.Icc 1 (N - 1),
          (1 : ℝ) / Real.sqrt n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [inv_eq_one_div]
      _ ≤ 7 * (2 * Real.sqrt ((N - 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le (N - 1)) (by norm_num)
      _ ≤ 14 * Real.sqrt N := by
        have hcast : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
        have hsqrt : Real.sqrt ((N - 1 : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) :=
          Real.sqrt_le_sqrt hcast
        nlinarith
  linarith

/-- **Sharp half-mass upper law.** `primeMassHalf X ≤ 21 sqrt X` for `X ≥ 1`. -/
theorem primeMassHalf_le_sqrt {X : ℝ} (hX : 1 ≤ X) :
    primeMassHalf X ≤ 21 * Real.sqrt X := by
  let N : ℕ := ⌊X⌋₊
  have hX0 : 0 ≤ X := by linarith
  have hN : 1 ≤ N := by
    dsimp only [N]
    apply Nat.le_floor
    simpa using hX
  have hvm0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    exact not_isPrimePow_zero
  have hmass : primeMassHalf X =
      ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
    rw [primeMassHalf]
    change (∑ n ∈ Finset.Icc 0 N,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n) = _
    rw [Icc_zero_eq_insert, Finset.sum_insert (by simp), hvm0, zero_div, zero_add]
  rw [hmass]
  calc
    _ ≤ 21 * Real.sqrt N := primeMassHalf_nat_le N hN
    _ ≤ 21 * Real.sqrt X := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.sqrt_le_sqrt (Nat.floor_le hX0)

end RHTower
