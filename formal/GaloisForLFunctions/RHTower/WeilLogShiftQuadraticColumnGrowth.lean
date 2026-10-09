import GaloisForLFunctions.RHTower.WeilLogShiftLateColumnRunaway

/-!
# Quadratic-exponent growth of late inverse columns

Accumulating the native adjacent amplification retains the full triangular
sum in the exponent. Every sufficiently late fixed column consequently
escapes every exponential envelope. The native tail threshold is unchanged;
no assertion about early columns or a matching upper bound is made.
-/

open Filter Topology Real

namespace RHTower

open WeilExcess

/-- Accumulating every adjacent gain gives a quadratic exponent between
any two indices beyond the seed of a sufficiently late fixed column. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_quadratic_exponent_growth :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ j : ℕ, k + 2 ≤ j →
      ∀ n : ℕ, j ≤ n →
        exp (((n : ℝ) * ((n : ℝ) + 1) - (j : ℝ) * ((j : ℝ) + 1)) / 2) *
          |weilLogShiftRecoveryCoefficientColumn k j| ≤
            |weilLogShiftRecoveryCoefficientColumn k n| := by
  obtain ⟨K, hK, hgrowth⟩ := exists_weilLogShiftRecoveryCoefficientColumn_growth
  refine ⟨K, hK, fun k hk j hj n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base =>
      simp only [sub_self, zero_div, exp_zero, one_mul, le_refl]
  | succ n hn ih =>
      have hnseed : k + 2 ≤ n := hj.trans hn
      have hstep₀ := hgrowth k hk (n + 1) (by omega) n hnseed (by omega)
      have hstep : exp ((n : ℝ) + 1) * |weilLogShiftRecoveryCoefficientColumn k n| ≤
          |weilLogShiftRecoveryCoefficientColumn k (n + 1)| := by
        simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one] using hstep₀
      have he : exp ((((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) -
          (j : ℝ) * ((j : ℝ) + 1)) / 2) =
          exp ((n : ℝ) + 1) *
            exp (((n : ℝ) * ((n : ℝ) + 1) - (j : ℝ) * ((j : ℝ) + 1)) / 2) := by
        rw [← exp_add]
        congr 1
        push_cast
        ring
      rw [he, mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih (exp_pos _).le).trans hstep

/-- Every sufficiently late fixed column has a positive lower envelope
with exponent `n*(n+1)/2`, not merely a fixed linear exponential rate. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_quadratic_exponential_lower :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, k + 2 ≤ n → c * exp ((n : ℝ) * ((n : ℝ) + 1) / 2) ≤
        |weilLogShiftRecoveryCoefficientColumn k n| := by
  obtain ⟨K, hK, hgrowth⟩ := exists_weilLogShiftRecoveryCoefficientColumn_quadratic_exponent_growth
  refine ⟨K, hK, fun k hk => ?_⟩
  let c : ℝ := |weilLogShiftRecoveryCoefficientColumn k (k + 2)| *
    exp (-(((k : ℝ) + 2) * ((k : ℝ) + 3) / 2))
  have hc : 0 < c := mul_pos
    (abs_pos.mpr (weilLogShiftRecoveryCoefficientColumn_seed_pos k).ne') (exp_pos _)
  refine ⟨c, hc, fun n hn => ?_⟩
  have h := hgrowth k hk (k + 2) le_rfl n hn
  calc
    c * exp ((n : ℝ) * ((n : ℝ) + 1) / 2) =
        exp (((n : ℝ) * ((n : ℝ) + 1) -
          ((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) + 1)) / 2) *
            |weilLogShiftRecoveryCoefficientColumn k (k + 2)| := by
      dsimp only [c]
      rw [mul_assoc, ← exp_add]
      have he : -(((k : ℝ) + 2) * ((k : ℝ) + 3) / 2) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 =
          ((n : ℝ) * ((n : ℝ) + 1) -
            ((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) + 1)) / 2 := by
        push_cast
        ring
      rw [he, mul_comm]
    _ ≤ _ := h

/-- No fixed real exponential damping controls a sufficiently late
coefficient column: its damped absolute coefficients still tend to infinity. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_all_exponential_dampings_runaway :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ A : ℝ,
      Tendsto (fun n : ℕ => exp (-(A * n)) *
        |weilLogShiftRecoveryCoefficientColumn k n|) atTop atTop := by
  obtain ⟨K, hK, hcoeff⟩ := exists_weilLogShiftRecoveryCoefficientColumn_quadratic_exponential_lower
  refine ⟨K, hK, fun k hk A => ?_⟩
  obtain ⟨c, hc, hcol⟩ := hcoeff k hk
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * A + 1)
  have hlower : ∀ᶠ n : ℕ in atTop,
      c * exp (n : ℝ) ≤ exp (-(A * n)) * |weilLogShiftRecoveryCoefficientColumn k n| := by
    filter_upwards [eventually_ge_atTop (max N (k + 2))] with n hn
    have hnN : (N : ℝ) ≤ n := by
      exact_mod_cast (le_trans (le_max_left N (k + 2)) hn)
    have hlinear : 2 * A + 1 ≤ (n : ℝ) := hN.le.trans hnN
    have hpoly : (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 - A * n := by
      have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hlinear)
      nlinarith only [h]
    calc
      c * exp (n : ℝ) ≤ c * exp ((n : ℝ) * ((n : ℝ) + 1) / 2 - A * n) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hpoly) hc.le
      _ = exp (-(A * n)) * (c * exp ((n : ℝ) * ((n : ℝ) + 1) / 2)) := by
        rw [sub_eq_add_neg, exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hcol n (le_trans (le_max_right N (k + 2)) hn)) (exp_pos _).le
  have hexp : Tendsto (fun n : ℕ => c * exp (n : ℝ)) atTop atTop :=
    (tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hlower, (tendsto_atTop.mp hexp) B] with n hn hB
  exact hB.trans hn

end RHTower
