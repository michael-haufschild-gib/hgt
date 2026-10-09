import GaloisForLFunctions.RHTower.MobiusSquareDivisorProductBudget
import GaloisForLFunctions.RHTower.MobiusSquareBilinearCutoff

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace RHTower

/-- Exact displacement between the first square sample and the continuous birth. -/
noncomputable def mobiusSquareBirthRounding (q : ℕ) : ℝ :=
  (squareSampledHyperbolaBirth q 1 : ℝ) - Real.sqrt q

theorem mobiusSquareBirthRounding_bounds {q : ℕ} (hq : 0 < q) :
    0 ≤ mobiusSquareBirthRounding q ∧ mobiusSquareBirthRounding q ≤ 1 := by
  have hbNat := (squareSampledHyperbolaBirth_le_iff hq (by norm_num : 0 < (1 : ℕ))
    (squareSampledHyperbolaBirth q 1)).mp le_rfl
  simp only [mul_one] at hbNat
  have hbSq : (q : ℝ) ≤ (squareSampledHyperbolaBirth q 1 : ℝ) ^ 2 := by exact_mod_cast hbNat
  have hb : Real.sqrt q ≤ (squareSampledHyperbolaBirth q 1 : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    simpa only [Real.sq_sqrt (Nat.cast_nonneg q)] using hbSq
  have hsNat : (Nat.sqrt (q - 1)) ^ 2 ≤ q := by
    simpa only [pow_two] using (Nat.sqrt_le (q - 1)).trans (Nat.sub_le q 1)
  have hs : (Nat.sqrt (q - 1) : ℝ) ≤ Real.sqrt q := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg q)]
    exact_mod_cast hsNat
  have hbirth : (squareSampledHyperbolaBirth q 1 : ℝ) = (Nat.sqrt (q - 1) : ℝ) + 1 := by
    simp [squareSampledHyperbolaBirth]
  unfold mobiusSquareBirthRounding
  constructor <;> linarith

/-- In the first quotient cell, the full kernel counts its square-sample births exactly. -/
theorem mobiusSquareShortBilinearKernel_eq_top_cell_birth (N : ℕ) {q : ℕ}
    (hq : 0 < q) (hcell : (N - 1) ^ 2 < 2 * q) :
    mobiusSquareShortBilinearKernel N q =
      Real.log (q : ℝ) * ((N - squareSampledHyperbolaBirth q 1 : ℕ) : ℝ) := by
  classical
  rw [mobiusSquareShortBilinearKernel_eq_divisor_sum]
  have hin (s : ℕ) (hs : s ∈ range N) :
      (∑ n ∈ Icc 1 (s ^ 2 / q), (n.divisors.card : ℝ) *
        (Real.log (q : ℝ) + Real.log (n : ℝ) / 2)) =
      if q ≤ s ^ 2 then Real.log (q : ℝ) else 0 := by
    have hsN : s ≤ N - 1 := by have := mem_range.mp hs; omega
    have hs2 : s ^ 2 < 2 * q := lt_of_le_of_lt (by nlinarith) hcell
    have hdiv : s ^ 2 / q < 2 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    by_cases hsq : q ≤ s ^ 2
    · have hdiv1 : s ^ 2 / q = 1 := by
        have hge : 1 ≤ s ^ 2 / q := (Nat.le_div_iff_mul_le hq).mpr (by simpa using hsq)
        omega
      simp [hdiv1, hsq]
    · have hdiv0 : s ^ 2 / q = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge hsq)
      simp [hdiv0, hsq]
  rw [sum_congr rfl hin, ← sum_filter]
  have hset : (range N).filter (fun s => q ≤ s ^ 2) =
      Ico (squareSampledHyperbolaBirth q 1) N := by
    ext s
    have hb := squareSampledHyperbolaBirth_le_iff hq (by norm_num : 0 < (1 : ℕ)) s
    simp only [mul_one] at hb
    simp only [mem_filter, mem_range, mem_Ico]
    rw [hb]
    tauto
  rw [hset]
  simp [mul_comm]

theorem mobiusSquareShortBilinearKernel_eq_continuous_sub_rounding
    {N q : ℕ} (hq : 0 < q) (hqN : q ≤ N ^ 2) (hcell : (N - 1) ^ 2 < 2 * q) :
    mobiusSquareShortBilinearKernel N q =
      Real.log (q : ℝ) * ((N : ℝ) - Real.sqrt q) -
        Real.log (q : ℝ) * mobiusSquareBirthRounding q := by
  have hb : squareSampledHyperbolaBirth q 1 ≤ N :=
    (squareSampledHyperbolaBirth_le_iff hq (by norm_num : 0 < (1 : ℕ)) N).mpr (by simpa using hqN)
  rw [mobiusSquareShortBilinearKernel_eq_top_cell_birth N hq hcell, Nat.cast_sub hb]
  unfold mobiusSquareBirthRounding
  ring

/-- Outer corner of the actual full double-Möbius kernel. -/
noncomputable def mobiusSquareCornerAction (N U : ℕ) : ℝ :=
  ∑ a ∈ Ioc U N, ∑ b ∈ Ioc U N,
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
      mobiusSquareShortBilinearKernel N (a * b)

/-- The continuous corner depends on exactly four one-dimensional signed moments. -/
noncomputable def mobiusSquareCornerContinuous (N U : ℕ) : ℝ :=
  2 * ((N : ℝ) * (∑ a ∈ Ioc U N, (ArithmeticFunction.moebius a : ℝ)) *
      (∑ a ∈ Ioc U N, (ArithmeticFunction.moebius a : ℝ) * Real.log a) -
    (∑ a ∈ Ioc U N, (ArithmeticFunction.moebius a : ℝ) * Real.sqrt a) *
      (∑ a ∈ Ioc U N, (ArithmeticFunction.moebius a : ℝ) * Real.sqrt a * Real.log a))

/-- Exact signed lattice correction to the four-moment corner. -/
noncomputable def mobiusSquareCornerRounding (N U : ℕ) : ℝ :=
  ∑ a ∈ Ioc U N, ∑ b ∈ Ioc U N,
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
      Real.log (a * b : ℕ) * mobiusSquareBirthRounding (a * b)

private theorem corner_product_bounds {N U a b : ℕ}
    (ha : a ∈ Ioc U N) (hb : b ∈ Ioc U N) :
    0 < a * b ∧ a * b ≤ N ^ 2 ∧ Real.log (a * b : ℕ) ≤ 2 * Real.log (N : ℝ) := by
  have ha0 : 0 < a := lt_of_le_of_lt (Nat.zero_le U) (mem_Ioc.mp ha).1
  have hb0 : 0 < b := lt_of_le_of_lt (Nat.zero_le U) (mem_Ioc.mp hb).1
  have hp := Nat.mul_pos ha0 hb0
  have hcap : a * b ≤ N ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (mem_Ioc.mp ha).2 (mem_Ioc.mp hb).2
  have hl := Real.log_le_log (by exact_mod_cast hp : (0 : ℝ) < (a * b : ℕ))
    (by exact_mod_cast hcap : ((a * b : ℕ) : ℝ) ≤ (N : ℝ) ^ 2)
  rw [Real.log_pow] at hl
  norm_num at hl
  exact ⟨hp, hcap, by simpa only [Nat.cast_mul] using hl⟩

private theorem corner_continuous_factorization (S : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) :
    (∑ a ∈ S, ∑ b ∈ S, c a * c b * (Real.log a + Real.log b) *
        (x - Real.sqrt a * Real.sqrt b)) =
      2 * (x * (∑ a ∈ S, c a) * (∑ a ∈ S, c a * Real.log a) -
        (∑ a ∈ S, c a * Real.sqrt a) * (∑ a ∈ S, c a * Real.sqrt a * Real.log a)) := by
  have hp (a b : ℕ) : c a * c b * (Real.log a + Real.log b) *
      (x - Real.sqrt a * Real.sqrt b) =
      (x * c a) * (c b * Real.log b) + (x * (c a * Real.log a)) * c b -
      (c a * Real.sqrt a) * (c b * Real.sqrt b * Real.log b) -
      (c a * Real.sqrt a * Real.log a) * (c b * Real.sqrt b) := by ring
  simp_rw [hp, sum_sub_distrib, sum_add_distrib]
  rw [← sum_mul_sum, ← sum_mul_sum, ← sum_mul_sum, ← sum_mul_sum]
  simp_rw [← mul_sum]
  ring

theorem mobiusSquareCornerAction_eq_continuous_sub_rounding (N U : ℕ)
    (hcell : (N - 1) ^ 2 < 2 * (U + 1) ^ 2) :
    mobiusSquareCornerAction N U =
      mobiusSquareCornerContinuous N U - mobiusSquareCornerRounding N U := by
  unfold mobiusSquareCornerAction
  have hin (a : ℕ) (ha : a ∈ Ioc U N) (b : ℕ) (hb : b ∈ Ioc U N) :
      (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
        mobiusSquareShortBilinearKernel N (a * b) =
      (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
        (Real.log a + Real.log b) * ((N : ℝ) - Real.sqrt a * Real.sqrt b) -
      (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
        Real.log (a * b : ℕ) * mobiusSquareBirthRounding (a * b) := by
    have hp := corner_product_bounds ha hb
    have hlow := Nat.mul_le_mul (Nat.succ_le_iff.mpr (mem_Ioc.mp ha).1)
      (Nat.succ_le_iff.mpr (mem_Ioc.mp hb).1)
    have hc : (N - 1) ^ 2 < 2 * (a * b) := by nlinarith
    rw [mobiusSquareShortBilinearKernel_eq_continuous_sub_rounding hp.1 hp.2.1 hc]
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by have := (mem_Ioc.mp ha).1; omega)
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by have := (mem_Ioc.mp hb).1; omega)
    simp only [Nat.cast_mul, Real.sqrt_mul (le_of_lt ha0), Real.log_mul (ne_of_gt ha0) (ne_of_gt hb0)]
    ring
  calc
    _ = ∑ a ∈ Ioc U N, ∑ b ∈ Ioc U N,
        ((ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
          (Real.log a + Real.log b) * ((N : ℝ) - Real.sqrt a * Real.sqrt b) -
        (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
          Real.log (a * b : ℕ) * mobiusSquareBirthRounding (a * b)) := by
      apply sum_congr rfl
      intro a ha
      exact sum_congr rfl (hin a ha)
    _ = _ := by
      simp only [sum_sub_distrib]
      rw [corner_continuous_factorization]
      rfl

theorem abs_mobiusSquareCornerRounding_le (N U : ℕ) :
    |mobiusSquareCornerRounding N U| ≤
      2 * ((N - U : ℕ) : ℝ) ^ 2 * Real.log (N : ℝ) := by
  have hmu (a : ℕ) : |(ArithmeticFunction.moebius a : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
  have hin (a : ℕ) (ha : a ∈ Ioc U N) (b : ℕ) (hb : b ∈ Ioc U N) :
      |(ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
        Real.log (a * b : ℕ) * mobiusSquareBirthRounding (a * b)| ≤ 2 * Real.log (N : ℝ) := by
    have hp := corner_product_bounds ha hb
    have hr := mobiusSquareBirthRounding_bounds hp.1
    have hl0 := Real.log_natCast_nonneg (a * b)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hr.1, abs_of_nonneg hl0]
    have hcoeff : |(ArithmeticFunction.moebius a : ℝ)| * |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
      simpa using mul_le_mul (hmu a) (hmu b) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    calc
      _ ≤ (1 * Real.log (a * b : ℕ)) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hcoeff hl0) hr.2 hr.1 (by positivity)
      _ ≤ _ := by simpa using hp.2.2
  unfold mobiusSquareCornerRounding
  calc
    _ ≤ ∑ a ∈ Ioc U N, |∑ b ∈ Ioc U N,
        (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
          Real.log (a * b : ℕ) * mobiusSquareBirthRounding (a * b)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Ioc U N, ∑ _b ∈ Ioc U N, 2 * Real.log (N : ℝ) := by
      apply sum_le_sum
      intro a ha
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (hin a ha))
    _ = _ := by simp; ring

theorem abs_mobiusSquareCornerAction_sub_continuous_le (N U : ℕ)
    (hcell : (N - 1) ^ 2 < 2 * (U + 1) ^ 2) :
    |mobiusSquareCornerAction N U - mobiusSquareCornerContinuous N U| ≤
      2 * ((N - U : ℕ) : ℝ) ^ 2 * Real.log (N : ℝ) := by
  rw [mobiusSquareCornerAction_eq_continuous_sub_rounding N U hcell]
  simpa only [sub_sub_cancel_left, abs_neg] using abs_mobiusSquareCornerRounding_le N U

theorem mobiusSquareCorner_principal_add_remainder_eq (N U : ℕ)
    (hcell : (N - 1) ^ 2 < 2 * (U + 1) ^ 2) :
    (∑ a ∈ Ioc U N, ∑ b ∈ Ioc U N,
      (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
        mobiusSquareDivisorPrincipalKernel N (a * b)) +
    (∑ a ∈ Ioc U N, ∑ b ∈ Ioc U N,
      (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
        mobiusSquareDivisorRemainderKernel N (a * b)) =
      mobiusSquareCornerContinuous N U - mobiusSquareCornerRounding N U := by
  rw [← mobiusSquareCornerAction_eq_continuous_sub_rounding N U hcell]
  unfold mobiusSquareCornerAction
  simp_rw [mobiusSquareShortBilinearKernel_eq_principal_add_remainder, mul_add, sum_add_distrib]

end RHTower
