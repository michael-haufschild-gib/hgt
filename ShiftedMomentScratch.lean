import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

#check add_pow
#check MeasureTheory.integral_finsetSum
#check MeasureTheory.integrable_finsetSum
#check Finset.sum_range_reflect
#check Nat.choose_mul_factorial_mul_factorial

theorem test_integral_shifted_pow
    (N p : ℕ) (hp : 0 < p) (a : ℝ) :
    (∫ x : ℝ in Ioi 0, (x + a) ^ N * Real.exp (-(p : ℝ) * x)) =
      ∑ m ∈ Finset.range (N + 1),
        (N.choose m : ℝ) * a ^ (N - m) *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
  have hInt (m : ℕ) : IntegrableOn
      (fun x : ℝ => ((N.choose m : ℝ) * a ^ (N - m)) *
        (x ^ m * Real.exp (-(p : ℝ) * x))) (Ioi 0) := by
    have hb : IntegrableOn
        (fun x : ℝ => x ^ m * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
      apply Integrable.of_integral_ne_zero
      rw [integral_pow_mul_exp_nat_neg m p hp]
      positivity
    exact hb.const_mul _
  rw [show (fun x : ℝ => (x + a) ^ N * Real.exp (-(p : ℝ) * x)) =
      fun x : ℝ => ∑ m ∈ Finset.range (N + 1),
        ((N.choose m : ℝ) * a ^ (N - m)) *
          (x ^ m * Real.exp (-(p : ℝ) * x)) by
    funext x
    rw [add_pow]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _hm
    ring]
  rw [MeasureTheory.integral_finsetSum _ (fun m _hm => hInt m)]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [MeasureTheory.integral_const_mul, integral_pow_mul_exp_nat_neg m p hp]

theorem test_shifted_moment_sum_eq
    (N p : ℕ) (hp : 0 < p) (a : ℝ) :
    (∑ m ∈ Finset.range (N + 1),
        (N.choose m : ℝ) * a ^ (N - m) *
          (m.factorial / (p : ℝ) ^ (m + 1))) =
      (N.factorial / (p : ℝ) ^ (N + 1)) *
        ∑ j ∈ Finset.range (N + 1),
          (((p : ℝ) * a) ^ j / j.factorial) := by
  rw [← Finset.sum_range_reflect
    (fun j : ℕ => (((p : ℝ) * a) ^ j / j.factorial)) (N + 1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmle : m ≤ N := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  rw [show N + 1 - 1 - m = N - m by omega]
  have hfacNat := Nat.choose_mul_factorial_mul_factorial hmle
  have hfac : (N.choose m : ℝ) * m.factorial * (N - m).factorial =
      N.factorial := by exact_mod_cast hfacNat
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hmf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hsubf : (((N - m).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hpR, hmf, hsubf]
  rw [mul_pow]
  rw [show N + 1 = (m + 1) + (N - m) by omega, pow_add]
  nlinarith

theorem test_shifted_moment_sum_le
    (N p : ℕ) (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) :
    (∑ m ∈ Finset.range (N + 1),
        (N.choose m : ℝ) * a ^ (N - m) *
          (m.factorial / (p : ℝ) ^ (m + 1))) ≤
      (N.factorial / (p : ℝ) ^ (N + 1)) * Real.exp ((p : ℝ) * a) := by
  rw [test_shifted_moment_sum_eq N p hp a]
  gcongr
  exact Real.sum_le_exp_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) _

end

end RHTower
