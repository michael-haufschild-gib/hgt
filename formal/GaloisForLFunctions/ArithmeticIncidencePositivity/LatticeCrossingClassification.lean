import GaloisForLFunctions.ArithmeticIncidencePositivity.CrossingConductanceSignLaw

/-!
# The negative archimedean crossing pairs of the lattice

On the logarithmic lattice the crossing pair `(−log a, log b)`, `a, b ≥ 1`, has archimedean
gauge-free kernel

    k_arch(−log a, log b) = (4 (ab)² − (a−1)(b−1)((ab)² − 1)) / (4 √(ab) ((ab)² − 1)),

so its conductance in an odd gauge is negative exactly when

    (a − 1)(b − 1)((ab)² − 1) < 4 (ab)².

The axis pairs `a = 1` or `b = 1` always satisfy this. For `a, b ≥ 2` the inequality holds for
exactly five unordered pairs: `{2,2}, {2,3}, {2,4}, {2,5}, {3,3}`. Two of them are arithmetic
near-misses: `(2,5)` gives `396 < 400` and `(3,3)` gives `320 < 324`. Every other lattice crossing
pair has positive archimedean conductance. Together with the prime-power dominance law this says
that on the lattice the whole negative conductance of the zero form is carried by the axis pairs
and these five pairs.
-/

open RHTower Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

theorem cosh_log {t : ℝ} (ht : 0 < t) : Real.cosh (Real.log t) = (t + t⁻¹) / 2 := by
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log ht]

/-- `ω(2 log r) = r⁻¹ / (1 − r⁻⁴)`. -/
theorem archLevyDensity_two_mul_log {r : ℝ} (hr : 0 < r) :
    archLevyDensity (2 * Real.log r) = r⁻¹ / (1 - (r ^ 4)⁻¹) := by
  unfold archLevyDensity
  rw [show -(2 * Real.log r) / 2 = -Real.log r by ring,
    show -2 * (2 * Real.log r) = -Real.log (r ^ 4) by rw [Real.log_pow]; push_cast; ring,
    Real.exp_neg, Real.exp_neg, Real.exp_log hr, Real.exp_log (by positivity)]

/-- **Closed form on the lattice.** For `a, b > 0` with `ab > 1`,
`k_arch(−log a, log b) = (4(ab)² − (a−1)(b−1)((ab)²−1)) / (4√(ab)((ab)²−1))`. -/
theorem archPairKernel_neg_log_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : 1 < a * b) :
    archPairKernel (-Real.log a) (Real.log b) =
      (4 * (a * b) ^ 2 - (a - 1) * (b - 1) * ((a * b) ^ 2 - 1)) /
        (4 * Real.sqrt (a * b) * ((a * b) ^ 2 - 1)) := by
  set p := Real.sqrt a with hp_def
  set q := Real.sqrt b with hq_def
  have hp : 0 < p := Real.sqrt_pos.mpr ha
  have hq : 0 < q := Real.sqrt_pos.mpr hb
  have hpa : p ^ 2 = a := Real.sq_sqrt ha.le
  have hqb : q ^ 2 = b := Real.sq_sqrt hb.le
  have hla : Real.log a = 2 * Real.log p := by rw [← hpa, Real.log_pow]; push_cast; ring
  have hlb : Real.log b = 2 * Real.log q := by rw [← hqb, Real.log_pow]; push_cast; ring
  have hpq0 : 0 < p * q := mul_pos hp hq
  have hsq : Real.sqrt (a * b) = p * q := by rw [Real.sqrt_mul ha.le]
  have hpq : 1 < p * q := by
    have h2 : (p * q) ^ 2 = a * b := by rw [mul_pow, hpa, hqb]
    nlinarith
  have hlog : 0 < Real.log (p * q) := Real.log_pos hpq
  have hxy : -Real.log a < Real.log b := by
    rw [hla, hlb, Real.log_mul hp.ne' hq.ne'] at *
    linarith
  rw [archPairKernel_eq_of_lt hxy, hla, hlb,
    show 2 * Real.log q - -(2 * Real.log p) = 2 * Real.log (p * q) by
      rw [Real.log_mul hp.ne' hq.ne']; ring,
    show (-(2 * Real.log p) + 2 * Real.log q) / 2 = Real.log (q / p) by
      rw [Real.log_div hq.ne' hp.ne']; ring,
    show 2 * Real.log (p * q) / 2 = Real.log (p * q) by ring,
    archLevyDensity_two_mul_log hpq0, cosh_log (div_pos hq hp), cosh_log hpq0, hsq, ← hpa, ← hqb]
  have h4 : (p * q) ^ 4 - 1 ≠ 0 := by
    have : 1 < (p * q) ^ 4 := one_lt_pow₀ hpq (by norm_num)
    linarith
  have h4' : 1 - ((p * q) ^ 4)⁻¹ ≠ 0 := by
    have : ((p * q) ^ 4)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hpq (by norm_num))
    linarith
  have h5 : (p ^ 2 * q ^ 2) ^ 2 - 1 ≠ 0 := by
    have : (p ^ 2 * q ^ 2) ^ 2 = (p * q) ^ 4 := by ring
    rw [this]; exact h4
  -- clear the three small denominators separately, then combine
  have eω : (p * q)⁻¹ / (1 - ((p * q) ^ 4)⁻¹) = (p * q) ^ 3 / ((p * q) ^ 4 - 1) := by
    rw [div_eq_div_iff h4' h4]
    have h1 : (p * q)⁻¹ * (p * q) ^ 4 = (p * q) ^ 3 := by
      rw [show (p * q) ^ 4 = (p * q) * (p * q) ^ 3 by ring, ← mul_assoc,
        inv_mul_cancel₀ hpq0.ne', one_mul]
    have h2 : (p * q) ^ 3 * ((p * q) ^ 4)⁻¹ = (p * q)⁻¹ := by
      rw [show (p * q) ^ 4 = (p * q) ^ 3 * (p * q) by ring, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero 3 hpq0.ne'), one_mul]
    rw [mul_sub, mul_one, h1, mul_sub, mul_one, h2]
  have ec1 : (q / p + (q / p)⁻¹) / 2 = (p ^ 2 + q ^ 2) / (2 * (p * q)) := by
    rw [inv_div, div_add_div _ _ hp.ne' hq.ne', div_div]
    congr 1 <;> ring
  have ec2' : p * q + (p * q)⁻¹ = ((p * q) ^ 2 + 1) / (p * q) := by
    rw [eq_div_iff hpq0.ne', add_mul, inv_mul_cancel₀ hpq0.ne']
    ring
  have ec2 : (p * q + (p * q)⁻¹) / 2 = ((p * q) ^ 2 + 1) / (2 * (p * q)) := by
    rw [ec2', div_div]
    congr 1
    ring
  have e3 : ((p ^ 2 + q ^ 2) / (2 * (p * q)) - ((p * q) ^ 2 + 1) / (2 * (p * q))) / 2 =
      (p ^ 2 + q ^ 2 - (p * q) ^ 2 - 1) / (4 * (p * q)) := by
    rw [← sub_div, div_div]
    congr 1 <;> ring
  rw [eω, ec1, ec2, e3]
  have h4pq : (4 : ℝ) * (p * q) ≠ 0 := mul_ne_zero (by norm_num) hpq0.ne'
  have hden : (4 * (p * q) * ((p ^ 2 * q ^ 2) ^ 2 - 1)) ≠ 0 := mul_ne_zero h4pq h5
  rw [div_add_div _ _ h4 h4pq, div_eq_div_iff (mul_ne_zero h4 h4pq) hden]
  ring

/-- The lattice crossing pair `(−log a, log b)` of positive integers with `ab ≥ 2` has positive
archimedean kernel, that is negative conductance, iff `(a−1)(b−1)((ab)²−1) < 4(ab)²`. -/
theorem archPairKernel_neg_log_log_pos_iff {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 2 ≤ a * b) :
    0 < archPairKernel (-Real.log a) (Real.log b) ↔
      (a - 1) * (b - 1) * ((a * b) ^ 2 - 1) < 4 * (a * b) ^ 2 := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab' : (1 : ℝ) < a * b := by exact_mod_cast (by omega : 1 < a * b)
  have hN : 1 ≤ (a * b) ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [archPairKernel_neg_log_log ha' hb' hab']
  have hden : 0 < 4 * Real.sqrt ((a : ℝ) * b) * (((a : ℝ) * b) ^ 2 - 1) := by
    have : (1 : ℝ) < ((a : ℝ) * b) ^ 2 := one_lt_pow₀ hab' (by norm_num)
    have : 0 < Real.sqrt ((a : ℝ) * b) := Real.sqrt_pos.mpr (by positivity)
    positivity
  rw [div_pos_iff_of_pos_right hden]
  have key : (((a - 1) * (b - 1) * ((a * b) ^ 2 - 1) : ℕ) : ℝ) =
      ((a : ℝ) - 1) * ((b : ℝ) - 1) * (((a : ℝ) * b) ^ 2 - 1) := by
    push_cast [Nat.cast_sub ha, Nat.cast_sub hb, Nat.cast_sub hN]
    ring
  rw [← Nat.cast_lt (α := ℝ), key]
  push_cast
  constructor <;> intro h <;> linarith

/-- The axis pairs `(0, log b) = (−log 1, log b)` always have positive kernel: there is no
variance term to pay the archimedean jump. -/
theorem archPairKernel_zero_pos {y : ℝ} (hy : 0 < y) : 0 < archPairKernel 0 y := by
  unfold archPairKernel
  rw [zero_sub, abs_neg, abs_of_pos hy, zero_div, Real.sinh_zero, zero_mul, add_zero]
  exact archLevyDensity_pos hy

/-- **Finite classification.** For `a, b ≥ 2`, `(a−1)(b−1)((ab)²−1) < 4(ab)²` holds exactly for
the pairs `(2,2), (2,3), (3,2), (2,4), (4,2), (2,5), (5,2), (3,3)`. -/
theorem latticeCrossing_inequality_iff {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (a - 1) * (b - 1) * ((a * b) ^ 2 - 1) < 4 * (a * b) ^ 2 ↔
      (a = 2 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
        (a = 2 ∧ b = 5) ∨ (a = 5 ∧ b = 2) ∨ (a = 3 ∧ b = 3) := by
  constructor
  · intro h
    have h4 : 4 ≤ a * b := by nlinarith
    have hN : 16 ≤ (a * b) ^ 2 := by nlinarith
    set N := (a * b) ^ 2 with hN_def
    set X := (a - 1) * (b - 1) * (N - 1) with hX_def
    have h5 : (a - 1) * (b - 1) ≤ 5 := by
      by_contra hc
      have hc6 : 6 ≤ (a - 1) * (b - 1) := not_le.mp hc
      have : 6 * (N - 1) ≤ X := by
        rw [hX_def]; exact Nat.mul_le_mul_right _ hc6
      omega
    have ha6 : a ≤ 6 := by
      have : a - 1 ≤ (a - 1) * (b - 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hb6 : b ≤ 6 := by
      have : b - 1 ≤ (a - 1) * (b - 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [hX_def, hN_def] at h
    interval_cases a <;> interval_cases b <;> revert h <;> norm_num
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- **The negative lattice crossing pairs.** For integers `a, b ≥ 2` the pair `(−log a, log b)`
has negative archimedean conductance in an odd gauge iff `{a, b}` is one of
`{2,2}, {2,3}, {2,4}, {2,5}, {3,3}`. -/
theorem archPairKernel_neg_log_log_pos_iff_of_two_le {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    0 < archPairKernel (-Real.log a) (Real.log b) ↔
      (a = 2 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
        (a = 2 ∧ b = 5) ∨ (a = 5 ∧ b = 2) ∨ (a = 3 ∧ b = 3) := by
  rw [archPairKernel_neg_log_log_pos_iff (by omega) (by omega) (by nlinarith)]
  exact latticeCrossing_inequality_iff ha hb

/-- Beyond the five pairs every lattice crossing pair of integers `≥ 2` has positive conductance:
`k_arch(−log a, log b) < 0` once `(a−1)(b−1) ≥ 6`, or more generally outside the list. -/
theorem archPairKernel_neg_log_log_neg_of_six_le {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h6 : 6 ≤ (a - 1) * (b - 1)) : archPairKernel (-Real.log a) (Real.log b) < 0 := by
  have hab : 2 ≤ a * b := by nlinarith
  have hne : archPairKernel (-Real.log a) (Real.log b) ≠ 0 := by
    intro h0
    have ha' : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    have hb' : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hab' : (1 : ℝ) < a * b := by exact_mod_cast (by omega : 1 < a * b)
    rw [archPairKernel_neg_log_log ha' hb' hab', div_eq_zero_iff] at h0
    have hden : 4 * Real.sqrt ((a : ℝ) * b) * (((a : ℝ) * b) ^ 2 - 1) ≠ 0 := by
      have : (1 : ℝ) < ((a : ℝ) * b) ^ 2 := one_lt_pow₀ hab' (by norm_num)
      have : 0 < Real.sqrt ((a : ℝ) * b) := Real.sqrt_pos.mpr (by positivity)
      positivity
    rcases h0 with h0 | h0
    · -- the numerator cannot vanish: `(a−1)(b−1)((ab)²−1) = 4(ab)²` has no solutions here
      have hN : 1 ≤ (a * b) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have key : (((a - 1) * (b - 1) * ((a * b) ^ 2 - 1) : ℕ) : ℝ) =
          ((a : ℝ) - 1) * ((b : ℝ) - 1) * (((a : ℝ) * b) ^ 2 - 1) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub (by omega : 1 ≤ b),
          Nat.cast_sub hN]
        ring
      have heq : (a - 1) * (b - 1) * ((a * b) ^ 2 - 1) = 4 * (a * b) ^ 2 := by
        have : (((a - 1) * (b - 1) * ((a * b) ^ 2 - 1) : ℕ) : ℝ) = ((4 * (a * b) ^ 2 : ℕ) : ℝ) := by
          rw [key]; push_cast; linarith
        exact_mod_cast this
      have h4 : 4 ≤ a * b := Nat.mul_le_mul ha hb
      have h16 : 16 ≤ (a * b) ^ 2 := by
        have := Nat.pow_le_pow_left h4 2
        simpa using this
      set N := (a * b) ^ 2 with hN_def
      have : 6 * (N - 1) ≤ (a - 1) * (b - 1) * (N - 1) := Nat.mul_le_mul_right _ h6
      omega
    · exact hden h0
  have hnotpos : ¬ 0 < archPairKernel (-Real.log a) (Real.log b) := by
    rw [archPairKernel_neg_log_log_pos_iff (by omega) (by omega) hab]
    intro h
    have h4 : 4 ≤ a * b := Nat.mul_le_mul ha hb
    have h16 : 16 ≤ (a * b) ^ 2 := by
      have := Nat.pow_le_pow_left h4 2
      simpa using this
    set N := (a * b) ^ 2 with hN_def
    have : 6 * (N - 1) ≤ (a - 1) * (b - 1) * (N - 1) := Nat.mul_le_mul_right _ h6
    omega
  exact lt_of_le_of_ne (not_lt.mp hnotpos) hne

end GaloisForLFunctions.ArithmeticIncidencePositivity
