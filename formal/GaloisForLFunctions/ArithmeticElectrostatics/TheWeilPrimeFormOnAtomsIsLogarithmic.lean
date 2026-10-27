import GaloisForLFunctions.ArithmeticElectrostatics.TheArithmeticPointCarriesTheDivergence

/-!
# The Weil prime form on atoms is logarithmic

At atomic resolution — tests concentrated at the points `log n`, `1 ≤ n ≤ N` — the prime side of
Weil's form is the quadratic form of the kernel `P(m, n) = Λ(n/m)(n/m)^{−1/2}` on pairs `m ∣ n`,
`m ≠ n` (`weilPrimeKernel`), the renormalized limit of the gcd-twisted torsion energies. Weil
positivity at that resolution asks the archimedean self-energy of the atoms to pay this form. This
file computes the size of what must be paid.

* **Upper bound** (`atomicWeilForm_le`): `Σ x_m x_n P(m, n) ≤ (2 log N + log 4 + 4) Σ x_n²`. Schur
  test with weights `n^{−1/2}`: up the tower the row is `Σ_{t ≤ N/m} Λ(t)/t ≤ log N + log 4 + 4`
  (Mertens), down the tower it is `Σ_{t ∣ m} Λ(t) = log m`.
* **Lower bound at the arithmetic point** (`sqrt_le_of_atomicWeilForm_le`,
  `log_two_mul_le_sq_of_atomicWeilForm_le`): the atom at `log 1 = 0` meets every prime-power atom
  with weight `Λ(n)/√n`; if `κ` bounds the form, then `κ² ≥ Σ_{2 ≤ n ≤ N} Λ(n)²/n ≥ log 2 (log N − log 4 − 4)`.

So the counterterm the archimedean place must supply at atomic resolution `N` grows like a
logarithm, as the torsion counterterm does (`TheTorsionCountertermIsLogarithmic`), and in both the
divergence is forced by the arithmetic point. The archimedean self-energy of an atom of width `ε`
is `log(1/ε) + O(1)`; the two renormalizations can only match at `ε ≍ N^{−c}`, the scale of the
atoms themselves.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.ArithmeticElectrostatics

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The **atomic Weil prime form** on the atoms `log n`, `1 ≤ n ≤ N`. -/
def atomicWeilForm (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * weilPrimeKernel m n

theorem weilPrimeKernel_comm (m n : ℕ) : weilPrimeKernel m n = weilPrimeKernel n m := by
  unfold weilPrimeKernel
  by_cases h1 : m ∣ n ∧ m ≠ n
  · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
    rw [if_pos h1, if_neg h2, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : n ∣ m ∧ n ≠ m
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_neg h1]

theorem weilPrimeKernel_nonneg (m n : ℕ) : 0 ≤ weilPrimeKernel m n := by
  unfold weilPrimeKernel
  split_ifs <;> first | exact div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _) | exact le_rfl

theorem weilPrimeKernel_self (n : ℕ) : weilPrimeKernel n n = 0 := by
  simp [weilPrimeKernel]

/-- The kernel against the arithmetic point: `P(1, n) = Λ(n)/√n` for `n ≥ 2`. -/
theorem weilPrimeKernel_one_left {n : ℕ} (hn : 2 ≤ n) :
    weilPrimeKernel 1 n = Λ n / Real.sqrt n := by
  rw [weilPrimeKernel, if_pos ⟨one_dvd n, by omega⟩, Nat.div_one]

/-- The Schur-weighted kernel `P(m, n) √(m/n)`: `Λ(t)/t` up the tower, `Λ(t)` down the tower. -/
theorem weilPrimeKernel_mul_sqrt_ratio {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) =
      (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) +
        (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) := by
  unfold weilPrimeKernel
  by_cases h1 : m ∣ n ∧ m ≠ n
  · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
    rw [if_pos h1, if_pos h1, if_neg h2, add_zero]
    have hcast : ((n / m : ℕ) : ℝ) = (n : ℝ) / m := Nat.cast_div h1.1 (by exact_mod_cast hm.ne')
    have ht : (0 : ℝ) < ((n / m : ℕ) : ℝ) := by rw [hcast]; positivity
    rw [show (m : ℝ) / n = 1 / ((n / m : ℕ) : ℝ) by rw [hcast]; field_simp, Real.sqrt_div' 1 ht.le,
      Real.sqrt_one]
    have hs : Real.sqrt ((n / m : ℕ) : ℝ) * Real.sqrt ((n / m : ℕ) : ℝ) = ((n / m : ℕ) : ℝ) :=
      Real.mul_self_sqrt ht.le
    have hs0 : Real.sqrt ((n / m : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    field_simp
    rw [Real.sq_sqrt ht.le]
  · rw [if_neg h1, if_neg h1, zero_add]
    by_cases h2 : n ∣ m ∧ n ≠ m
    · rw [if_pos h2, if_pos h2]
      have hcast : ((m / n : ℕ) : ℝ) = (m : ℝ) / n := Nat.cast_div h2.1 (by exact_mod_cast hn.ne')
      rw [← hcast]
      have ht : (0 : ℝ) < ((m / n : ℕ) : ℝ) := by rw [hcast]; positivity
      have hs0 : Real.sqrt ((m / n : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
      field_simp
    · rw [if_neg h2, if_neg h2, zero_mul]

/-- **The row bound**: `Σ_{n ≤ N} P(m, n) √(m/n) ≤ 2 log N + log 4 + 4`. -/
theorem sum_row_weilPrimeKernel_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) ≤
      2 * Real.log N + (Real.log 4 + 4) := by
  have hN : 0 < N := lt_of_lt_of_le hm hmN
  rw [sum_congr rfl fun n hn => weilPrimeKernel_mul_sqrt_ratio hm (mem_Icc.mp hn).1,
    sum_add_distrib]
  -- up the tower
  have hup : ∑ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) ≤
      Real.log N + (Real.log 4 + 4) := by
    calc ∑ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0)
        ≤ ∑ n ∈ Icc 1 N, (if m ∣ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) := by
          refine sum_le_sum fun n _ => ?_
          by_cases h : m ∣ n
          · by_cases h' : m ≠ n
            · rw [if_pos ⟨h, h'⟩, if_pos h]
            · rw [if_neg (fun h'' => h' h''.2), if_pos h]
              exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
          · rw [if_neg (fun h'' => h h''.1), if_neg h]
      _ = ∑ t ∈ Icc 1 (N / m), Λ t / t := by
          rw [← sum_filter, filter_dvd_Icc_eq_image hm,
            sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h]
          exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm]
      _ ≤ Real.log N + (Real.log 4 + 4) := by
          have hNm : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by linarith)
          have hmert := (abs_le.mp (RHTower.Mertens.mertens_first (N / m) hNm)).2
          have hlog : Real.log ((N / m : ℕ) : ℝ) ≤ Real.log N :=
            Real.log_le_log (by exact_mod_cast hNm) (by exact_mod_cast Nat.div_le_self N m)
          linarith
  -- down the tower
  have hdown : ∑ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) ≤ Real.log N := by
    calc ∑ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0)
        ≤ ∑ n ∈ Icc 1 N, (if n ∣ m then Λ (m / n) else 0) := by
          refine sum_le_sum fun n _ => ?_
          by_cases h : n ∣ m
          · by_cases h' : n ≠ m
            · rw [if_pos ⟨h, h'⟩, if_pos h]
            · rw [if_neg (fun h'' => h' h''.2), if_pos h]; exact vonMangoldt_nonneg
          · rw [if_neg (fun h'' => h h''.1), if_neg h]
      _ = Real.log m := by
          rw [← sum_filter, filter_Icc_dvd_eq_divisors hm hmN, Nat.sum_div_divisors m (fun d => Λ d),
            vonMangoldt_sum]
      _ ≤ Real.log N := Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmN)
  linarith

/-- **Upper bound**: the atomic Weil prime form is at most `(2 log N + log 4 + 4) Σ x_n²`. -/
theorem atomicWeilForm_le (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm N x ≤ (2 * Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  set S := Icc 1 N
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => (mem_Icc.mp hn).1
  -- Schur: `2 x_m x_n ≤ x_m² √(m/n) + x_n² √(n/m)`
  have hpair : ∀ m ∈ S, ∀ n ∈ S, x m * x n * weilPrimeKernel m n ≤
      (x m ^ 2 * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n)) +
        x n ^ 2 * (weilPrimeKernel n m * Real.sqrt ((n : ℝ) / m))) / 2 := by
    intro m hm n hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos n hn
    have ha : 0 < Real.sqrt ((m : ℝ) / n) := Real.sqrt_pos.mpr (by positivity)
    have hinv : Real.sqrt ((n : ℝ) / m) = (Real.sqrt ((m : ℝ) / n))⁻¹ := by
      rw [← Real.sqrt_inv, inv_div]
    rw [weilPrimeKernel_comm n m, hinv]
    have hP := weilPrimeKernel_nonneg m n
    set a := Real.sqrt ((m : ℝ) / n)
    have key : x m ^ 2 * a + x n ^ 2 * a⁻¹ - 2 * (x m * x n) = (x m * a - x n) ^ 2 / a := by
      field_simp
      ring
    have h2 : 2 * (x m * x n) ≤ x m ^ 2 * a + x n ^ 2 * a⁻¹ := by
      have : 0 ≤ (x m * a - x n) ^ 2 / a := by positivity
      linarith
    nlinarith
  have hsym : ∑ m ∈ S, ∑ n ∈ S, x n ^ 2 * (weilPrimeKernel n m * Real.sqrt ((n : ℝ) / m)) =
      ∑ m ∈ S, ∑ n ∈ S, x m ^ 2 * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n)) := sum_comm
  calc atomicWeilForm N x
      ≤ ∑ m ∈ S, ∑ n ∈ S, (x m ^ 2 * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n)) +
          x n ^ 2 * (weilPrimeKernel n m * Real.sqrt ((n : ℝ) / m))) / 2 :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => hpair m hm n hn
    _ = ∑ m ∈ S, x m ^ 2 * ∑ n ∈ S, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) := by
        simp only [← sum_div, sum_add_distrib, hsym, mul_sum]
        ring
    _ ≤ ∑ m ∈ S, x m ^ 2 * (2 * Real.log N + (Real.log 4 + 4)) :=
        sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
          (sum_row_weilPrimeKernel_le (hpos m hm) (mem_Icc.mp hm).2) (sq_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

/-- **Lower bound at the arithmetic point**: a bound `κ` for the atomic Weil prime form on orders
`≤ N` satisfies `κ² ≥ Σ_{2 ≤ n ≤ N} Λ(n)²/n`. -/
theorem sqrt_le_of_atomicWeilForm_le {N : ℕ} (hN : 2 ≤ N) {κ : ℝ}
    (h : ∀ x : ℕ → ℝ, atomicWeilForm N x ≤ κ * ∑ n ∈ Icc 1 N, x n ^ 2) :
    ∑ n ∈ Icc 2 N, Λ n ^ 2 / n ≤ κ ^ 2 := by
  set A := ∑ n ∈ Icc 2 N, Λ n ^ 2 / n
  have hA0 : 0 ≤ A := sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  rcases hA0.eq_or_lt with hA | hA
  · rw [← hA]; exact sq_nonneg κ
  set c := 1 / Real.sqrt A
  have hc : 0 < c := by positivity
  set x : ℕ → ℝ := fun n => if n = 1 then 1 else c * Λ n / Real.sqrt n
  set S := Icc 1 N
  have h1S : 1 ∈ S := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hSe : S.erase 1 = Icc 2 N := by ext n; simp only [mem_erase, mem_Icc, S]; omega
  have hx0 : ∀ n ∈ S, 0 ≤ x n := by
    intro n _
    by_cases h1 : n = 1
    · simp [x, h1]
    · simp only [x, if_neg h1]; positivity
  have hF : ∀ m ∈ S, ∀ n ∈ S, 0 ≤ x m * x n * weilPrimeKernel m n := fun m hm n hn =>
    mul_nonneg (mul_nonneg (hx0 m hm) (hx0 n hn)) (weilPrimeKernel_nonneg m n)
  have hsqrt : ∀ n ∈ Icc 2 N, Real.sqrt n * Real.sqrt n = n := fun n _ =>
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hrow : ∀ n ∈ Icc 2 N, x 1 * x n * weilPrimeKernel 1 n = c * (Λ n ^ 2 / n) := by
    intro n hn
    have hn1 : n ≠ 1 := by have := (mem_Icc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by have := (mem_Icc.mp hn).1; exact_mod_cast (by omega : 0 < n)
    have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    simp only [x, if_pos rfl, if_neg hn1, one_mul, weilPrimeKernel_one_left (mem_Icc.mp hn).1]
    calc c * Λ n / Real.sqrt n * (Λ n / Real.sqrt n)
        = c * Λ n ^ 2 / (Real.sqrt n * Real.sqrt n) := by ring
      _ = c * (Λ n ^ 2 / n) := by rw [hsqrt n hn]; ring
  -- the form sees at least the row and the column of the arithmetic point
  have hlow : 2 * (c * A) ≤ atomicWeilForm N x := by
    rw [atomicWeilForm, ← add_sum_erase S _ h1S, ← add_sum_erase S _ h1S, hSe]
    have hcol : ∑ m ∈ Icc 2 N, x m * x 1 * weilPrimeKernel m 1 ≤
        ∑ m ∈ Icc 2 N, ∑ n ∈ S, x m * x n * weilPrimeKernel m n := by
      refine sum_le_sum fun m hm => ?_
      have hmS : m ∈ S := by rw [← hSe] at hm; exact mem_of_mem_erase hm
      exact single_le_sum (fun n hn => hF m hmS n hn) h1S
    have hcol' : ∑ m ∈ Icc 2 N, x m * x 1 * weilPrimeKernel m 1 = c * A := by
      rw [mul_sum]
      refine sum_congr rfl fun m hm => ?_
      rw [weilPrimeKernel_comm, mul_comm (x m), hrow m hm]
    rw [weilPrimeKernel_self, mul_zero, zero_add, sum_congr rfl hrow, ← mul_sum]
    linarith
  -- the mass of the test is `2`
  have hmass : ∑ n ∈ S, x n ^ 2 = 2 := by
    rw [← add_sum_erase S _ h1S, hSe]
    simp only [x, if_pos rfl, one_pow]
    have : ∑ n ∈ Icc 2 N, (if n = 1 then (1 : ℝ) else c * Λ n / Real.sqrt n) ^ 2 =
        c ^ 2 * A := by
      rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      have hn1 : n ≠ 1 := by have := (mem_Icc.mp hn).1; omega
      have hn0 : (0 : ℝ) < n := by have := (mem_Icc.mp hn).1; exact_mod_cast (by omega : 0 < n)
      rw [if_neg hn1, div_pow, mul_pow, Real.sq_sqrt hn0.le]
      ring
    rw [this]
    have hcA : c ^ 2 * A = 1 := by
      simp only [c, div_pow, one_pow, Real.sq_sqrt hA.le]
      field_simp
    linarith
  have hκ := h x
  rw [hmass] at hκ
  -- `2 c A ≤ 2 κ` with `c A = √A`
  have hcA : c * A = Real.sqrt A := by
    simp only [c]
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff (Real.sqrt_pos.mpr hA).ne',
      Real.mul_self_sqrt hA.le]
  have hsq : Real.sqrt A ≤ κ := by linarith
  calc A = Real.sqrt A ^ 2 := (Real.sq_sqrt hA.le).symm
    _ ≤ κ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2

/-- **The arithmetic point forces divergence on the prime side**: a bound `κ` for the atomic Weil
prime form on orders `≤ N` satisfies `κ² ≥ log 2 · (log N − log 4 − 4)`. -/
theorem log_two_mul_le_sq_of_atomicWeilForm_le {N : ℕ} (hN : 2 ≤ N) {κ : ℝ}
    (h : ∀ x : ℕ → ℝ, atomicWeilForm N x ≤ κ * ∑ n ∈ Icc 1 N, x n ^ 2) :
    Real.log 2 * (Real.log N - (Real.log 4 + 4)) ≤ κ ^ 2 := by
  refine le_trans ?_ (sqrt_le_of_atomicWeilForm_le hN h)
  have hmert := (abs_le.mp (RHTower.Mertens.mertens_first N (by omega))).1
  have hsplit : ∑ d ∈ Icc 1 N, Λ d / d = ∑ d ∈ Icc 2 N, Λ d / d := by
    rw [← add_sum_erase (Icc 1 N) _ (mem_Icc.mpr ⟨le_rfl, by omega⟩)]
    rw [vonMangoldt_apply_one, zero_div, zero_add]
    exact sum_congr (by ext n; simp only [mem_erase, mem_Icc]; omega) fun _ _ => rfl
  have hterm : ∀ n ∈ Icc 2 N, Real.log 2 * (Λ n / n) ≤ Λ n ^ 2 / n := fun n _ => by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (log_two_mul_le_vonMangoldt_sq n) (Nat.cast_nonneg _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc Real.log 2 * (Real.log N - (Real.log 4 + 4))
      ≤ Real.log 2 * ∑ d ∈ Icc 2 N, Λ d / d := by
        rw [← hsplit]; exact mul_le_mul_of_nonneg_left (by linarith) hlog2.le
    _ = ∑ d ∈ Icc 2 N, Real.log 2 * (Λ d / d) := mul_sum _ _ _
    _ ≤ ∑ n ∈ Icc 2 N, Λ n ^ 2 / n := sum_le_sum hterm

end GaloisForLFunctions.ArithmeticElectrostatics
