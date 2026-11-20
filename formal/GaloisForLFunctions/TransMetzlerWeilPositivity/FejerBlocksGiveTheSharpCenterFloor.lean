import GaloisForLFunctions.TransMetzlerWeilPositivity.LiouvilleTwinSelectivity

/-!
# Fejér blocks give the sharp archimedean center floor

For a finite real sequence `b₁, …, b_M`, the second differences of `1/L` are positive, so the
Toeplitz form with symbol `1/|n - j|` is a positive combination of Fejér block forms
`Σ_m (b_{m-L+1} + ⋯ + b_m)²`. Summation by parts gives the exact identity

`(3/2) Σ b_n² + Σ_{n ≠ j} b_n b_j / |n - j| - (Σ b_n)² / (M + 1)
  = Σ_{L=2}^{M} Δ²(1/L) · T_L(b) + (1/M - 1/(M + 1)) · T_{M+1}(b)`,

where `T_L(b) = Σ_{n,j} b_n b_j (L - |n - j|)⁺` is a Fejér block form. Hence the Toeplitz form is
at least `-(3/2) Σ b_n²`. The Hilbert form `Σ b_n b_j/(n + j) = ∫₀¹ t (Σ b_n t^{n-1})² dt` is
nonnegative, and in pole gauge `b_n = √n x_n` the archimedean center kernel is half the sum of the
two kernels, so its quadratic form is at least `-Σ n x_n²`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open RenormalizedArithmeticPotentialTheory

/-! ### 1. Fejér block forms -/

/-- The Fejér block form `T_L(b) = Σ_{n,j ≤ M} b_n b_j (L - |n - j|)⁺`. -/
def fejerBlockForm (M L : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, b n * b j * ((L - (max n j - min n j) : ℕ) : ℝ)

/-- Each Fejér block form is a sum of squares of window sums:
`T_L(b) = Σ_m (Σ_{m - L < n ≤ m} b_n)²`. -/
theorem fejerBlockForm_eq_sum_sq (M L : ℕ) (b : ℕ → ℝ) :
    fejerBlockForm M L b = ∑ m ∈ range (M + L),
      (∑ n ∈ Icc 1 M, b n * (if n ≤ m ∧ m < n + L then 1 else 0)) ^ 2 := by
  have hcount : ∀ n ∈ Icc 1 M, ∀ j ∈ Icc 1 M,
      ((L - (max n j - min n j) : ℕ) : ℝ) = ∑ m ∈ range (M + L),
        (if n ≤ m ∧ m < n + L then (1 : ℝ) else 0) * (if j ≤ m ∧ m < j + L then 1 else 0) := by
    intro n hn j hj
    have hnM := (mem_Icc.mp hn).2
    have hjM := (mem_Icc.mp hj).2
    have hfilt : (range (M + L)).filter (fun m => (n ≤ m ∧ m < n + L) ∧ (j ≤ m ∧ m < j + L)) =
        Ico (max n j) (min n j + L) := by
      ext m
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    have hprod : ∀ m ∈ range (M + L),
        (if n ≤ m ∧ m < n + L then (1 : ℝ) else 0) * (if j ≤ m ∧ m < j + L then 1 else 0) =
          if (n ≤ m ∧ m < n + L) ∧ (j ≤ m ∧ m < j + L) then 1 else 0 := by
      intro m _
      by_cases h1 : n ≤ m ∧ m < n + L <;> by_cases h2 : j ≤ m ∧ m < j + L <;> simp [h1, h2]
    rw [sum_congr rfl hprod, sum_boole, hfilt, Nat.card_Ico]
    congr 1
    omega
  unfold fejerBlockForm
  calc _ = ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, ∑ m ∈ range (M + L),
        (b n * (if n ≤ m ∧ m < n + L then 1 else 0)) *
          (b j * (if j ≤ m ∧ m < j + L then 1 else 0)) := by
        refine sum_congr rfl fun n hn => sum_congr rfl fun j hj => ?_
        rw [hcount n hn j hj, mul_sum]
        exact sum_congr rfl fun m _ => by ring
    _ = ∑ n ∈ Icc 1 M, ∑ m ∈ range (M + L), ∑ j ∈ Icc 1 M,
        (b n * (if n ≤ m ∧ m < n + L then 1 else 0)) *
          (b j * (if j ≤ m ∧ m < j + L then 1 else 0)) :=
        sum_congr rfl fun n _ => sum_comm
    _ = ∑ m ∈ range (M + L), ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
        (b n * (if n ≤ m ∧ m < n + L then 1 else 0)) *
          (b j * (if j ≤ m ∧ m < j + L then 1 else 0)) := sum_comm
    _ = _ := sum_congr rfl fun m _ => by rw [sq, sum_mul_sum]

theorem fejerBlockForm_nonneg (M L : ℕ) (b : ℕ → ℝ) : 0 ≤ fejerBlockForm M L b := by
  rw [fejerBlockForm_eq_sum_sq]
  exact sum_nonneg fun _ _ => sq_nonneg _

/-! ### 2. Second differences of `1/L` -/

/-- The second difference `1/(L-1) - 2/L + 1/(L+1)` of `1/L`. -/
def fejerWeight (L : ℕ) : ℝ := 1 / ((L : ℝ) - 1) - 2 / L + 1 / ((L : ℝ) + 1)

theorem fejerWeight_eq {L : ℕ} (hL : 2 ≤ L) :
    fejerWeight L = 2 / (((L : ℝ) - 1) * L * ((L : ℝ) + 1)) := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (L : ℝ) - 1 ≠ 0 := by linarith only [hL']
  have h2 : (L : ℝ) ≠ 0 := by linarith only [hL']
  have h3 : (L : ℝ) + 1 ≠ 0 := by linarith only [hL']
  unfold fejerWeight
  field_simp
  ring

theorem fejerWeight_pos {L : ℕ} (hL : 2 ≤ L) : 0 < fejerWeight L := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  rw [fejerWeight_eq hL]
  apply div_pos two_pos
  apply mul_pos (mul_pos _ _) _ <;> linarith only [hL']

/-- Fejér-summed coefficient of lag `d`:
`Σ_{L=2}^{M} Δ²(1/L) (L - d)⁺ + (1/M - 1/(M + 1)) (M + 1 - d)⁺`. -/
def fejerLagCoefficient (M d : ℕ) : ℝ :=
  ∑ L ∈ Icc 2 M, fejerWeight L * ((L - d : ℕ) : ℝ) +
    (1 / (M : ℝ) - 1 / ((M : ℝ) + 1)) * ((M + 1 - d : ℕ) : ℝ)

/-- Summation by parts: the Fejér-summed coefficient of lag `d ≤ M` is `1/d - 1/(M + 1)` for
`d ≥ 1` and `3/2 - 1/(M + 1)` for `d = 0`. -/
theorem fejerLagCoefficient_eq {M d : ℕ} (hM : 1 ≤ M) (hd : d ≤ M) :
    fejerLagCoefficient M d = (if d = 0 then 3 / 2 else 1 / (d : ℝ)) - 1 / ((M : ℝ) + 1) := by
  induction M, (show max d 1 ≤ M from max_le hd hM) using Nat.le_induction with
  | base =>
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · norm_num [fejerLagCoefficient]
      · have hmax : max d 1 = d := max_eq_left hd0
        rw [hmax]
        have hzero : ∑ L ∈ Icc 2 d, fejerWeight L * ((L - d : ℕ) : ℝ) = 0 :=
          sum_eq_zero fun L hL => by
            rw [Nat.sub_eq_zero_of_le (mem_Icc.mp hL).2, Nat.cast_zero, mul_zero]
        rw [fejerLagCoefficient, hzero, zero_add, if_neg hd0.ne',
          show d + 1 - d = 1 by omega, Nat.cast_one, mul_one]
  | succ M hle ih =>
      have hdM : d ≤ M := (le_max_left d 1).trans hle
      have hM1 : 1 ≤ M := (le_max_right d 1).trans hle
      have ih' := ih hM1 hdM
      have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
      have hsplit : Icc 2 (M + 1) = insert (M + 1) (Icc 2 M) := by
        ext L; simp only [mem_Icc, mem_insert]; omega
      have hnot : M + 1 ∉ Icc 2 M := by simp only [mem_Icc]; omega
      unfold fejerLagCoefficient at ih' ⊢
      rw [hsplit, sum_insert hnot]
      have hc1 : ((M + 1 - d : ℕ) : ℝ) = (M : ℝ) + 1 - d := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hc2 : ((M + 1 + 1 - d : ℕ) : ℝ) = (M : ℝ) + 2 - d := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hc1] at ih'
      rw [hc1, hc2]
      have hw : fejerWeight (M + 1) = 1 / (M : ℝ) - 2 / ((M : ℝ) + 1) + 1 / ((M : ℝ) + 2) := by
        unfold fejerWeight; push_cast; ring_nf
      rw [hw]
      push_cast
      have h0 : (M : ℝ) ≠ 0 := by linarith only [hM']
      have h1 : (M : ℝ) + 1 ≠ 0 := by linarith only [hM']
      have h2 : (M : ℝ) + 1 + 1 ≠ 0 := by linarith only [hM']
      have h2' : (M : ℝ) + 2 ≠ 0 := by linarith only [hM']
      have key : ∑ L ∈ Icc 2 M, fejerWeight L * ((L - d : ℕ) : ℝ) =
          (if d = 0 then 3 / 2 else 1 / (d : ℝ)) - 1 / ((M : ℝ) + 1) -
            (1 / (M : ℝ) - 1 / ((M : ℝ) + 1)) * ((M : ℝ) + 1 - d) := by
        linarith only [ih']
      rw [key]
      field_simp
      ring

/-! ### 3. The exact Fejér identity and the Toeplitz floor -/

private theorem sum_sum_ite_diag (M : ℕ) (a : ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, (if n = j then a n else f n j) =
      ∑ n ∈ Icc 1 M, a n + ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, (if n = j then 0 else f n j) := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hsplit : ∀ j ∈ Icc 1 M, (if n = j then a n else f n j) =
      (if n = j then a n else 0) + (if n = j then 0 else f n j) := by
    intro j _; split_ifs <;> simp
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_ite_eq, if_pos hn]

/-- **Exact Fejér identity.** For every `M` and every real `b`,
`(3/2) Σ b_n² + Σ_{n ≠ j} b_n b_j/|n - j| - (Σ b_n)²/(M + 1)` equals the positive combination
`Σ_{L=2}^{M} Δ²(1/L) T_L(b) + (1/M - 1/(M + 1)) T_{M+1}(b)` of Fejér block forms. -/
theorem fejer_toeplitz_identity (M : ℕ) (b : ℕ → ℝ) :
    (3 / 2) * (∑ n ∈ Icc 1 M, b n ^ 2) +
        (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / |(n : ℝ) - j|) -
        (∑ n ∈ Icc 1 M, b n) ^ 2 / ((M : ℝ) + 1) =
      ∑ L ∈ Icc 2 M, fejerWeight L * fejerBlockForm M L b +
        (1 / (M : ℝ) - 1 / ((M : ℝ) + 1)) * fejerBlockForm M (M + 1) b := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [fejerBlockForm]
  have hcoef : ∀ n ∈ Icc 1 M, ∀ j ∈ Icc 1 M,
      b n * b j * fejerLagCoefficient M (max n j - min n j) =
        (if n = j then (3 / 2) * b n ^ 2 else b n * b j / |(n : ℝ) - j|) -
          b n * b j / ((M : ℝ) + 1) := by
    intro n hn j hj
    have hnM := (mem_Icc.mp hn).2
    have hjM := (mem_Icc.mp hj).2
    rw [fejerLagCoefficient_eq hM (by omega)]
    by_cases hnj : n = j
    · subst hnj
      simp only [max_self, min_self, Nat.sub_self, if_true]
      ring
    · have hd : max n j - min n j ≠ 0 := by omega
      rw [if_neg hd, if_neg hnj]
      have hcast : ((max n j - min n j : ℕ) : ℝ) = |(n : ℝ) - j| := by
        rcases le_total n j with h | h
        · rw [max_eq_right h, min_eq_left h, Nat.cast_sub h, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
        · rw [max_eq_left h, min_eq_right h, Nat.cast_sub h,
            abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
      rw [hcast]
      ring
  have hlhs : ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, b n * b j * fejerLagCoefficient M (max n j - min n j) =
      (3 / 2) * (∑ n ∈ Icc 1 M, b n ^ 2) +
        (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / |(n : ℝ) - j|) -
        (∑ n ∈ Icc 1 M, b n) ^ 2 / ((M : ℝ) + 1) := by
    rw [sum_congr rfl fun n hn => sum_congr rfl fun j hj => hcoef n hn j hj]
    simp_rw [sum_sub_distrib]
    rw [sum_sum_ite_diag M (fun n => (3 / 2) * b n ^ 2) (fun n j => b n * b j / |(n : ℝ) - j|),
      ← mul_sum, sq, sum_mul_sum, sum_div]
    simp_rw [sum_div]
  rw [← hlhs]
  calc ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, b n * b j * fejerLagCoefficient M (max n j - min n j)
      = (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, ∑ L ∈ Icc 2 M,
          fejerWeight L * (b n * b j * ((L - (max n j - min n j) : ℕ) : ℝ))) +
        ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, (1 / (M : ℝ) - 1 / ((M : ℝ) + 1)) *
          (b n * b j * ((M + 1 - (max n j - min n j) : ℕ) : ℝ)) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun n _ => ?_
        rw [← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        unfold fejerLagCoefficient
        rw [mul_add, mul_sum]
        congr 1
        · exact sum_congr rfl fun L _ => by ring
        · ring
    _ = (∑ n ∈ Icc 1 M, ∑ L ∈ Icc 2 M, ∑ j ∈ Icc 1 M,
          fejerWeight L * (b n * b j * ((L - (max n j - min n j) : ℕ) : ℝ))) +
        ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, (1 / (M : ℝ) - 1 / ((M : ℝ) + 1)) *
          (b n * b j * ((M + 1 - (max n j - min n j) : ℕ) : ℝ)) := by
        congr 1
        exact sum_congr rfl fun n _ => sum_comm
    _ = (∑ L ∈ Icc 2 M, ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
          fejerWeight L * (b n * b j * ((L - (max n j - min n j) : ℕ) : ℝ))) +
        ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, (1 / (M : ℝ) - 1 / ((M : ℝ) + 1)) *
          (b n * b j * ((M + 1 - (max n j - min n j) : ℕ) : ℝ)) := by
        congr 1
        exact sum_comm
    _ = _ := by
        unfold fejerBlockForm
        simp only [mul_sum]

/-- **Fejér Toeplitz floor.** `(Σ b_n)²/(M + 1) ≤ (3/2) Σ b_n² + Σ_{n ≠ j} b_n b_j/|n - j|`; in
particular the Toeplitz form with symbol `1/|n - j|` is at least `-(3/2) Σ b_n²`. -/
theorem sq_sum_div_le_fejer_toeplitz (M : ℕ) (b : ℕ → ℝ) :
    (∑ n ∈ Icc 1 M, b n) ^ 2 / ((M : ℝ) + 1) ≤
      (3 / 2) * (∑ n ∈ Icc 1 M, b n ^ 2) +
        ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / |(n : ℝ) - j| := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have h := fejer_toeplitz_identity M b
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpos : 0 ≤ ∑ L ∈ Icc 2 M, fejerWeight L * fejerBlockForm M L b +
      (1 / (M : ℝ) - 1 / ((M : ℝ) + 1)) * fejerBlockForm M (M + 1) b := by
    refine add_nonneg (sum_nonneg fun L hL =>
      mul_nonneg (fejerWeight_pos (mem_Icc.mp hL).1).le (fejerBlockForm_nonneg M L b))
      (mul_nonneg ?_ (fejerBlockForm_nonneg M (M + 1) b))
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by linarith only [hM']) (by linarith only)
  linarith only [h, hpos]

theorem neg_three_halves_le_sum_inv_abs_sub (M : ℕ) (b : ℕ → ℝ) :
    -(3 / 2 : ℝ) * (∑ n ∈ Icc 1 M, b n ^ 2) ≤
      ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / |(n : ℝ) - j| := by
  have h := sq_sum_div_le_fejer_toeplitz M b
  have h0 : 0 ≤ (∑ n ∈ Icc 1 M, b n) ^ 2 / ((M : ℝ) + 1) := by positivity
  linarith only [h, h0]

/-! ### 4. The Hilbert moment form -/

/-- **Hilbert moment form.** `Σ_{n,j ≤ M} b_n b_j/(n + j) = ∫₀¹ t (Σ b_n t^{n-1})² dt ≥ 0`. -/
theorem sum_inv_add_eq_integral (M : ℕ) (b : ℕ → ℝ) :
    ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, b n * b j / ((n : ℝ) + j) =
      ∫ t in (0 : ℝ)..1, t * (∑ n ∈ Icc 1 M, b n * t ^ (n - 1)) ^ 2 := by
  have hexp : ∀ t : ℝ, t * (∑ n ∈ Icc 1 M, b n * t ^ (n - 1)) ^ 2 =
      ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, (b n * b j) * t ^ ((n - 1) + (j - 1) + 1) := fun t => by
    rw [sq, sum_mul, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [pow_succ, pow_add]
    ring
  simp_rw [hexp]
  have hi : ∀ n ∈ Icc 1 M, ∀ j ∈ Icc 1 M,
      IntervalIntegrable (fun t : ℝ => (b n * b j) * t ^ ((n - 1) + (j - 1) + 1))
        MeasureTheory.volume 0 1 :=
    fun _ _ _ _ => (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum fun n _ =>
    (continuous_finsetSum _ fun j _ => by fun_prop).intervalIntegrable _ _]
  refine sum_congr rfl fun n hn => ?_
  rw [intervalIntegral.integral_finsetSum fun j hj => hi n hn j hj]
  refine sum_congr rfl fun j hj => ?_
  have hn1 := (mem_Icc.mp hn).1
  have hj1 := (mem_Icc.mp hj).1
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have hexp_eq : (n - 1) + (j - 1) + 1 + 1 = n + j := by omega
  have hden_eq : (((n - 1) + (j - 1) + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + j := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hn1, Nat.cast_sub hj1, Nat.cast_one]
    ring
  rw [hexp_eq, hden_eq, one_pow, zero_pow (by omega : n + j ≠ 0), sub_zero]
  ring

theorem sum_inv_add_nonneg (M : ℕ) (b : ℕ → ℝ) :
    0 ≤ ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, b n * b j / ((n : ℝ) + j) := by
  rw [sum_inv_add_eq_integral]
  exact intervalIntegral.integral_nonneg zero_le_one fun t ht => mul_nonneg ht.1 (sq_nonneg _)

/-- The off-diagonal Hilbert form is at least `-Σ b_n²/(2n) ≥ -(1/2) Σ b_n²`. -/
theorem neg_half_le_sum_inv_add (M : ℕ) (b : ℕ → ℝ) :
    -(1 / 2 : ℝ) * (∑ n ∈ Icc 1 M, b n ^ 2) ≤
      ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / ((n : ℝ) + j) := by
  have hsplit : (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, b n * b j / ((n : ℝ) + j)) =
      (∑ n ∈ Icc 1 M, b n ^ 2 / (2 * (n : ℝ))) +
        ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / ((n : ℝ) + j) := by
    have h := sum_sum_ite_diag M (fun n => b n ^ 2 / (2 * (n : ℝ)))
      (fun n j => b n * b j / ((n : ℝ) + j))
    rw [← h]
    refine sum_congr rfl fun n _ => sum_congr rfl fun j _ => ?_
    split_ifs with hnj
    · subst hnj; ring
    · rfl
  have hdiag_le : (∑ n ∈ Icc 1 M, b n ^ 2 / (2 * (n : ℝ))) ≤
      (1 / 2 : ℝ) * ∑ n ∈ Icc 1 M, b n ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hdiv : 1 / (2 * (n : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith only [hn1])
    calc b n ^ 2 / (2 * (n : ℝ)) = (1 / (2 * (n : ℝ))) * b n ^ 2 := by ring
      _ ≤ (1 / 2) * b n ^ 2 := mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)
  linarith only [sum_inv_add_nonneg M b, hsplit, hdiag_le]

/-! ### 5. The sharp center floor -/

/-- **Sharp pole-gauge floor of the archimedean center kernel**:
`-Σ_{n ≤ M} n x_n² ≤ Σ_{n,j ≤ M} x_n x_j archimedeanCenterKernel n j`. With `b_n = √n x_n`, the
kernel is half the sum of the Toeplitz and Hilbert kernels, whose forms are at least
`-(3/2) Σ b_n²` and `-(1/2) Σ b_n²`. -/
theorem neg_sum_le_sum_archimedeanCenterKernel (M : ℕ) (x : ℕ → ℝ) :
    -(∑ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2) ≤
      ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j := by
  set b : ℕ → ℝ := fun n => Real.sqrt n * x n
  have hbsq : ∑ n ∈ Icc 1 M, b n ^ 2 = ∑ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 := by
    refine sum_congr rfl fun n _ => ?_
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hterm : ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j =
      (1 / 2 : ℝ) *
        ((∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / |(n : ℝ) - j|) +
          ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, if n = j then 0 else b n * b j / ((n : ℝ) + j)) := by
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    by_cases hnj : n = j
    · subst hnj
      simp [archimedeanCenterKernel_self]
    · have hn1 := (mem_Icc.mp hn).1
      have hj1 := (mem_Icc.mp hj).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
      have hsj : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hj0).ne'
      have hdiv := archimedeanCenterKernel_div_sqrt_mul hn1 hj1 hnj
      rw [if_neg hnj, if_neg hnj]
      have hker : archimedeanCenterKernel n j =
          (Real.sqrt n * Real.sqrt j) *
            ((1 / 2 : ℝ) * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j))) := by
        rw [div_eq_iff (mul_ne_zero hsn hsj)] at hdiv
        linarith only [hdiv]
      rw [hker]
      dsimp only [b]
      ring
  have h1 := neg_three_halves_le_sum_inv_abs_sub M b
  have h2 := neg_half_le_sum_inv_add M b
  rw [hterm, ← hbsq]
  linarith only [h1, h2]

#print axioms fejer_toeplitz_identity
#print axioms sq_sum_div_le_fejer_toeplitz
#print axioms sum_inv_add_eq_integral
#print axioms neg_half_le_sum_inv_add
#print axioms neg_sum_le_sum_archimedeanCenterKernel

end GaloisForLFunctions.TransMetzlerWeilPositivity
