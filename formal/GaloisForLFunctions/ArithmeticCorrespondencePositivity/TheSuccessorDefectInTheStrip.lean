import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheSuccessorIsInvisibleAtZeros

/-!
# The successor defect in the strip

The successor defect of the primes `D_Λ(s) = Σ Λ(n+1)((n+1)^{−s} − (n+2)^{−s})` is holomorphic on
`Re s > 0` and at most `|s||ζ′/ζ(1+σ)|` (`TheSuccessorIsInvisibleAtZeros`). That bound is linear in
the height. Inside the strip the defect is much smaller: each term is at most `2 x^{−σ}` (two
powers of modulus `x^{−σ}`) and at most `|s| x^{−σ−1}` (the unit step). Splitting the series at
`M ≈ |s|` and using `Λ(n) ≤ n^η/η`:

* **The head** (`sum_range_rpow_neg_le`): `Σ_{n < M} (n+1)^{−β} ≤ M^{1−β}/(1−β)` for `0 < β < 1`,
  from the concave Bernoulli inequality.
* **The strip bound** (`norm_succShiftDefect_vonMangoldt_le_rpow`). For `0 < η < σ < 1` and
  `Re s = σ`,
  `|D_Λ(s)| ≤ (4/(η(1+η−σ)) + 2/(η(σ−η))) (|s| + 1)^{1−σ+η}`.

So the regular part of the successor grows like `|t|^{1−σ+η}` along vertical lines in the strip —
the size of a Dirichlet polynomial of length `|t|` — and not linearly. It is a holomorphic function
of order one whose growth exponent decreases to `0` as `σ → 1`: the successor perturbs `−ζ′/ζ` by a
term that is small in the strip and changes none of its poles.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The concave step `q (x+1)^{q−1} ≤ (x+1)^q − x^q` for `0 < q ≤ 1`, `x ≥ 0`. -/
theorem mul_rpow_sub_one_le_rpow_sub {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    q * (x + 1) ^ (q - 1) ≤ (x + 1) ^ q - x ^ q := by
  have hx1 : 0 < x + 1 := by linarith
  -- Bernoulli: `(1 − 1/(x+1))^q ≤ 1 − q/(x+1)`
  have hb := rpow_one_add_le_one_add_mul_self (s := -(1 / (x + 1)))
    (by rw [neg_le_neg_iff, div_le_one hx1]; linarith) hq0.le hq1
  have hfrac : 1 + -(1 / (x + 1)) = x / (x + 1) := by field_simp; ring
  rw [hfrac, Real.div_rpow hx hx1.le] at hb
  have hpos := Real.rpow_pos_of_pos hx1 q
  have hsub : (x + 1) ^ (q - 1) = (x + 1) ^ q / (x + 1) := Real.rpow_sub_one hx1.ne' q
  rw [div_le_iff₀ hpos] at hb
  rw [hsub]
  have : (1 + q * -(1 / (x + 1))) * (x + 1) ^ q = (x + 1) ^ q - q * ((x + 1) ^ q / (x + 1)) := by
    field_simp
    ring
  linarith

/-- **The head of a power sum**: `Σ_{n < M} (n+1)^{−β} ≤ M^{1−β}/(1−β)` for `0 < β < 1`. -/
theorem sum_range_rpow_neg_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (M : ℕ) :
    ∑ n ∈ range M, ((n : ℝ) + 1) ^ (-β) ≤ (M : ℝ) ^ (1 - β) / (1 - β) := by
  have hq : 0 < 1 - β := by linarith
  induction M with
  | zero =>
    simp only [range_zero, sum_empty, Nat.cast_zero]
    rw [Real.zero_rpow hq.ne', zero_div]
  | succ M ih =>
    rw [sum_range_succ]
    have hstep := mul_rpow_sub_one_le_rpow_sub hq (by linarith) (Nat.cast_nonneg M)
    rw [show 1 - β - 1 = -β by ring] at hstep
    push_cast
    rw [le_div_iff₀ hq] at ih ⊢
    nlinarith

/-- One term of the prime defect is at most `2 Λ(n+1)(n+1)^{−σ}`. -/
theorem norm_succShiftTerm_le_two (a : ℕ → ℂ) (n : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖succShiftTerm a n s‖ ≤ ‖a (n + 1)‖ * (2 * ((n : ℝ) + 1) ^ (-s.re)) := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
  rw [succShiftTerm, norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos h1, Complex.norm_cpow_eq_rpow_re_of_pos h2,
    Complex.neg_re]
  have : ((n : ℝ) + 1 + 1) ^ (-s.re) ≤ ((n : ℝ) + 1) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos h1 (by linarith) (by linarith)
  linarith

/-- `Λ(n) ≤ n^η/η`. -/
theorem norm_vonMangoldtC_le (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ‖vonMangoldtC n‖ ≤ (n : ℝ) ^ η / η := by
  rw [vonMangoldtC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_rpow_div (Nat.cast_nonneg n) hη)

/-- **The successor defect in the strip**: for `0 < η < σ < 1` and `Re s = σ`,
`|D_Λ(s)| ≤ (4/(η(1+η−σ)) + 2/(η(σ−η))) (|s| + 1)^{1−σ+η}`. -/
theorem norm_succShiftDefect_vonMangoldt_le_rpow {σ η : ℝ} (hη : 0 < η) (hησ : η < σ)
    (hσ1 : σ < 1) {s : ℂ} (hs : s.re = σ) :
    ‖succShiftDefect vonMangoldtC s‖ ≤
      (4 / (η * (1 + η - σ)) + 2 / (η * (σ - η))) * (‖s‖ + 1) ^ (1 - σ + η) := by
  have hσ0 : 0 < σ := hη.trans hησ
  have hsre : 0 < s.re := hs ▸ hσ0
  set M : ℕ := ⌈‖s‖⌉₊ + 1 with hMdef
  have hM1 : 1 ≤ M := by omega
  have hMs : ‖s‖ ≤ M := by
    have := Nat.le_ceil ‖s‖
    rw [hMdef]; push_cast; linarith
  have hMs1 : (M : ℝ) ≤ ‖s‖ + 2 := by
    have := Nat.ceil_lt_add_one (norm_nonneg s)
    rw [hMdef]; push_cast; linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  -- summability of the norms of the terms
  have hsum : Summable fun n : ℕ => ‖succShiftTerm vonMangoldtC n s‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_succShiftTerm_le vonMangoldtC n hsre)
      ((summable_vonMangoldt_shift hsre).mul_left ‖s‖ |>.congr fun n => by ring)
  -- head and tail bounds
  have hhead : ∀ n : ℕ, ‖succShiftTerm vonMangoldtC n s‖ ≤ 2 / η * ((n : ℝ) + 1) ^ (-(σ - η)) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine (norm_succShiftTerm_le_two vonMangoldtC n hsre.le).trans ?_
    have hΛ := norm_vonMangoldtC_le (n + 1) hη
    push_cast at hΛ
    rw [hs]
    calc ‖vonMangoldtC (n + 1)‖ * (2 * ((n : ℝ) + 1) ^ (-σ))
        ≤ ((n : ℝ) + 1) ^ η / η * (2 * ((n : ℝ) + 1) ^ (-σ)) :=
          mul_le_mul_of_nonneg_right hΛ (by positivity)
      _ = 2 / η * ((n : ℝ) + 1) ^ (-(σ - η)) := by
          rw [show -(σ - η) = η + -σ by ring, Real.rpow_add h1]; ring
  have htail : ∀ k : ℕ, ‖succShiftTerm vonMangoldtC (k + M) s‖ ≤
      ‖s‖ / η * ((M : ℝ) + 1 + (k : ℝ)) ^ ((η - σ) - 1) := by
    intro k
    have h1 : (0 : ℝ) < (M : ℝ) + 1 + k := by positivity
    refine (norm_succShiftTerm_le vonMangoldtC (k + M) hsre).trans ?_
    have hΛ := norm_vonMangoldtC_le (k + M + 1) hη
    have hcast : ((k + M : ℕ) : ℝ) + 1 = (M : ℝ) + 1 + k := by push_cast; ring
    push_cast at hΛ
    rw [hcast, hs]
    rw [show ((k : ℝ) + (M : ℝ) + 1) = (M : ℝ) + 1 + k by ring] at hΛ
    calc ‖vonMangoldtC (k + M + 1)‖ * (‖s‖ * ((M : ℝ) + 1 + k) ^ (-σ - 1))
        ≤ ((M : ℝ) + 1 + k) ^ η / η * (‖s‖ * ((M : ℝ) + 1 + k) ^ (-σ - 1)) :=
          mul_le_mul_of_nonneg_right hΛ (by positivity)
      _ = ‖s‖ / η * ((M : ℝ) + 1 + (k : ℝ)) ^ ((η - σ) - 1) := by
          rw [show (η - σ) - 1 = η + (-σ - 1) by ring, Real.rpow_add h1]; ring
  -- the two pieces
  have hHead : ∑ n ∈ range M, ‖succShiftTerm vonMangoldtC n s‖ ≤
      2 / η * ((M : ℝ) ^ (1 - (σ - η)) / (1 - (σ - η))) := by
    calc ∑ n ∈ range M, ‖succShiftTerm vonMangoldtC n s‖
        ≤ ∑ n ∈ range M, 2 / η * ((n : ℝ) + 1) ^ (-(σ - η)) := sum_le_sum fun n _ => hhead n
      _ = 2 / η * ∑ n ∈ range M, ((n : ℝ) + 1) ^ (-(σ - η)) := by rw [mul_sum]
      _ ≤ 2 / η * ((M : ℝ) ^ (1 - (σ - η)) / (1 - (σ - η))) :=
          mul_le_mul_of_nonneg_left (sum_range_rpow_neg_le (by linarith) (by linarith) M)
            (div_nonneg (by norm_num) hη.le)
  have hTail : ∑' k : ℕ, ‖succShiftTerm vonMangoldtC (k + M) s‖ ≤
      ‖s‖ / η * ((M : ℝ) ^ (η - σ) / (-(η - σ))) := by
    have hs2 := HTGeometry.summable_shift_rpow (q := η - σ) (by linarith) M
    refine le_trans (((summable_nat_add_iff M).2 hsum).tsum_le_tsum htail (hs2.mul_left _)) ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (HTGeometry.tsum_shift_rpow_le (by linarith) hM1)
      (div_nonneg (norm_nonneg _) hη.le)
  -- assemble
  have hsplit := hsum.sum_add_tsum_nat_add M
  have hD : ‖succShiftDefect vonMangoldtC s‖ ≤ ∑' n, ‖succShiftTerm vonMangoldtC n s‖ :=
    norm_tsum_le_tsum_norm hsum
  rw [← hsplit] at hD
  -- `M ≤ 2(|s| + 1)` and the exponent `e = 1 − σ + η` lies in `(0, 1)`
  set e := 1 - σ + η with he_def
  have he0 : 0 < e := by rw [he_def]; linarith
  have he1 : e ≤ 1 := by rw [he_def]; linarith
  have hs1 : (0 : ℝ) < ‖s‖ + 1 := by positivity
  have hpowM : (M : ℝ) ^ e ≤ 2 * (‖s‖ + 1) ^ e := by
    have h1 : (M : ℝ) ^ e ≤ (2 * (‖s‖ + 1)) ^ e :=
      Real.rpow_le_rpow hM0.le (by linarith [norm_nonneg s]) he0.le
    have h2 : (2 : ℝ) ^ e ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he1
    rw [Real.mul_rpow (by norm_num) hs1.le] at h1
    nlinarith [Real.rpow_pos_of_pos hs1 e]
  -- the tail: `|s| M^{η−σ} ≤ M^{1+η−σ} = M^e`
  have htail' : ‖s‖ * (M : ℝ) ^ (η - σ) ≤ (M : ℝ) ^ e := by
    have : (M : ℝ) ^ e = (M : ℝ) * (M : ℝ) ^ (η - σ) := by
      rw [he_def, show 1 - σ + η = 1 + (η - σ) by ring, Real.rpow_add hM0, Real.rpow_one]
    rw [this]
    exact mul_le_mul_of_nonneg_right hMs (Real.rpow_pos_of_pos hM0 _).le
  have hHead' : ∑ n ∈ range M, ‖succShiftTerm vonMangoldtC n s‖ ≤
      4 / (η * (1 + η - σ)) * (‖s‖ + 1) ^ e := by
    refine hHead.trans ?_
    rw [show 1 - (σ - η) = e by rw [he_def]; ring]
    have hden : 0 < 1 + η - σ := by linarith
    rw [show 1 + η - σ = e by rw [he_def]; ring] at hden ⊢
    calc 2 / η * ((M : ℝ) ^ e / e) ≤ 2 / η * (2 * (‖s‖ + 1) ^ e / e) := by gcongr
      _ = 4 / (η * e) * (‖s‖ + 1) ^ e := by field_simp; ring
  have hTail' : ∑' k : ℕ, ‖succShiftTerm vonMangoldtC (k + M) s‖ ≤
      2 / (η * (σ - η)) * (‖s‖ + 1) ^ e := by
    refine hTail.trans ?_
    have hd : 0 < σ - η := by linarith
    calc ‖s‖ / η * ((M : ℝ) ^ (η - σ) / (-(η - σ)))
        = (‖s‖ * (M : ℝ) ^ (η - σ)) / (η * (σ - η)) := by rw [neg_sub, div_mul_div_comm]
      _ ≤ (2 * (‖s‖ + 1) ^ e) / (η * (σ - η)) :=
          div_le_div_of_nonneg_right (htail'.trans hpowM) (mul_pos hη hd).le
      _ = 2 / (η * (σ - η)) * (‖s‖ + 1) ^ e := by ring
  calc ‖succShiftDefect vonMangoldtC s‖
      ≤ ∑ n ∈ range M, ‖succShiftTerm vonMangoldtC n s‖ +
          ∑' k : ℕ, ‖succShiftTerm vonMangoldtC (k + M) s‖ := hD
    _ ≤ 4 / (η * (1 + η - σ)) * (‖s‖ + 1) ^ e + 2 / (η * (σ - η)) * (‖s‖ + 1) ^ e :=
        add_le_add hHead' hTail'
    _ = (4 / (η * (1 + η - σ)) + 2 / (η * (σ - η))) * (‖s‖ + 1) ^ e := by ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
