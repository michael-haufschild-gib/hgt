import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheBudgetAtTheEdge
import GaloisForLFunctions.VerifiedHeightRungs.PolyaFrequencyEntries
import GaloisForLFunctions.VerifiedHeightRungs.LiAndHausdorffEntries
import GaloisForLFunctions.BezoutValuationIncidence.PronicBezoutSplitAndPrimePowerIndecomposability

/-!
# The Riemann hypothesis through height 67

**Theorem** (`rhVerifiedThrough_sixtySeven`). Every zero of `ζ` in the strip with ordinate in `(0, 67]`
lies on the critical line.

No zero and no value of `ζ` is located. The Fejér budget at band `L = 3` on the line `Re s = 1` says
that an off-line zero at height `γ` forces

`2(2 − (4/3)(1 − e^{−3/2})) ≤ ½ log(γ/2π) + O(1/γ) − Σ_{n ≤ 20} (Λ(n)/n)(1 − (log n)/3) cos(γ log n)`.

The polynomial is bounded below at every height with no information on the phases, other than the
relation between the phases of one prime: for `p = 2, 3` the powers of `p` have phases `k γ log p`, so
all coefficients cannot pay at once, and the minimum over the phase of `p` is at phase `π`
(`family_two`, `family_three`).

Through the existing rungs this gives `PF_200` at the centre of `ξ`, all slice coefficients nonnegative
on `|t| ≤ 133/2`, and `λ_n ≥ 0` for `n ≤ 314`.
-/

open Complex
open ArithmeticFunction (vonMangoldt)
open scoped ComplexOrder

namespace GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

/-! ## The minimum over the phase of one prime -/

/-- The powers of `2`: the minimum over the phase is at phase `π`. -/
theorem family_two {A B C D u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1) (hC : 0 < C) (hD : 0 ≤ D)
    (hdisc : B ^ 2 ≤ 4 * C * (A - B - 16 * D)) :
    -A + B - C + D ≤ A * u + B * (2 * u ^ 2 - 1) + C * (4 * u ^ 3 - 3 * u) +
      D * (8 * u ^ 4 - 8 * u ^ 2 + 1) := by
  obtain ⟨v, hv⟩ : ∃ v, v = 2 * u - 1 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = A - B - 16 * D := ⟨_, rfl⟩
  have hq : 0 ≤ C * v ^ 2 + B * v + e := by
    have h1 : 0 ≤ 4 * C * (C * v ^ 2 + B * v + e) := by
      rw [← he] at hdisc
      nlinarith only [sq_nonneg (2 * C * v + B), hdisc]
    exact nonneg_of_mul_nonneg_right h1 (by positivity)
  have hu2 : u ^ 2 ≤ 1 := by nlinarith only [hu0, hu1]
  have h8 : -(16 * D) ≤ 8 * D * (u ^ 2 * (u - 1)) := by
    have h1 : u ^ 2 * (1 - u) ≤ 2 := by
      have h2 : 1 - u ≤ 2 := by linarith only [hu0]
      nlinarith only [h2, hu2, sq_nonneg u, mul_nonneg (sq_nonneg u) (by linarith only [h2] : 0 ≤ 2 - (1 - u))]
    nlinarith only [mul_le_mul_of_nonneg_left h1 hD]
  have hR : 0 ≤ A + 2 * B * (u - 1) + C * (2 * u - 1) ^ 2 + 8 * D * (u ^ 2 * (u - 1)) := by
    rw [hv, he] at hq
    nlinarith only [hq, h8]
  have hprod := mul_nonneg (by linarith only [hu0] : 0 ≤ u + 1) hR
  nlinarith only [hprod]

/-- The powers of `3`. -/
theorem family_three {E F u : ℝ} (hu0 : -1 ≤ u) (hF : 0 ≤ F) (hEF : 4 * F ≤ E) :
    -E + F ≤ E * u + F * (2 * u ^ 2 - 1) := by
  have hR : 0 ≤ E + 2 * F * (u - 1) := by nlinarith only [hu0, hF, hEF]
  have hprod := mul_nonneg (by linarith only [hu0] : 0 ≤ u + 1) hR
  nlinarith only [hprod]

/-- `x(1 − x/3)` decreases past `3/2`. -/
theorem prime_term_le {x x0 p : ℝ} (h0 : x0 ≤ x) (hx0 : 3 / 2 ≤ x0) (hp : 0 < p) :
    x / p * (1 - x / 3) ≤ x0 / p * (1 - x0 / 3) := by
  have h := mul_nonneg (sub_nonneg.2 h0) (by linarith only [h0, hx0] : 0 ≤ (x + x0) / 3 - 1)
  have e : x0 / p * (1 - x0 / 3) - x / p * (1 - x / 3) = (x - x0) * ((x + x0) / 3 - 1) / p := by
    field_simp
    ring
  have h2 : 0 ≤ x0 / p * (1 - x0 / 3) - x / p * (1 - x / 3) := by
    rw [e]
    exact div_nonneg h hp.le
  linarith only [h2]

private theorem neg_le_mul_cos {c w θ : ℝ} (h0 : 0 ≤ c) (hw : c ≤ w) :
    -w ≤ c * Real.cos θ := by
  have := Real.neg_one_le_cos θ
  nlinarith only [this, h0, hw]

/-! ## Logarithms from powers of two -/

private theorem le_log_of_two_pow_le {p : ℝ} (hp : 0 < p) {k m : ℕ} (hk : 0 < k)
    (h : (2 : ℝ) ^ m ≤ p ^ k) : (m : ℝ) / k * Real.log 2 ≤ Real.log p := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']
  linarith only [hl]

private theorem log_le_of_pow_le_two_pow {p : ℝ} (hp : 0 < p) {k m : ℕ} (hk : 0 < k)
    (h : p ^ k ≤ (2 : ℝ) ^ m) : Real.log p ≤ (m : ℝ) / k * Real.log 2 := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, le_div_iff₀ hk']
  linarith only [hl]

private theorem log3_lb : (1.09857 : ℝ) ≤ Real.log 3 := by
  have h := le_log_of_two_pow_le (p := 3) (by norm_num) (k := 53) (m := 84) (by norm_num)
    (by norm_num)
  have h2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith only [h, h2]

private theorem log3_ub : Real.log 3 ≤ 1.09872 := by
  have h := log_le_of_pow_le_two_pow (p := 3) (by norm_num) (k := 94) (m := 149) (by norm_num)
    (by norm_num)
  have h2 := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith only [h, h2]

private theorem log5_lb : (1.60909 : ℝ) ≤ Real.log 5 := by
  have h := le_log_of_two_pow_le (p := 5) (by norm_num) (k := 28) (m := 65) (by norm_num)
    (by norm_num)
  have h2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith only [h, h2]

private theorem log7_lb : (1.9452 : ℝ) ≤ Real.log 7 := by
  have h := le_log_of_two_pow_le (p := 7) (by norm_num) (k := 31) (m := 87) (by norm_num)
    (by norm_num)
  have h2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith only [h, h2]

private theorem log11_lb : (2.3971 : ℝ) ≤ Real.log 11 := by
  have h := le_log_of_two_pow_le (p := 11) (by norm_num) (k := 24) (m := 83) (by norm_num)
    (by norm_num)
  have h2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith only [h, h2]

private theorem log13_lb : (2.5646 : ℝ) ≤ Real.log 13 := by
  have h := le_log_of_two_pow_le (p := 13) (by norm_num) (k := 10) (m := 37) (by norm_num)
    (by norm_num)
  have h2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith only [h, h2]

private theorem log17_lb : (2.8328 : ℝ) ≤ Real.log 17 := by
  have h := le_log_of_two_pow_le (p := 17) (by norm_num) (k := 23) (m := 94) (by norm_num)
    (by norm_num)
  have h2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith only [h, h2]

private theorem log19_lb : (2.9406 : ℝ) ≤ Real.log 19 := by
  have h := le_log_of_two_pow_le (p := 19) (by norm_num) (k := 33) (m := 140) (by norm_num)
    (by norm_num)
  have h2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith only [h, h2]

private theorem log_pi_lb : (1.1444 : ℝ) ≤ Real.log Real.pi := by
  have hpow : (2 : ℝ) ^ 71 ≤ Real.pi ^ 43 := by
    have hπ := Real.pi_gt_d4
    calc (2 : ℝ) ^ 71 ≤ 3.1415 ^ 43 := by norm_num
      _ ≤ Real.pi ^ 43 := pow_le_pow_left₀ (by norm_num) hπ.le 43
  have h := le_log_of_two_pow_le (p := Real.pi) Real.pi_pos (k := 43) (m := 71) (by norm_num) hpow
  have h2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith only [h, h2]

private theorem exp_three_le : Real.exp 3 ≤ 20.0856 := by
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h]
  have h1 := Real.exp_one_lt_d9
  calc Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 3
    _ ≤ 20.0856 := by norm_num

private theorem twenty_le_exp_three : (20 : ℝ) ≤ Real.exp 3 := by
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h]
  have h1 := Real.exp_one_gt_d9
  calc (20 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3

private theorem exp_neg_three_halves_ge : (0.22312 : ℝ) ≤ Real.exp (-(3 / 2)) := by
  have hsq : (0.22312 : ℝ) ^ 2 ≤ Real.exp (-(3 / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
    rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos 3)]
    have := exp_three_le
    nlinarith only [this]
  exact (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num)).1 hsq

/-! ## The Fejér polynomial at band three -/

private theorem tri_eq {u : ℝ} (h0 : 0 ≤ u) (h3 : u ≤ 3) : triangleFn 3 u = 1 - u / 3 := by
  unfold triangleFn
  rw [abs_of_nonneg h0, max_eq_left]
  linarith only [h3]

private theorem log_le_three {n : ℝ} (h0 : 0 < n) (h20 : n ≤ 20) : Real.log n ≤ 3 := by
  rw [Real.log_le_iff_le_exp h0]
  linarith only [h20, twenty_le_exp_three]

private theorem three_le_log (n : ℕ) (hn : 21 ≤ n) : 3 ≤ Real.log n := by
  have hn' : (21 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith only [hn'])]
  linarith only [hn', exp_three_le]

private theorem Λ_coprime {a b : ℕ} (h : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    vonMangoldt (a * b) = 0 := vonMangoldt_mul_eq_zero_of_coprime h ha hb

private theorem Λ_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    vonMangoldt (p ^ k) = Real.log p := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- The Fejér polynomial expanded over prime powers. -/
private theorem poly_eq (γ : ℝ) :
    ∑ n ∈ Finset.range 21, vonMangoldt n / n * triangleFn 3 (Real.log n) *
        Real.cos (γ * Real.log n) =
      (Real.log 2 / 2 * (1 - Real.log 2 / 3) * Real.cos (γ * Real.log 2) +
        Real.log 2 / 4 * (1 - 2 * Real.log 2 / 3) * Real.cos (2 * (γ * Real.log 2)) +
        Real.log 2 / 8 * (1 - 3 * Real.log 2 / 3) * Real.cos (3 * (γ * Real.log 2)) +
        Real.log 2 / 16 * (1 - 4 * Real.log 2 / 3) * Real.cos (2 * (2 * (γ * Real.log 2)))) +
      (Real.log 3 / 3 * (1 - Real.log 3 / 3) * Real.cos (γ * Real.log 3) +
        Real.log 3 / 9 * (1 - 2 * Real.log 3 / 3) * Real.cos (2 * (γ * Real.log 3))) +
      Real.log 5 / 5 * (1 - Real.log 5 / 3) * Real.cos (γ * Real.log 5) +
      Real.log 7 / 7 * (1 - Real.log 7 / 3) * Real.cos (γ * Real.log 7) +
      Real.log 11 / 11 * (1 - Real.log 11 / 3) * Real.cos (γ * Real.log 11) +
      Real.log 13 / 13 * (1 - Real.log 13 / 3) * Real.cos (γ * Real.log 13) +
      Real.log 17 / 17 * (1 - Real.log 17 / 3) * Real.cos (γ * Real.log 17) +
      Real.log 19 / 19 * (1 - Real.log 19 / 3) * Real.cos (γ * Real.log 19) := by
  have h0 : vonMangoldt 0 = 0 := ArithmeticFunction.map_zero
  have h1 : vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
  have h6 : vonMangoldt 6 = 0 := Λ_coprime (a := 2) (b := 3) (by norm_num) (by norm_num) (by norm_num)
  have h10 : vonMangoldt 10 = 0 :=
    Λ_coprime (a := 2) (b := 5) (by norm_num) (by norm_num) (by norm_num)
  have h12 : vonMangoldt 12 = 0 :=
    Λ_coprime (a := 3) (b := 4) (by norm_num) (by norm_num) (by norm_num)
  have h14 : vonMangoldt 14 = 0 :=
    Λ_coprime (a := 2) (b := 7) (by norm_num) (by norm_num) (by norm_num)
  have h15 : vonMangoldt 15 = 0 :=
    Λ_coprime (a := 3) (b := 5) (by norm_num) (by norm_num) (by norm_num)
  have h18 : vonMangoldt 18 = 0 :=
    Λ_coprime (a := 2) (b := 9) (by norm_num) (by norm_num) (by norm_num)
  have h20 : vonMangoldt 20 = 0 :=
    Λ_coprime (a := 4) (b := 5) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : vonMangoldt 2 = Real.log 2 := by
    have := Λ_pow 2 1 (by norm_num) (by norm_num)
    simpa using this
  have hp3 : vonMangoldt 3 = Real.log 3 := by
    have := Λ_pow 3 1 (by norm_num) (by norm_num)
    simpa using this
  have hp5 : vonMangoldt 5 = Real.log 5 := by
    have := Λ_pow 5 1 (by norm_num) (by norm_num)
    simpa using this
  have hp7 : vonMangoldt 7 = Real.log 7 := by
    have := Λ_pow 7 1 (by norm_num) (by norm_num)
    simpa using this
  have hp11 : vonMangoldt 11 = Real.log 11 := by
    have := Λ_pow 11 1 (by norm_num) (by norm_num)
    simpa using this
  have hp13 : vonMangoldt 13 = Real.log 13 := by
    have := Λ_pow 13 1 (by norm_num) (by norm_num)
    simpa using this
  have hp17 : vonMangoldt 17 = Real.log 17 := by
    have := Λ_pow 17 1 (by norm_num) (by norm_num)
    simpa using this
  have hp19 : vonMangoldt 19 = Real.log 19 := by
    have := Λ_pow 19 1 (by norm_num) (by norm_num)
    simpa using this
  have hp4 : vonMangoldt 4 = Real.log 2 := by
    have := Λ_pow 2 2 (by norm_num) (by norm_num)
    norm_num at this
    exact this
  have hp8 : vonMangoldt 8 = Real.log 2 := by
    have := Λ_pow 2 3 (by norm_num) (by norm_num)
    norm_num at this
    exact this
  have hp16 : vonMangoldt 16 = Real.log 2 := by
    have := Λ_pow 2 4 (by norm_num) (by norm_num)
    norm_num at this
    exact this
  have hp9 : vonMangoldt 9 = Real.log 3 := by
    have := Λ_pow 3 2 (by norm_num) (by norm_num)
    norm_num at this
    exact this
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hl16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hl9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have ht (m : ℝ) (h0 : 1 ≤ m) (h20 : m ≤ 20) : triangleFn 3 (Real.log m) = 1 - Real.log m / 3 :=
    tri_eq (Real.log_nonneg h0) (log_le_three (by linarith only [h0]) h20)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, h0, h1, h6, h10, h12, h14, h15, h18, h20, hp2, hp3, hp4, hp5, hp7, hp8, hp9,
    hp11, hp13, hp16, hp17, hp19, zero_div, zero_mul, zero_add, add_zero]
  rw [ht 2 (by norm_num) (by norm_num), ht 3 (by norm_num) (by norm_num),
    ht 4 (by norm_num) (by norm_num), ht 5 (by norm_num) (by norm_num),
    ht 7 (by norm_num) (by norm_num), ht 8 (by norm_num) (by norm_num),
    ht 9 (by norm_num) (by norm_num), ht 11 (by norm_num) (by norm_num),
    ht 13 (by norm_num) (by norm_num), ht 16 (by norm_num) (by norm_num),
    ht 17 (by norm_num) (by norm_num), ht 19 (by norm_num) (by norm_num), hl4, hl8, hl9, hl16]
  have e2 : γ * (2 * Real.log 2) = 2 * (γ * Real.log 2) := by ring
  have e3 : γ * (3 * Real.log 2) = 3 * (γ * Real.log 2) := by ring
  have e4 : γ * (4 * Real.log 2) = 2 * (2 * (γ * Real.log 2)) := by ring
  have e9 : γ * (2 * Real.log 3) = 2 * (γ * Real.log 3) := by ring
  rw [e2, e3, e4, e9]
  ring

/-- **The worst phase.** The Fejér polynomial at band three is at least `−0.7278` at every height. -/
theorem poly_ge (γ : ℝ) :
    -(0.7278 : ℝ) ≤ ∑ n ∈ Finset.range 21, vonMangoldt n / n * triangleFn 3 (Real.log n) *
      Real.cos (γ * Real.log n) := by
  rw [poly_eq]
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  obtain ⟨l2, hl2⟩ : ∃ l2, l2 = Real.log 2 := ⟨_, rfl⟩
  rw [← hl2] at hl2a hl2b ⊢
  obtain ⟨s, hs⟩ : ∃ s, s = l2 ^ 2 := ⟨_, rfl⟩
  have hs1 : (0.6931471803 : ℝ) ^ 2 ≤ s := by
    rw [hs]
    exact pow_le_pow_left₀ (by norm_num) hl2a.le 2
  have hs2 : s ≤ (0.6931471808 : ℝ) ^ 2 := by
    rw [hs]
    exact pow_le_pow_left₀ (by linarith only [hl2a]) hl2b.le 2
  norm_num at hs1 hs2
  -- The family of `2`.
  obtain ⟨u, hu⟩ : ∃ u, u = Real.cos (γ * l2) := ⟨_, rfl⟩
  have hu0 : -1 ≤ u := by rw [hu]; exact Real.neg_one_le_cos _
  have hu1 : u ≤ 1 := by rw [hu]; exact Real.cos_le_one _
  have ec2 : Real.cos (2 * (γ * l2)) = 2 * u ^ 2 - 1 := by rw [Real.cos_two_mul, hu]
  have ec3 : Real.cos (3 * (γ * l2)) = 4 * u ^ 3 - 3 * u := by rw [Real.cos_three_mul, hu]
  have ec4 : Real.cos (2 * (2 * (γ * l2))) = 8 * u ^ 4 - 8 * u ^ 2 + 1 := by
    rw [Real.cos_two_mul, ec2]
    ring
  have eA : l2 / 2 * (1 - l2 / 3) = l2 / 2 - s / 6 := by rw [hs]; ring
  have eB : l2 / 4 * (1 - 2 * l2 / 3) = l2 / 4 - s / 6 := by rw [hs]; ring
  have eC : l2 / 8 * (1 - 3 * l2 / 3) = l2 / 8 - s / 8 := by rw [hs]; ring
  have eD : l2 / 16 * (1 - 4 * l2 / 3) = l2 / 16 - s / 12 := by rw [hs]; ring
  have hfam2 := family_two (A := l2 / 2 - s / 6) (B := l2 / 4 - s / 6) (C := l2 / 8 - s / 8)
    (D := l2 / 16 - s / 12) hu0 hu1 (by linarith only [hl2a, hs2]) (by linarith only [hl2a, hs2])
    (by
      have hB0 : 0 ≤ l2 / 4 - s / 6 := by linarith only [hl2a, hs2]
      have hB1 : l2 / 4 - s / 6 ≤ 0.0933 := by linarith only [hl2b, hs1]
      have hC1 : (0.0265 : ℝ) ≤ l2 / 8 - s / 8 := by linarith only [hl2a, hs2]
      have hE : (0.12 : ℝ) ≤ l2 / 2 - s / 6 - (l2 / 4 - s / 6) - 16 * (l2 / 16 - s / 12) := by
        linarith only [hl2a, hl2b, hs1, hs2]
      have h1 := pow_le_pow_left₀ hB0 hB1 2
      have h2 := mul_le_mul hC1 hE (by norm_num) (by linarith only [hC1])
      norm_num at h1 h2 ⊢
      linarith only [h1, h2])
  -- The family of `3`.
  have hl3a := log3_lb
  have hl3b := log3_ub
  obtain ⟨l3, hl3⟩ : ∃ l3, l3 = Real.log 3 := ⟨_, rfl⟩
  rw [← hl3] at hl3a hl3b ⊢
  obtain ⟨v, hv⟩ : ∃ v, v = Real.cos (γ * l3) := ⟨_, rfl⟩
  have hv0 : -1 ≤ v := by rw [hv]; exact Real.neg_one_le_cos _
  have hv1 : v ≤ 1 := by rw [hv]; exact Real.cos_le_one _
  have ecv2 : Real.cos (2 * (γ * l3)) = 2 * v ^ 2 - 1 := by rw [Real.cos_two_mul, hv]
  have hl3s1 : (1.09857 : ℝ) ^ 2 ≤ l3 ^ 2 := pow_le_pow_left₀ (by norm_num) hl3a 2
  have hl3s2 : l3 ^ 2 ≤ (1.09872 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith only [hl3a]) hl3b 2
  norm_num at hl3s1 hl3s2
  have eE : l3 / 3 * (1 - l3 / 3) = l3 / 3 - l3 ^ 2 / 9 := by ring
  have eF : l3 / 9 * (1 - 2 * l3 / 3) = l3 / 9 - 2 * l3 ^ 2 / 27 := by ring
  have hfam3 := family_three (E := l3 / 3 - l3 ^ 2 / 9) (F := l3 / 9 - 2 * l3 ^ 2 / 27) hv0
    (by linarith only [hl3a, hl3s2]) (by linarith only [hl3a, hl3b, hl3s1, hl3s2])
  -- The single primes.
  have hp (x x0 p : ℝ) (θ : ℝ) (h0 : x0 ≤ x) (hx0 : 3 / 2 ≤ x0) (hp : 0 < p) (hx3 : x ≤ 3) :
      -(x0 / p * (1 - x0 / 3)) ≤ x / p * (1 - x / 3) * Real.cos θ := by
    refine neg_le_mul_cos ?_ (prime_term_le h0 hx0 hp)
    have : 0 ≤ 1 - x / 3 := by linarith only [hx3]
    have hx : 0 ≤ x := by linarith only [h0, hx0]
    positivity
  have h5 := hp _ 1.60909 5 (γ * Real.log 5) log5_lb (by norm_num) (by norm_num)
    (log_le_three (by norm_num) (by norm_num))
  have h7 := hp _ 1.9452 7 (γ * Real.log 7) log7_lb (by norm_num) (by norm_num)
    (log_le_three (by norm_num) (by norm_num))
  have h11 := hp _ 2.3971 11 (γ * Real.log 11) log11_lb (by norm_num) (by norm_num)
    (log_le_three (by norm_num) (by norm_num))
  have h13 := hp _ 2.5646 13 (γ * Real.log 13) log13_lb (by norm_num) (by norm_num)
    (log_le_three (by norm_num) (by norm_num))
  have h17 := hp _ 2.8328 17 (γ * Real.log 17) log17_lb (by norm_num) (by norm_num)
    (log_le_three (by norm_num) (by norm_num))
  have h19 := hp _ 2.9406 19 (γ * Real.log 19) log19_lb (by norm_num) (by norm_num)
    (log_le_three (by norm_num) (by norm_num))
  norm_num at h5 h7 h11 h13 h17 h19
  rw [eA, eB, eC, eD, eE, eF, ec2, ec3, ec4, ecv2, ← hu, ← hv]
  norm_num at hfam2 hfam3 ⊢
  linarith only [hfam2, hfam3, h5, h7, h11, h13, h17, h19, hl2a, hl2b, hs1, hs2, hl3a, hl3b,
    hl3s1, hl3s2]

/-! ## The height -/

/-- The value of the left side of the budget at band three. -/
private theorem budget_left_ge : (1.9283 : ℝ) ≤ 2 * (2 - 4 * (1 - Real.exp (-(3 / 2))) / 3) := by
  have := exp_neg_three_halves_ge
  norm_num at this ⊢
  linarith only [this]

private theorem arch_tail_le {γ γ₀ : ℝ} (h0 : 0 < γ₀) (hγ : γ₀ ≤ γ) :
    8 / 3 / γ ^ 2 + 9 / (2 * Real.pi * 3) / γ ≤ 8 / 3 / γ₀ ^ 2 + 0.47749 / γ₀ := by
  have hγ0 : 0 < γ := h0.trans_le hγ
  have hπ := Real.pi_gt_d4
  have h1 : 8 / 3 / γ ^ 2 ≤ 8 / 3 / γ₀ ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ h0.le hγ 2)
  have h2 : 9 / (2 * Real.pi * 3) ≤ 0.47749 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hπ]
  have h3 : 9 / (2 * Real.pi * 3) / γ ≤ 0.47749 / γ₀ :=
    calc _ ≤ 0.47749 / γ := div_le_div_of_nonneg_right h2 hγ0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) h0 hγ
  linarith only [h1, h3]

/-- Bands of `log(9/4 + γ²/4)`. -/
private theorem log_band_le {γ B : ℝ} (hγ : 0 < γ) (h : 9 / 4 + γ ^ 2 / 4 ≤ B) :
    Real.log (9 / 4 + γ ^ 2 / 4) ≤ Real.log B :=
  Real.log_le_log (by positivity) h

/-- **No budget for an off-line zero below height 67.** -/
private theorem arch_lt {γ : ℝ} (h14 : 14 ≤ γ) (h67 : γ ≤ 67) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 + 8 / 3 / γ ^ 2 +
      9 / (2 * Real.pi * 3) / γ < 1.2005 := by
  have hγ0 : 0 < γ := by linarith only [h14]
  have hπ := log_pi_lb
  have hl2 := Real.log_two_lt_d9
  rcases le_total γ 40 with h40 | h40
  · have hlog := log_band_le hγ0 (B := 512) (by nlinarith only [h14, h40])
    rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow] at hlog
    have ht := arch_tail_le (γ₀ := 14) (by norm_num) h14
    norm_num at hlog ht ⊢
    linarith only [hlog, ht, hπ, hl2]
  · rcases le_total γ 60 with h60 | h60
    · have hlog := log_band_le hγ0 (B := 1024) (by nlinarith only [h40, h60])
      rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow] at hlog
      have ht := arch_tail_le (γ₀ := 40) (by norm_num) h40
      norm_num at hlog ht ⊢
      linarith only [hlog, ht, hπ, hl2]
    · have hlog := log_band_le hγ0 (B := 1130) (by nlinarith only [h60, h67])
      have hsplit : Real.log 1130 = 10 * Real.log 2 + Real.log (565 / 512) := by
        rw [show (1130 : ℝ) = 2 ^ 10 * (565 / 512) by norm_num,
          Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
        norm_num
      have hsmall := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 565 / 512 by norm_num)
      have ht := arch_tail_le (γ₀ := 60) (by norm_num) h60
      norm_num at hsmall ht ⊢
      rw [hsplit] at hlog
      linarith only [hlog, hsmall, ht, hπ, hl2]

/-- **RH through height 67.** No off-line zero of `ξ` has ordinate in `(0, 67]`. -/
theorem rhVerifiedThrough_sixtySeven : RHVerifiedThrough 67 := by
  intro ρ hzero _ _ him0 him67
  by_contra hoff
  let rhoSupport : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hzero⟩
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rhoSupport
    have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rhoSupport : ℂ)) := by omega
    exact ⟨rhoSupport, ⟨0, hn⟩⟩
  have hqre : (q.1 : ℂ).re ≠ 1 / 2 := hoff
  have hqim : (q.1 : ℂ).im = ρ.im := rfl
  have hfloor := orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine q hqre
  rw [hqim] at hfloor
  unfold xiOrderTwentyThreeOptimizedHeightSq at hfloor
  have h14 : 14 ≤ ρ.im := by nlinarith only [hfloor, him0]
  have hb := budget_at_edge (L := 3) (N := 21) (by norm_num) (fun n hn => three_le_log n hn) q hqre
    hqim (by linarith only [h14])
  have hpoly := poly_ge ρ.im
  have hleft := budget_left_ge
  have harch := arch_lt h14 him67
  norm_num at hb hleft harch hpoly
  linarith only [hb, hleft, harch, hpoly]

/-! ## Consequences on the rungs -/

/-- The Taylor coefficients of `ξ` at the centre form a `PF_200` sequence. -/
theorem xi_centre_pfSeq_twoHundred : PFSeq 200 (evenTaylorRe (fun x => xi (1 / 2 + x))) :=
  xi_centre_pfSeq_of_rhVerifiedThrough (T := 67) (by norm_num) rhVerifiedThrough_sixtySeven
    (by norm_num) (by norm_num)

/-- Every Taylor coefficient of `ξ(½+x+it)ξ(½−x+it)` is nonnegative on `|t| ≤ 133/2`. -/
theorem xiSliceCoeff_nonneg_of_abs_le_band {t : ℝ} (ht : |t| ≤ 133 / 2) (n : ℕ) :
    0 ≤ xiSliceCoeff t n :=
  xiSliceCoeff_nonneg_of_rhVerifiedThrough (T := 67) (t := t) (by linarith only [ht])
    rhVerifiedThrough_sixtySeven n

/-- The Li coefficients `λ_n` are nonnegative for `n ≤ 314`. -/
theorem re_xiLiPaired_nonneg_of_le {n : ℕ} (hn : n ≤ 314) : 0 ≤ (xiLiPaired n).re := by
  have hn' : (n : ℝ) ≤ 314 := by exact_mod_cast hn
  exact re_xiLiPaired_nonneg_of_rhVerifiedThrough (T := 67) (by norm_num)
    rhVerifiedThrough_sixtySeven (by linarith only [hn'])

end

end GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget
