import GaloisForLFunctions.ArithmeticIncidencePositivity.UnpaidAxisIntervals

/-!
# Which anti-diagonals have their quarter point paid

The full level of the anti-diagonal of `n` is `E_n = ω(log n) + Λ(n)/√n` and its polar weight is
`P(a) = 2 sinh(a/2) sinh((log n − a)/2)`. With `r = n^{1/4}`, the quarter point is paid,
`E_n ≤ P(log n / 4)`, iff

`n²/(n² − 1) + Λ(n) ≤ (n + 1 − r³ − r)/2`        (`antiDiagonalLevel_le_quarter_iff`),

and for `n ≥ 2` this holds exactly for `n ∈ {10, 12}` and every `n ≥ 14` except `n = 17`
(`antiDiagonalLevel_le_quarter_iff_mem`). The prime `17` misses by about one percent:
`289/288 + log 17 ≈ 3.837` against `(18 − 17^{3/4} − 17^{1/4})/2 ≈ 3.799`.

Whenever the midpoint is paid, `E ≤ P(s/2)`, the unpaid set is exactly two axis intervals
`(0, c) ∪ (s − c, s)` with `P(c) = E` (`unpaidSet_eq_of_le_midpoint`): `P` is strictly increasing on
`[0, s/2]` and symmetric. The quarter point is paid iff `c ≤ s/4`. The midpoint is paid but the
quarter point is not exactly for `n ∈ {6, 17}` (`midpoint_paid_and_quarter_unpaid_iff`); for these
two moduli the unpaid intervals reach past the quarter point, `s/4 < c ≤ s/2`
(`unpaidSet_level_eq_of_quarter_unpaid`).
-/

open RHTower Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The quarter condition in fourth-root coordinates -/

/-- With `r = n^{1/4}`, the quarter point of the anti-diagonal of `n` is paid iff
`n²/(n² − 1) + Λ(n) ≤ (n + 1 − r³ − r)/2`. -/
theorem antiDiagonalLevel_le_quarter_iff {n : ℕ} (hn : 2 ≤ n) :
    antiDiagonalLevel n ≤ crossingPolarWeight (Real.log n) (Real.log n / 4) ↔
      (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + ArithmeticFunction.vonMangoldt n ≤
        ((n : ℝ) + 1 - Real.sqrt (Real.sqrt n) ^ 3 - Real.sqrt (Real.sqrt n)) / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  set r := Real.sqrt (Real.sqrt n) with hr_def
  have hr : 0 < r := Real.sqrt_pos.mpr hs
  have hr2 : r ^ 2 = Real.sqrt n := Real.sq_sqrt hs.le
  have hr4 : r ^ 4 = n := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2, Real.sq_sqrt hn0.le]
  have hlog : Real.log n = 4 * Real.log r := by
    rw [← hr4, Real.log_pow]; push_cast; ring
  have hP : crossingPolarWeight (Real.log n) (Real.log n / 4) =
      (r ^ 2 + (r ^ 2)⁻¹) / 2 - (r + r⁻¹) / 2 := by
    rw [crossingPolarWeight_eq, show Real.log n / 2 - Real.log n / 4 = Real.log n / 4 by ring,
      hlog, show 4 * Real.log r / 2 = Real.log (r ^ 2) by rw [Real.log_pow]; push_cast; ring,
      show 4 * Real.log r / 4 = Real.log r by ring, cosh_log (by positivity), cosh_log hr]
  unfold antiDiagonalLevel vonMangoldtAtom
  rw [if_pos hn, archLevyDensity_log_nat hn, hP,
    show (n : ℝ) ^ 2 / (((n : ℝ) ^ 2 - 1) * Real.sqrt n) =
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) / Real.sqrt n by rw [div_div], ← add_div, ← hr2,
    div_le_iff₀ (by positivity)]
  have hR : ((r ^ 2 + (r ^ 2)⁻¹) / 2 - (r + r⁻¹) / 2) * r ^ 2 = (r ^ 4 + 1 - r ^ 3 - r) / 2 := by
    field_simp
    ring
  rw [hR, hr4]

/-! ### Interval certificates -/

theorem sqrt_sqrt_pow_four (n : ℕ) : Real.sqrt (Real.sqrt n) ^ 4 = n := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [show Real.sqrt (Real.sqrt n) ^ 4 = (Real.sqrt (Real.sqrt n) ^ 2) ^ 2 by ring,
    Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt h0]

theorem sqrt_sqrt_le_of_le_pow_four {n : ℕ} {b : ℝ} (hb : 0 ≤ b) (h : (n : ℝ) ≤ b ^ 4) :
    Real.sqrt (Real.sqrt n) ≤ b := by
  by_contra hlt
  rw [not_le] at hlt
  have := pow_lt_pow_left₀ hlt hb (by norm_num : (4 : ℕ) ≠ 0)
  rw [sqrt_sqrt_pow_four] at this
  linarith

theorem le_sqrt_sqrt_of_pow_four_le {n : ℕ} {a : ℝ} (h : a ^ 4 ≤ n) :
    a ≤ Real.sqrt (Real.sqrt n) := by
  by_contra hlt
  rw [not_le] at hlt
  have := pow_lt_pow_left₀ hlt (Real.sqrt_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)
  rw [sqrt_sqrt_pow_four] at this
  linarith

/-- A certificate that the quarter point is paid: an upper bound `b ≥ n^{1/4}` and `Λ(n) ≤ L`. -/
theorem quarter_paid_of {n : ℕ} (hn : 2 ≤ n) {b L : ℝ} (hb : 0 ≤ b) (hb4 : (n : ℝ) ≤ b ^ 4)
    (hΛ : ArithmeticFunction.vonMangoldt n ≤ L)
    (h : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + L ≤ ((n : ℝ) + 1 - b ^ 3 - b) / 2) :
    antiDiagonalLevel n ≤ crossingPolarWeight (Real.log n) (Real.log n / 4) := by
  rw [antiDiagonalLevel_le_quarter_iff hn]
  have hr := sqrt_sqrt_le_of_le_pow_four hb hb4
  have hr0 := Real.sqrt_nonneg (Real.sqrt n)
  have h3 : Real.sqrt (Real.sqrt n) ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ hr0 hr 3
  linarith

/-- A certificate that the quarter point is unpaid: a lower bound `a ≤ n^{1/4}` and `L ≤ Λ(n)`. -/
theorem quarter_unpaid_of {n : ℕ} (hn : 2 ≤ n) {a L : ℝ} (ha : 0 ≤ a) (ha4 : a ^ 4 ≤ n)
    (hΛ : L ≤ ArithmeticFunction.vonMangoldt n)
    (h : ((n : ℝ) + 1 - a ^ 3 - a) / 2 < (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + L) :
    ¬ antiDiagonalLevel n ≤ crossingPolarWeight (Real.log n) (Real.log n / 4) := by
  rw [antiDiagonalLevel_le_quarter_iff hn, not_le]
  have hr := le_sqrt_sqrt_of_pow_four_le ha4
  have h3 : a ^ 3 ≤ Real.sqrt (Real.sqrt n) ^ 3 := pow_le_pow_left₀ ha hr 3
  linarith

/-! ### Values of `Λ` -/

theorem vonMangoldt_eq_zero_of_not {n : ℕ} (h : ¬ IsPrimePow n) : ArithmeticFunction.vonMangoldt n = 0 :=
  ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h

/-- A product of two distinct primes is not a prime power. -/
theorem not_isPrimePow_mul_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ IsPrimePow (p * q) := by
  rw [isPrimePow_nat_iff]
  rintro ⟨r, k, hr, -, h⟩
  have e1 := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow (h ▸ dvd_mul_right p q))
  have e2 := (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow (h ▸ dvd_mul_left q p))
  exact hpq (e1.trans e2.symm)

theorem vonMangoldt_prime_ge_log_two {p : ℕ} (hp : p.Prime) :
    Real.log 2 ≤ ArithmeticFunction.vonMangoldt p := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)

theorem vonMangoldt_prime_ge_three_log_two {p : ℕ} (hp : p.Prime) (h8 : 8 ≤ p) :
    3 * Real.log 2 ≤ ArithmeticFunction.vonMangoldt p := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp, ← Real.log_rpow (by norm_num)]
  exact Real.log_le_log (by norm_num) (by norm_num; exact_mod_cast h8)

theorem vonMangoldt_seventeen_ge : 4 * Real.log 2 + 1 / 17 ≤ ArithmeticFunction.vonMangoldt 17 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 17 / 16)
  rw [Real.log_div (by norm_num) (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num,
    Real.log_pow] at h
  push_cast at h ⊢
  linarith

theorem vonMangoldt_nineteen_le : ArithmeticFunction.vonMangoldt 19 ≤ 4 * Real.log 2 + 3 / 16 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 19 / 16)
  rw [Real.log_div (by norm_num) (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num,
    Real.log_pow] at h
  push_cast at h ⊢
  linarith

theorem vonMangoldt_two_pow_le {k : ℕ} (hk : k ≠ 0) :
    ArithmeticFunction.vonMangoldt (2 ^ k) ≤ 0.6931471808 := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime
    Nat.prime_two]
  push_cast
  exact Real.log_two_lt_d9.le

/-! ### The classification -/

/-- **Quarter-point classification.** For `n ≥ 2` the pole pays the full level of the
anti-diagonal of `n` at the quarter point exactly when `n ∈ {10, 12}` or `n ≥ 14`, `n ≠ 17`. -/
theorem antiDiagonalLevel_le_quarter_iff_mem {n : ℕ} (hn : 2 ≤ n) :
    antiDiagonalLevel n ≤ crossingPolarWeight (Real.log n) (Real.log n / 4) ↔
      n = 10 ∨ n = 12 ∨ (14 ≤ n ∧ n ≠ 17) := by
  rcases Nat.lt_or_ge n 23 with h23 | h23
  · have hl2 := Real.log_two_gt_d9
    have hΛ0 : ∀ m : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt m :=
      fun _ => ArithmeticFunction.vonMangoldt_nonneg
    interval_cases n
    · exact iff_of_false (quarter_unpaid_of (a := 1.189) (L := 0) hn (by norm_num) (by norm_num)
        (hΛ0 2) (by norm_num)) (by omega)
    · exact iff_of_false (quarter_unpaid_of (a := 1.316) (L := 0) hn (by norm_num) (by norm_num)
        (hΛ0 3) (by norm_num)) (by omega)
    · exact iff_of_false (quarter_unpaid_of (a := 1.414) (L := 0) hn (by norm_num) (by norm_num)
        (hΛ0 4) (by norm_num)) (by omega)
    · exact iff_of_false (quarter_unpaid_of (a := 1.495) (L := 0) hn (by norm_num) (by norm_num)
        (hΛ0 5) (by norm_num)) (by omega)
    · exact iff_of_false (quarter_unpaid_of (a := 1.565) (L := 0) hn (by norm_num) (by norm_num)
        (hΛ0 6) (by norm_num)) (by omega)
    · exact iff_of_false (quarter_unpaid_of (a := 1.626) (L := 0.69) hn (by norm_num) (by norm_num)
        (by linarith [vonMangoldt_prime_ge_log_two (p := 7) (by norm_num)]) (by norm_num)) (by omega)
    · have h8 : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
          ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        norm_num
      exact iff_of_false (quarter_unpaid_of (a := 1.681) (L := 0.69) hn (by norm_num) (by norm_num)
        (by linarith) (by norm_num)) (by omega)
    · have h9 : Real.log 2 ≤ ArithmeticFunction.vonMangoldt 9 := by
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num)]
        exact vonMangoldt_prime_ge_log_two (by norm_num)
      exact iff_of_false (quarter_unpaid_of (a := 1.732) (L := 0.69) hn (by norm_num) (by norm_num)
        (by linarith) (by norm_num)) (by omega)
    · exact iff_of_true (quarter_paid_of (b := 1.7783) (L := 0) hn (by norm_num) (by norm_num)
        (vonMangoldt_eq_zero_of_not (by decide)).le (by norm_num)) (by omega)
    · exact iff_of_false (quarter_unpaid_of (a := 1.821) (L := 2.07) hn (by norm_num) (by norm_num)
        (by linarith [vonMangoldt_prime_ge_three_log_two (p := 11) (by norm_num) (by norm_num)])
        (by norm_num)) (by omega)
    · exact iff_of_true (quarter_paid_of (b := 1.8613) (L := 0) hn (by norm_num) (by norm_num)
        (vonMangoldt_eq_zero_of_not (by decide)).le (by norm_num)) (by omega)
    · exact iff_of_false (quarter_unpaid_of (a := 1.898) (L := 2.07) hn (by norm_num) (by norm_num)
        (by linarith [vonMangoldt_prime_ge_three_log_two (p := 13) (by norm_num) (by norm_num)])
        (by norm_num)) (by omega)
    · exact iff_of_true (quarter_paid_of (b := 1.9344) (L := 0) hn (by norm_num) (by norm_num)
        (vonMangoldt_eq_zero_of_not (by decide)).le (by norm_num)) (by omega)
    · have h15 : ¬ IsPrimePow 15 := by
        simpa using not_isPrimePow_mul_of_prime (p := 3) (q := 5) (by norm_num) (by norm_num)
          (by norm_num)
      exact iff_of_true (quarter_paid_of (b := 1.9681) (L := 0) hn (by norm_num) (by norm_num)
        (vonMangoldt_eq_zero_of_not h15).le (by norm_num)) (by omega)
    · exact iff_of_true (quarter_paid_of (b := 2) (L := 0.6931471808) hn (by norm_num) (by norm_num)
        (by simpa using vonMangoldt_two_pow_le (k := 4) (by norm_num)) (by norm_num)) (by omega)
    · exact iff_of_false (quarter_unpaid_of (a := 2.0305) (L := 2.8314) hn (by norm_num)
        (by norm_num) (by linarith [vonMangoldt_seventeen_ge]) (by norm_num)) (by omega)
    · exact iff_of_true (quarter_paid_of (b := 2.0599) (L := 0) hn (by norm_num) (by norm_num)
        (vonMangoldt_eq_zero_of_not (by decide)).le (by norm_num)) (by omega)
    · have hl2' := Real.log_two_lt_d9
      exact iff_of_true (quarter_paid_of (b := 2.088) (L := 2.9601) hn (by norm_num) (by norm_num)
        (by linarith [vonMangoldt_nineteen_le]) (by norm_num)) (by omega)
    · exact iff_of_true (quarter_paid_of (b := 2.115) (L := 0) hn (by norm_num) (by norm_num)
        (vonMangoldt_eq_zero_of_not (by decide)).le (by norm_num)) (by omega)
    · have h21 : ¬ IsPrimePow 21 := by
        simpa using not_isPrimePow_mul_of_prime (p := 3) (q := 7) (by norm_num) (by norm_num)
          (by norm_num)
      exact iff_of_true (quarter_paid_of (b := 2.141) (L := 0) hn (by norm_num) (by norm_num)
        (vonMangoldt_eq_zero_of_not h21).le (by norm_num)) (by omega)
    · exact iff_of_true (quarter_paid_of (b := 2.166) (L := 0) hn (by norm_num) (by norm_num)
        (vonMangoldt_eq_zero_of_not (by decide)).le (by norm_num)) (by omega)
  · exact iff_of_true (antiDiagonalLevel_le_quarter h23) (by omega)


/-! ### The unpaid set once the midpoint is paid -/

/-- The polar weight is strictly increasing from the axis to the midpoint. -/
theorem crossingPolarWeight_lt {s a b : ℝ} (hab : a < b) (hb : b ≤ s / 2) :
    crossingPolarWeight s a < crossingPolarWeight s b := by
  rw [crossingPolarWeight_eq, crossingPolarWeight_eq]
  have h : Real.cosh (s / 2 - b) < Real.cosh (s / 2 - a) := by
    rw [Real.cosh_lt_cosh, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  linarith

/-- **Two axis intervals.** If the midpoint is paid, `0 < E ≤ P_s(s/2)`, the unpaid set is
`(0, c) ∪ (s − c, s)` for the unique `c ∈ (0, s/2]` with `P_s(c) = E`. -/
theorem unpaidSet_eq_of_le_midpoint {s E : ℝ} (hs : 0 < s) (hE : 0 < E)
    (hmid : E ≤ crossingPolarWeight s (s / 2)) :
    ∃ c, 0 < c ∧ c ≤ s / 2 ∧ crossingPolarWeight s c = E ∧
      unpaidSet s E = Ioo 0 c ∪ Ioo (s - c) s := by
  obtain ⟨c, ⟨hc0, hcs⟩, hcE⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ s / 2)
    (continuous_crossingPolarWeight s).continuousOn
    (show E ∈ Icc (crossingPolarWeight s 0) (crossingPolarWeight s (s / 2)) by
      rw [crossingPolarWeight_zero_left]; exact ⟨hE.le, hmid⟩)
  beta_reduce at hcE
  have hc : 0 < c := by
    rcases hc0.lt_or_eq with h | h
    · exact h
    · rw [← h, crossingPolarWeight_zero_left] at hcE; linarith
  refine ⟨c, hc, hcs, hcE, Set.ext fun a => ⟨fun ⟨ha0, has, haE⟩ => ?_, fun ha => ?_⟩⟩
  · rcases le_or_gt a (s / 2) with hah | hah
    · refine Or.inl ⟨ha0, lt_of_not_ge fun hca => ?_⟩
      have := crossingPolarWeight_mono hca hah
      linarith
    · refine Or.inr ⟨?_, has⟩
      by_contra hle
      rw [not_lt] at hle
      have h := crossingPolarWeight_mono (s := s) (show c ≤ s - a by linarith) (by linarith)
      rw [crossingPolarWeight_symm] at h
      linarith
  · rcases ha with ⟨ha0, hac⟩ | ⟨hsa, has⟩
    · exact ⟨ha0, by linarith, hcE ▸ crossingPolarWeight_lt hac hcs⟩
    · refine ⟨by linarith, has, ?_⟩
      have h := crossingPolarWeight_lt (by linarith : s - a < c) hcs
      rw [crossingPolarWeight_symm, hcE] at h
      exact h

/-- The midpoint condition of the anti-diagonal of `n` in square-root coordinates. -/
theorem antiDiagonalLevel_le_midpoint_iff {n : ℕ} (hn : 2 ≤ n) :
    antiDiagonalLevel n ≤ crossingPolarWeight (Real.log n) (Real.log n / 2) ↔
      n ∉ totalDominatedModuli := by
  rw [← total_midpoint_inequality_iff hn, not_lt]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hP : crossingPolarWeight (Real.log n) (Real.log n / 2) =
      (Real.sqrt n - 1) ^ 2 / (2 * Real.sqrt n) := by
    rw [crossingPolarWeight_eq, sub_self, Real.cosh_zero,
      show Real.log n / 2 = Real.log (Real.sqrt n) by rw [Real.log_sqrt hn0.le], cosh_log hs]
    field_simp
    ring
  unfold antiDiagonalLevel vonMangoldtAtom
  rw [if_pos hn, archLevyDensity_log_nat hn, hP,
    show (n : ℝ) ^ 2 / (((n : ℝ) ^ 2 - 1) * Real.sqrt n) =
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) / Real.sqrt n by rw [div_div], ← add_div,
    div_le_div_iff₀ hs (by positivity),
    show 2 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) = 2 * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) by ring,
    show ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + ArithmeticFunction.vonMangoldt n) * (2 * Real.sqrt n) =
      (2 * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) + 2 * ArithmeticFunction.vonMangoldt n) *
        Real.sqrt n by ring,
    mul_le_mul_iff_of_pos_right hs]

/-- **Midpoint paid, quarter point unpaid** happens exactly for `n ∈ {6, 17}`. -/
theorem midpoint_paid_and_quarter_unpaid_iff {n : ℕ} (hn : 2 ≤ n) :
    (antiDiagonalLevel n ≤ crossingPolarWeight (Real.log n) (Real.log n / 2) ∧
      ¬ antiDiagonalLevel n ≤ crossingPolarWeight (Real.log n) (Real.log n / 4)) ↔
      n = 6 ∨ n = 17 := by
  rw [antiDiagonalLevel_le_midpoint_iff hn, antiDiagonalLevel_le_quarter_iff_mem hn]
  simp only [totalDominatedModuli, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- For `n ∈ {6, 17}` the unpaid set of the anti-diagonal of `n` is two axis intervals that reach
past the quarter point: `(0, c) ∪ (log n − c, log n)` with `log n/4 < c ≤ log n/2`. -/
theorem unpaidSet_level_eq_of_quarter_unpaid {n : ℕ} (hn : n = 6 ∨ n = 17) :
    ∃ c, Real.log n / 4 < c ∧ c ≤ Real.log n / 2 ∧
      crossingPolarWeight (Real.log n) c = antiDiagonalLevel n ∧
      unpaidSet (Real.log n) (antiDiagonalLevel n) = Ioo 0 c ∪ Ioo (Real.log n - c) (Real.log n) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hmid, hq⟩ := (midpoint_paid_and_quarter_unpaid_iff hn2).mpr hn
  have hs : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hE : 0 < antiDiagonalLevel n := by
    unfold antiDiagonalLevel
    have h1 : 0 < archLevyDensity (Real.log n) := by
      rw [archLevyDensity_log_nat hn2]
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
      positivity
    have h2 : 0 ≤ vonMangoldtAtom n := by
      unfold vonMangoldtAtom
      rw [if_pos hn2]
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    linarith
  obtain ⟨c, hc0, hcs, hcE, hset⟩ := unpaidSet_eq_of_le_midpoint hs hE hmid
  refine ⟨c, lt_of_not_ge fun hc => hq ?_, hcs, hcE, hset⟩
  rw [← hcE]
  exact crossingPolarWeight_mono hc (by linarith)

end GaloisForLFunctions.ArithmeticIncidencePositivity
