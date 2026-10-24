import GaloisForLFunctions.SignedSuccessorArithmetic.TheOneThirdSuccessorFloor

/-!
# The floor reads the parity of the shift

Replace the successor `n → n+1` by the shift `n → n+h`. For a completely multiplicative sign the
lag-`h` signs `σ_h(n) = f(n) f(n+h)` satisfy the same dilation cocycle along arithmetic
progressions, `∏_{j<m} σ_h(mn + jh) = σ_h(n)` (`shift_dilation_cocycle`), and at `m = 2` the same
per-step count `a_h(2n) + a_h(2n+h) + a_h(n) = 1 + 2 a_h(n) a_h(2n)`.

Whether this count produces a floor depends on the parity of `h`, that is on the Bézout relation
between the dilation `2` and the shift:

* **Odd shifts.** The positions `2n` (even) and `2n + h` (odd) are disjoint and fill
  `[1, 2N+h]`, so the argument of the one-third floor goes through:
  `Σ_{n ≤ M, f(n) = f(n+h)} 1/n ≥ (1/3) log M − (h+1)` (`odd_shift_log_floor`).
* **Even shifts.** The two position sets overlap and the odd positions are unconstrained. The
  conductor-four twins (`f = χ₄` off `2`) disagree at every odd position for `h = 2`, keep their
  sign exactly once per two steps along the successor (`C(4J) = 0`, perfect successor balance), and
  have lag-two agreement mass `≤ (1/4) log M + 2` (`chi4Twin_lag_two_log_le`). Every completely
  multiplicative sign has lag-two mass `≥ (1/6) log M − 1` (`lag_two_log_floor`), so the lag-two
  floor lies in `[1/6, 1/4]`, strictly below the odd-shift floor.

The alternating sign `(-1)^n`, which is not multiplicative, disagrees at every step
(`alternating_succSign`) and violates the dilation cocycle (`alternating_not_cocycle`): the floor
is a property of `×` and `+1` together, not of either alone.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset

/-- The lag-`h` sign `σ_h(n) = f(n) f(n+h)`. -/
def shiftSign (f : ℕ → ℤˣ) (h n : ℕ) : ℤˣ := f n * f (n + h)

/-- Lag-`h` agreement indicator. -/
def agreeAt (f : ℕ → ℤˣ) (h n : ℕ) : ℕ := if shiftSign f h n = 1 then 1 else 0

theorem agreeAt_one (f : ℕ → ℤˣ) : agreeAt f 1 = agree f := rfl

theorem agreeAt_le_one (f : ℕ → ℤˣ) (h n : ℕ) : agreeAt f h n ≤ 1 := by
  unfold agreeAt; split_ifs <;> omega

/-- Telescoping along the progression `a, a+h, …, a+mh`. -/
theorem prod_shiftSign_progression (f : ℕ → ℤˣ) (h a m : ℕ) :
    ∏ j ∈ range m, shiftSign f h (a + j * h) = f a * f (a + m * h) := by
  induction m with
  | zero => simp [Int.units_mul_self]
  | succ m ih =>
    rw [prod_range_succ, ih, shiftSign, show a + m * h + h = a + (m + 1) * h by ring]
    calc f a * f (a + m * h) * (f (a + m * h) * f (a + (m + 1) * h))
        = f a * (f (a + m * h) * f (a + m * h)) * f (a + (m + 1) * h) := by simp only [mul_assoc]
      _ = f a * f (a + (m + 1) * h) := by rw [Int.units_mul_self, mul_one]

/-- **The lag-`h` dilation cocycle.** -/
theorem shift_dilation_cocycle (f : CMSign) (h : ℕ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∏ j ∈ range m, shiftSign f h (m * n + j * h) = shiftSign f h n := by
  rw [prod_shiftSign_progression, show m * n + m * h = m * (n + h) by ring, f.map_mul hm hn,
    f.map_mul hm (by omega), mul_mul_mul_comm, Int.units_mul_self, one_mul, shiftSign]

theorem shiftSign_two_mul_mul (f : CMSign) (h : ℕ) {n : ℕ} (hn : 0 < n) :
    shiftSign f h (2 * n) * shiftSign f h (2 * n + h) = shiftSign f h n := by
  have hc := shift_dilation_cocycle f h (m := 2) two_pos hn
  rwa [prod_range_succ, prod_range_one, zero_mul, add_zero, one_mul] at hc

/-- Per-step doubling count for lag `h`. -/
theorem agreeAt_doubling (f : CMSign) (h : ℕ) {n : ℕ} (hn : 0 < n) :
    agreeAt f h (2 * n) + agreeAt f h (2 * n + h) + agreeAt f h n =
      1 + 2 * (agreeAt f h n * agreeAt f h (2 * n)) := by
  have hw := (shiftSign_two_mul_mul f h hn).symm
  unfold agreeAt
  rcases Int.units_eq_one_or (shiftSign f h (2 * n)) with hu | hu <;>
    rcases Int.units_eq_one_or (shiftSign f h (2 * n + h)) with hv | hv <;>
    simp [hu, hv] at hw ⊢ <;> simp [hw]

/-- Lag-`h` logarithmic agreement mass. -/
noncomputable def logAgreeAt (f : ℕ → ℤˣ) (h N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (agreeAt f h n : ℝ) / n

theorem logAgreeAt_mono (f : ℕ → ℤˣ) (h : ℕ) : Monotone (logAgreeAt f h) := by
  intro M N hMN
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hMN) fun n _ _ => by positivity

theorem logAgreeAt_nonneg (f : ℕ → ℤˣ) (h N : ℕ) : 0 ≤ logAgreeAt f h N :=
  sum_nonneg fun n _ => by positivity

/-! ## Odd shifts: the floor persists -/

/-- For odd `h` the even positions `2n` and the odd positions `2n + h` are disjoint inside
`[1, 2N+h]`. -/
theorem sum_two_mul_add_sum_two_mul_add_le {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {h : ℕ} (hodd : Odd h)
    (N : ℕ) :
    ∑ n ∈ Icc 1 N, (g (2 * n) + g (2 * n + h)) ≤ ∑ k ∈ Icc 1 (2 * N + h), g k := by
  rw [sum_add_distrib]
  have hinj1 : Set.InjOn (fun n => 2 * n) (Icc 1 N : Finset ℕ) := fun a _ b _ hab => by
    simp only at hab; omega
  have hinj2 : Set.InjOn (fun n => 2 * n + h) (Icc 1 N : Finset ℕ) := fun a _ b _ hab => by
    simp only at hab; omega
  rw [← sum_image (f := g) hinj1, ← sum_image (f := g) hinj2, ← sum_union]
  · refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hg k
    intro k hk
    simp only [mem_union, mem_image, mem_Icc] at hk ⊢
    rcases hk with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩ <;> omega
  · rw [disjoint_left]
    intro k hk1 hk2
    simp only [mem_image] at hk1 hk2
    obtain ⟨a, _, rfl⟩ := hk1
    obtain ⟨b, _, hb⟩ := hk2
    obtain ⟨c, rfl⟩ := hodd
    omega

theorem sum_inv_mul_succ_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, (1 : ℝ) / (n * (n + 1)) ≤ 1 - 1 / (N + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega)]
    push_cast at ih ⊢
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have key : (1 : ℝ) / ((N + 1) * (N + 1 + 1)) = 1 / (N + 1) - 1 / (N + 1 + 1) := by
      field_simp; ring
    linarith

/-- `L_h(2N+h) ≥ H_N/3 − h/3` for odd `h`. -/
theorem logAgreeAt_two_mul_add_ge (f : CMSign) {h : ℕ} (hodd : Odd h) (N : ℕ) :
    (harmonic N : ℝ) / 3 - h / 3 ≤ logAgreeAt f h (2 * N + h) := by
  have hh : (1 : ℝ) ≤ h := by obtain ⟨c, rfl⟩ := hodd; push_cast; linarith [Nat.cast_nonneg (α := ℝ) c]
  have hpair : ∀ n ∈ Icc 1 N, (1 - (agreeAt f h n : ℝ)) / (2 * n) -
      (h : ℝ) / 2 * (1 / (n * (n + 1))) ≤
      (agreeAt f h (2 * n) : ℝ) / ((2 * n : ℕ) : ℝ) +
        (agreeAt f h (2 * n + h) : ℝ) / ((2 * n + h : ℕ) : ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hcount : (1 : ℝ) - agreeAt f h n ≤ (agreeAt f h (2 * n) : ℝ) + agreeAt f h (2 * n + h) := by
      have := agreeAt_doubling f h (n := n) (by omega)
      have h' : ((agreeAt f h (2 * n) + agreeAt f h (2 * n + h) + agreeAt f h n : ℕ) : ℝ) =
          ((1 + 2 * (agreeAt f h n * agreeAt f h (2 * n)) : ℕ) : ℝ) := by rw [this]
      push_cast at h'
      nlinarith [Nat.cast_nonneg (α := ℝ) (agreeAt f h n * agreeAt f h (2 * n))]
    have ha1 : (agreeAt f h n : ℝ) ≤ 1 := by exact_mod_cast agreeAt_le_one f h n
    have ha0 : (0 : ℝ) ≤ agreeAt f h n := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ agreeAt f h (2 * n) := Nat.cast_nonneg _
    push_cast
    have e1 : (agreeAt f h (2 * n) : ℝ) / (2 * n + h) ≤ (agreeAt f h (2 * n) : ℝ) / (2 * n) :=
      div_le_div_of_nonneg_left hb0 (by positivity) (by linarith)
    have e3 : (1 - (agreeAt f h n : ℝ)) / (2 * n + h) ≤
        ((agreeAt f h (2 * n) : ℝ) + agreeAt f h (2 * n + h)) / (2 * n + h) :=
      div_le_div_of_nonneg_right hcount (by positivity)
    have e2 : (1 - (agreeAt f h n : ℝ)) / (2 * n) - (h : ℝ) / 2 * (1 / (n * (n + 1))) ≤
        (1 - (agreeAt f h n : ℝ)) / (2 * n + h) := by
      have hid : (1 - (agreeAt f h n : ℝ)) / (2 * n) - (1 - (agreeAt f h n : ℝ)) / (2 * n + h) =
          (1 - (agreeAt f h n : ℝ)) * h / (2 * n * (2 * n + h)) := by
        field_simp; ring
      have hle : (1 - (agreeAt f h n : ℝ)) * h / (2 * n * (2 * n + h)) ≤
          (h : ℝ) / 2 * (1 / (n * (n + 1))) := by
        rw [div_le_iff₀ (by positivity)]
        have : (1 - (agreeAt f h n : ℝ)) * h ≤ h := by nlinarith
        have h2 : (h : ℝ) / 2 * (1 / (n * (n + 1))) * (2 * n * (2 * n + h)) =
            h * ((2 * n + h) / (n + 1)) := by field_simp
        rw [h2]
        have : (1 : ℝ) ≤ (2 * n + h) / (n + 1) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        nlinarith
      linarith
    rw [add_div] at e3
    linarith
  have hsum := sum_le_sum hpair
  have hdis := sum_two_mul_add_sum_two_mul_add_le (g := fun k => (agreeAt f h k : ℝ) / k)
    (fun k => by positivity) hodd N
  have hlin : ∑ n ∈ Icc 1 N, ((1 - (agreeAt f h n : ℝ)) / (2 * n) -
      (h : ℝ) / 2 * (1 / (n * (n + 1)))) =
      (harmonic N : ℝ) / 2 - logAgreeAt f h N / 2 -
        (h : ℝ) / 2 * ∑ n ∈ Icc 1 N, (1 : ℝ) / (n * (n + 1)) := by
    rw [harmonic_eq_sum, logAgreeAt, Finset.sum_div, Finset.sum_div, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    ring
  have htel := sum_inv_mul_succ_le N
  have hmono := logAgreeAt_mono f h (show N ≤ 2 * N + h by omega)
  have hpos : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  simp only [logAgreeAt] at hdis hmono hlin ⊢
  push_cast at hsum hdis
  nlinarith

/-- **The odd-shift floor.** For odd `h` and every completely multiplicative sign,
`Σ_{n ≤ M, f(n) = f(n+h)} 1/n ≥ (1/3) log M − (h+1)`. -/
theorem odd_shift_log_floor (f : CMSign) {h : ℕ} (hodd : Odd h) {M : ℕ} (hM : 0 < M) :
    Real.log M / 3 - (h + 1) ≤ logAgreeAt f h M := by
  rcases Nat.lt_or_ge M (2 * h + 2) with hsmall | hlarge
  · have hlog : Real.log M ≤ M - 1 := by
      have := Real.log_le_sub_one_of_pos (x := M) (by exact_mod_cast hM); linarith
    have hMh : (M : ℝ) < 2 * h + 2 := by exact_mod_cast hsmall
    have := logAgreeAt_nonneg f h M
    linarith
  · set N := (M - h) / 2 with hN
    have hNM : 2 * N + h ≤ M := by omega
    have hbase := logAgreeAt_two_mul_add_ge f hodd N
    have hH := log_add_one_le_harmonic N
    have hmono := logAgreeAt_mono f h hNM
    have h4 : (M : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
      have : M ≤ 4 * (N + 1) := by omega
      exact_mod_cast this
    have hlog : Real.log M ≤ Real.log 4 + Real.log ((N + 1 : ℕ) : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by exact_mod_cast hM) h4
    have hlog4 : Real.log 4 < 2 := by
      have := Real.log_lt_sub_one_of_pos (x := 4) (by norm_num) (by norm_num)
      have h2 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
      linarith
    linarith

/-! ## Even shifts: the conductor-four twins -/

/-- The character modulo `4` on odd integers, as a sign. -/
def chi4Unit (n : ℕ) : ℤˣ := if n % 4 = 3 then -1 else 1

theorem chi4Unit_mul {m n : ℕ} (hm : ¬ 2 ∣ m) (hn : ¬ 2 ∣ n) :
    chi4Unit (m * n) = chi4Unit m * chi4Unit n := by
  have hm' : m % 4 = 1 ∨ m % 4 = 3 := by omega
  have hn' : n % 4 = 1 ∨ n % 4 = 3 := by omega
  unfold chi4Unit
  rw [Nat.mul_mod]
  rcases hm' with h | h <;> rcases hn' with h' | h' <;> simp [h, h']

/-- The conductor-four twin with value `δ` at the prime `2`. -/
def chi4Twin (δ : ℤˣ) : CMSign where
  toFun n := δ ^ n.factorization 2 * chi4Unit (n / 2 ^ n.factorization 2)
  map_one' := by simp [chi4Unit]
  map_mul' := fun {m n} hm hn => by
    have hf : (m * n).factorization 2 = m.factorization 2 + n.factorization 2 := by
      rw [Nat.factorization_mul hm.ne' hn.ne']; rfl
    rw [Nat.ordCompl_mul, hf, chi4Unit_mul (Nat.not_dvd_ordCompl Nat.prime_two hm.ne')
      (Nat.not_dvd_ordCompl Nat.prime_two hn.ne')]
    exact (congrArg (· * _) (pow_add δ _ _)).trans (mul_mul_mul_comm _ _ _ _)

variable (δ : ℤˣ)

theorem chi4Twin_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) : chi4Twin δ n = chi4Unit n := by
  change δ ^ n.factorization 2 * chi4Unit (n / 2 ^ n.factorization 2) = _
  rw [Nat.factorization_eq_zero_of_not_dvd hn]
  simp

theorem chi4Twin_four_mul_add_one (j : ℕ) : chi4Twin δ (4 * j + 1) = 1 := by
  rw [chi4Twin_of_odd δ (by omega)]; simp [chi4Unit]

theorem chi4Twin_four_mul_add_three (j : ℕ) : chi4Twin δ (4 * j + 3) = -1 := by
  rw [chi4Twin_of_odd δ (by omega)]; simp [chi4Unit]

/-- **Perfect successor balance.** The steps `4j+1 → 4j+2 → 4j+3` contain exactly one agreement,
and so do `4j+3 → 4j+4 → 4j+5`. -/
theorem agree_chi4Twin_pairs (j : ℕ) :
    agree (chi4Twin δ) (4 * j + 1) + agree (chi4Twin δ) (4 * j + 2) = 1 ∧
      agree (chi4Twin δ) (4 * j + 3) + agree (chi4Twin δ) (4 * j + 4) = 1 := by
  have e1 : succSign (chi4Twin δ) (4 * j + 1) = chi4Twin δ (4 * j + 2) := by
    rw [succSign, chi4Twin_four_mul_add_one, one_mul]
  have e2 : succSign (chi4Twin δ) (4 * j + 2) = -chi4Twin δ (4 * j + 2) := by
    rw [succSign, show 4 * j + 2 + 1 = 4 * j + 3 by ring, chi4Twin_four_mul_add_three, mul_neg_one]
  have e3 : succSign (chi4Twin δ) (4 * j + 3) = -chi4Twin δ (4 * j + 4) := by
    rw [succSign, chi4Twin_four_mul_add_three, show 4 * j + 3 + 1 = 4 * j + 4 by ring, neg_one_mul]
  have e4 : succSign (chi4Twin δ) (4 * j + 4) = chi4Twin δ (4 * j + 4) := by
    rw [succSign, show 4 * j + 4 + 1 = 4 * (j + 1) + 1 by ring, chi4Twin_four_mul_add_one, mul_one]
  refine ⟨?_, ?_⟩
  · rw [agree, agree, e1, e2]
    rcases Int.units_eq_one_or (chi4Twin δ (4 * j + 2)) with h | h <;> simp [h]
  · rw [agree, agree, e3, e4]
    rcases Int.units_eq_one_or (chi4Twin δ (4 * j + 4)) with h | h <;> simp [h]

/-- `A(4J) = 2J`: the twin keeps its sign at exactly half of the steps. -/
theorem agreeCount_chi4Twin_four_mul (J : ℕ) : agreeCount (chi4Twin δ) (4 * J) = 2 * J := by
  induction J with
  | zero => simp [agreeCount]
  | succ J ih =>
    obtain ⟨h1, h2⟩ := agree_chi4Twin_pairs δ J
    have hs : ∀ N, agreeCount (chi4Twin δ) (N + 1) = agreeCount (chi4Twin δ) N +
        agree (chi4Twin δ) (N + 1) := fun N => by
      rw [agreeCount, sum_Icc_succ_top (by omega), ← agreeCount]
    rw [show 4 * (J + 1) = 4 * J + 1 + 1 + 1 + 1 by ring, hs, hs, hs, hs, ih,
      show 4 * J + 1 + 1 = 4 * J + 2 by ring, show 4 * J + 2 + 1 = 4 * J + 3 by ring,
      show 4 * J + 3 + 1 = 4 * J + 4 by ring]
    omega

/-- **Perfect successor balance.** `C(4J) = 0`. -/
theorem succCorr_chi4Twin_four_mul (J : ℕ) : succCorr (chi4Twin δ) (4 * J) = 0 := by
  rw [succCorr_eq, agreeCount_chi4Twin_four_mul]; push_cast; ring

/-- Lag two at odd positions always disagrees for the twin. -/
theorem agreeAt_chi4Twin_two_odd (j : ℕ) : agreeAt (chi4Twin δ) 2 (2 * j + 1) = 0 := by
  rcases Nat.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [agreeAt, shiftSign, show 2 * (k + k) + 1 = 4 * k + 1 by ring,
      show 4 * k + 1 + 2 = 4 * k + 3 by ring, chi4Twin_four_mul_add_one,
      chi4Twin_four_mul_add_three]
    simp
  · rw [agreeAt, shiftSign, show 2 * (2 * k + 1) + 1 = 4 * k + 3 by ring,
      show 4 * k + 3 + 2 = 4 * (k + 1) + 1 by ring, chi4Twin_four_mul_add_one,
      chi4Twin_four_mul_add_three]
    simp

/-- Lag two at even positions is lag one at half the position, for every completely
multiplicative sign. -/
theorem agreeAt_two_two_mul (f : CMSign) {m : ℕ} (hm : 0 < m) :
    agreeAt f 2 (2 * m) = agree f m := by
  have : shiftSign f 2 (2 * m) = succSign f m := by
    rw [shiftSign, succSign, show 2 * m + 2 = 2 * (m + 1) by ring, f.map_mul two_pos hm,
      f.map_mul two_pos (by omega), mul_mul_mul_comm, Int.units_mul_self, one_mul]
  rw [agreeAt, agree, this]

theorem logAgreeAt_two_mul_add_one_eq (f : CMSign) (M : ℕ)
    (hodd : ∀ j, agreeAt f 2 (2 * j + 1) = 0) :
    logAgreeAt f 2 (2 * M + 1) = logAgree f M / 2 := by
  rw [logAgreeAt, sum_Icc_two_mul_add_one (fun k => (agreeAt f 2 k : ℝ) / k), logAgree,
    Finset.sum_div]
  have h1 := hodd 0
  simp only [mul_zero, zero_add] at h1
  rw [h1]
  simp only [Nat.cast_zero, zero_div, zero_add]
  refine sum_congr rfl fun m hm => ?_
  rw [hodd m, agreeAt_two_two_mul f (by simp at hm; omega)]
  push_cast
  ring

/-- **Lag-two floor.** `Σ_{n ≤ M, f(n) = f(n+2)} 1/n ≥ (1/6) log M − 1`. -/
theorem lag_two_log_floor (f : CMSign) {M : ℕ} (hM : 0 < M) :
    Real.log M / 6 - 1 ≤ logAgreeAt f 2 M := by
  rcases Nat.lt_or_ge M 2 with hsmall | hlarge
  · have : M = 1 := by omega
    subst this
    simp only [Nat.cast_one, Real.log_one, zero_div, zero_sub]
    linarith [logAgreeAt_nonneg f 2 1]
  set K := M / 2 with hK
  have hK1 : 0 < K := by omega
  have hsplit : logAgree f K / 2 ≤ logAgreeAt f 2 M := by
    have hle : ∑ m ∈ Icc 1 K, (agreeAt f 2 (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ) ≤ logAgreeAt f 2 M := by
      rw [logAgreeAt]
      have hinj : Set.InjOn (fun n => 2 * n) (Icc 1 K : Finset ℕ) := fun a _ b _ hab => by
        simp only at hab; omega
      rw [← sum_image (f := fun k => (agreeAt f 2 k : ℝ) / k) hinj]
      refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => by positivity
      intro k hk
      simp only [mem_image, mem_Icc] at hk ⊢
      obtain ⟨n, hn, rfl⟩ := hk
      omega
    have heq : ∑ m ∈ Icc 1 K, (agreeAt f 2 (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ) = logAgree f K / 2 := by
      rw [logAgree, Finset.sum_div]
      refine sum_congr rfl fun m hm => ?_
      rw [agreeAt_two_two_mul f (by simp at hm; omega)]
      push_cast; ring
    linarith
  have hfloor := one_third_log_floor f hK1
  have hlog : Real.log M ≤ Real.log 3 + Real.log K := by
    rw [← Real.log_mul (by norm_num) (by exact_mod_cast hK1.ne')]
    exact Real.log_le_log (by exact_mod_cast hM) (by
      have : M ≤ 3 * K := by omega
      exact_mod_cast this)
  have hlog3 : Real.log 3 < 2 := by
    have := Real.log_lt_sub_one_of_pos (x := 3) (by norm_num) (by norm_num); linarith
  linarith

/-- One period of the twin contributes at most `1/(4j+1) + 1/(4j+3)` to the logarithmic mass. -/
theorem block_logAgree_chi4Twin_le (J : ℕ) :
    logAgree (chi4Twin δ) (4 * J + 4) ≤
      logAgree (chi4Twin δ) (4 * J) + (1 / (4 * J + 1) + 1 / (4 * J + 3) : ℝ) := by
  obtain ⟨h1, h2⟩ := agree_chi4Twin_pairs δ J
  have hs : ∀ N, logAgree (chi4Twin δ) (N + 1) = logAgree (chi4Twin δ) N +
      (agree (chi4Twin δ) (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) := fun N => by
    rw [logAgree, sum_Icc_succ_top (by omega), ← logAgree]
  rw [show 4 * J + 4 = 4 * J + 1 + 1 + 1 + 1 by ring, hs, hs, hs, hs,
    show 4 * J + 1 + 1 = 4 * J + 2 by ring, show 4 * J + 2 + 1 = 4 * J + 3 by ring,
    show 4 * J + 3 + 1 = 4 * J + 4 by ring]
  have hA : (agree (chi4Twin δ) (4 * J + 1) : ℝ) + agree (chi4Twin δ) (4 * J + 2) = 1 := by
    exact_mod_cast h1
  have hB : (agree (chi4Twin δ) (4 * J + 3) : ℝ) + agree (chi4Twin δ) (4 * J + 4) = 1 := by
    exact_mod_cast h2
  have a2 : (0 : ℝ) ≤ agree (chi4Twin δ) (4 * J + 2) := Nat.cast_nonneg _
  have a4 : (0 : ℝ) ≤ agree (chi4Twin δ) (4 * J + 4) := Nat.cast_nonneg _
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have eA : (agree (chi4Twin δ) (4 * J + 1) : ℝ) / ((4 * J + 1 : ℕ) : ℝ) +
      (agree (chi4Twin δ) (4 * J + 2) : ℝ) / ((4 * J + 2 : ℕ) : ℝ) ≤ 1 / (4 * J + 1) := by
    push_cast
    have : (agree (chi4Twin δ) (4 * J + 2) : ℝ) / (4 * J + 2) ≤
        (agree (chi4Twin δ) (4 * J + 2) : ℝ) / (4 * J + 1) :=
      div_le_div_of_nonneg_left a2 (by positivity) (by linarith)
    have hsum : (agree (chi4Twin δ) (4 * J + 1) : ℝ) / (4 * J + 1) +
        (agree (chi4Twin δ) (4 * J + 2) : ℝ) / (4 * J + 1) = 1 / (4 * J + 1) := by
      rw [← add_div, hA]
    linarith
  have eB : (agree (chi4Twin δ) (4 * J + 3) : ℝ) / ((4 * J + 3 : ℕ) : ℝ) +
      (agree (chi4Twin δ) (4 * J + 4) : ℝ) / ((4 * J + 4 : ℕ) : ℝ) ≤ 1 / (4 * J + 3) := by
    push_cast
    have : (agree (chi4Twin δ) (4 * J + 4) : ℝ) / (4 * J + 4) ≤
        (agree (chi4Twin δ) (4 * J + 4) : ℝ) / (4 * J + 3) :=
      div_le_div_of_nonneg_left a4 (by positivity) (by linarith)
    have hsum : (agree (chi4Twin δ) (4 * J + 3) : ℝ) / (4 * J + 3) +
        (agree (chi4Twin δ) (4 * J + 4) : ℝ) / (4 * J + 3) = 1 / (4 * J + 3) := by
      rw [← add_div, hB]
    linarith
  linarith

/-- The twin's logarithmic lag-one mass: `L(4(J+1)) ≤ H_J/2 + 4/3`. -/
theorem logAgree_chi4Twin_le (J : ℕ) :
    logAgree (chi4Twin δ) (4 * (J + 1)) ≤ (harmonic J : ℝ) / 2 + 4 / 3 := by
  induction J with
  | zero =>
    have h := block_logAgree_chi4Twin_le δ 0
    simp only [mul_zero, zero_add, Nat.cast_zero] at h ⊢
    have h0 : logAgree (chi4Twin δ) 0 = 0 := by simp [logAgree]
    rw [h0] at h
    simp only [harmonic_zero, Rat.cast_zero, zero_div, zero_add]
    norm_num at h ⊢
    linarith
  | succ J ih =>
    have h := block_logAgree_chi4Twin_le δ (J + 1)
    rw [show 4 * (J + 1) + 4 = 4 * (J + 1 + 1) by ring] at h
    rw [harmonic_succ]
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hb : (1 / (4 * ((J + 1 : ℕ) : ℝ) + 1) + 1 / (4 * ((J + 1 : ℕ) : ℝ) + 3) : ℝ) ≤
        1 / (2 * ((J : ℝ) + 1)) := by
      push_cast
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast at h hb ih ⊢
    have : ((J : ℝ) + 1)⁻¹ / 2 = 1 / (2 * ((J : ℝ) + 1)) := by field_simp
    rw [add_div, this]
    linarith

/-- **The even shift breaks the odd-shift floor.** The conductor-four twin has lag-two
logarithmic agreement mass at most `(1/4) log M + 1`. -/
theorem chi4Twin_lag_two_log_le {M : ℕ} (hM : 0 < M) :
    logAgreeAt (chi4Twin δ) 2 M ≤ Real.log M / 4 + 1 := by
  set J := M / 8 with hJ
  have hMle : M ≤ 2 * (4 * (J + 1)) + 1 := by omega
  have h1 := logAgreeAt_mono (chi4Twin δ) 2 hMle
  rw [logAgreeAt_two_mul_add_one_eq (chi4Twin δ) _ (agreeAt_chi4Twin_two_odd δ)] at h1
  have h2 := logAgree_chi4Twin_le δ J
  have hH : (harmonic J : ℝ) ≤ 1 + Real.log M := by
    rcases Nat.eq_zero_or_pos J with h0 | hJ0
    · rw [h0]; simp only [harmonic_zero, Rat.cast_zero]
      have : (0 : ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
      linarith
    · have := harmonic_le_one_add_log J
      have hJM : Real.log J ≤ Real.log M :=
        Real.log_le_log (by exact_mod_cast hJ0) (by exact_mod_cast (show J ≤ M by omega))
      linarith
  linarith

/-- **Lag-two bracket.** The lag-two floor lies between `1/6` and `1/4`. -/
theorem lag_two_bracket :
    (∀ f : CMSign, ∀ M : ℕ, 0 < M → Real.log M / 6 - 1 ≤ logAgreeAt f 2 M) ∧
      ∀ M : ℕ, 0 < M → logAgreeAt (chi4Twin 1) 2 M ≤ Real.log M / 4 + 1 :=
  ⟨fun f _ hM => lag_two_log_floor f hM, fun _ hM => chi4Twin_lag_two_log_le 1 hM⟩

/-! ## The alternating control -/

/-- The alternating sign `(-1)^n`. It is not multiplicative. -/
def altSign (n : ℕ) : ℤˣ := if Even n then 1 else -1

theorem alternating_succSign (n : ℕ) : succSign altSign n = -1 := by
  rcases Nat.even_or_odd n with h | h
  · have h' : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr h.add_one
    simp [succSign, altSign, h, h']
  · have h' : Even (n + 1) := h.add_one
    have h'' : ¬ Even n := Nat.not_even_iff_odd.mpr h
    simp [succSign, altSign, h', h'']

/-- The alternating sign never keeps its sign: its logarithmic agreement mass is `0`. -/
theorem alternating_logAgree (N : ℕ) : logAgree altSign N = 0 := by
  refine sum_eq_zero fun n _ => ?_
  simp [agree, alternating_succSign]

/-- The alternating sign violates the dilation cocycle at `m = 2`, `n = 1`. -/
theorem alternating_not_cocycle : ¬ IsDilationCocycleAt (succSign altSign) 2 := by
  intro h
  have := h 1 one_pos
  simp only [prod_range_succ, alternating_succSign] at this
  exact units_neg_one_ne_one (by simpa using this.symm)

end GaloisForLFunctions.SignedSuccessorArithmetic
