import GaloisForLFunctions.PrimeTorusTheory.TarryEscottWords
import Mathlib.Data.Nat.Choose.Lucas

/-!
# The floor of a word and of a polynomial phase

Two exact limits for any argument that treats `t log(x+a)/2π` on a block as a polynomial phase of
degree `k`.

* `card_letters_ge`: a nonzero integer word whose moments vanish through order `k` has at least
  `k+2` letters. So a single word certifies misalignment at precision at most `1/(2(k+2))`.
* `mem_range_of_consecutive`: a phase of degree `k` that is an integer at `k+1` consecutive points
  is an integer everywhere, and `card_nonintegers_ge`: otherwise at least one point in each window
  of `k+1` is not an integer.
* `card_filter_halfChoose`: this is sharp. The phase `C(a, 2^m-1)/2` of degree `k = 2^m-1` is not
  integer valued, and it fails to be an integer exactly on `a ≡ -1 mod 2^m`, by Lucas' theorem.

Hence `sum_exp_halfChoose`: a degree `k` phase which is far from every integer valued polynomial can
still have exponential sum `N(1 - 2/(k+1))`. A bound for a polynomial phase on one block therefore
saves at most `2/(k+1)` unless it excludes the denominators of the binomial basis, and those are
not excluded by the size of the coefficients of degree `k`.
-/

open Finset

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-! ### Letters of a word -/

/-- The letters of `c` in `[0, M]`. -/
def letters (M : ℕ) (c : ℕ → ℤ) : Finset ℕ := (range (M + 1)).filter fun a => c a ≠ 0

theorem mem_letters {M : ℕ} {c : ℕ → ℤ} {a : ℕ} : a ∈ letters M c ↔ a ≤ M ∧ c a ≠ 0 := by
  simp [letters]
  omega

/-- `a C(a,j) = (j+1) C(a,j+1) + j C(a,j)`. -/
theorem cast_mul_choose (a j : ℕ) :
    (a : ℤ) * (a.choose j : ℤ) = ((j : ℤ) + 1) * (a.choose (j + 1) : ℤ) + (j : ℤ) * (a.choose j : ℤ) := by
  rcases le_or_gt j a with h | h
  · have h1 := Nat.choose_succ_right_eq a j
    have h2 : ((a.choose (j + 1) : ℤ)) * ((j : ℤ) + 1) = (a.choose j : ℤ) * ((a : ℤ) - j) := by
      rw [← Nat.cast_sub h]
      exact_mod_cast h1
    linarith
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : a < j + 1)]
    simp

/-- Multiplying a word by the linear factor `a - a₀` lowers the order of its moments by one. -/
theorem binomMoment_mul_sub (M : ℕ) (c : ℕ → ℤ) (a₀ j : ℕ) :
    binomMoment M (fun a => c a * ((a : ℤ) - a₀)) j =
      ((j : ℤ) + 1) * binomMoment M c (j + 1) + ((j : ℤ) - a₀) * binomMoment M c j := by
  unfold binomMoment
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  linear_combination (c a) * cast_mul_choose a j

theorem two_le_card_letters {M : ℕ} {c : ℕ → ℤ} (hs : ∀ a, M < a → c a = 0)
    (hne : ∃ a, c a ≠ 0) (h0 : binomMoment M c 0 = 0) : 2 ≤ (letters M c).card := by
  obtain ⟨a, ha⟩ := hne
  have haM : a ≤ M := by
    by_contra h
    exact ha (hs a (by omega))
  have hmem : a ∈ letters M c := mem_letters.mpr ⟨haM, ha⟩
  by_contra hcard
  have hone : (letters M c).card = 1 := by
    have := Finset.card_pos.mpr ⟨a, hmem⟩
    omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hone
  have hbmem : b ∈ letters M c := by rw [hb]; exact mem_singleton_self b
  have hsum : ∑ x ∈ range (M + 1), c x = c b := by
    have hsub : ∀ x ∈ range (M + 1), x ≠ b → c x = 0 := by
      intro x hx hxb
      by_contra hc
      have : x ∈ letters M c := mem_letters.mpr ⟨Nat.lt_succ_iff.mp (mem_range.mp hx), hc⟩
      rw [hb] at this
      exact hxb (mem_singleton.mp this)
    refine sum_eq_single_of_mem b ?_ hsub
    exact mem_range.mpr (Nat.lt_succ_iff.mpr (mem_letters.mp hbmem).1)
  unfold binomMoment at h0
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one] at h0
  rw [hsum] at h0
  exact (mem_letters.mp hbmem).2 h0

/-- **A word of order `k` has at least `k+2` letters.** Each letter is removed by a linear factor,
which lowers the order by one. -/
theorem card_letters_ge {M : ℕ} :
    ∀ (k : ℕ) (c : ℕ → ℤ), (∀ a, M < a → c a = 0) → (∃ a, c a ≠ 0) →
      (∀ j ≤ k, binomMoment M c j = 0) → k + 2 ≤ (letters M c).card := by
  intro k
  induction k with
  | zero => exact fun c hs hne hm => two_le_card_letters hs hne (hm 0 le_rfl)
  | succ k ih =>
    intro c hs hne hm
    have h2 := two_le_card_letters hs hne (hm 0 (Nat.zero_le _))
    obtain ⟨a₀, ha₀, b, hb, hne'⟩ := Finset.one_lt_card.mp (by omega : 1 < (letters M c).card)
    have hfactor : ∀ a : ℕ, (a : ℤ) - a₀ ≠ 0 ↔ a ≠ a₀ := by
      intro a
      rw [sub_ne_zero, Ne, Ne, Nat.cast_inj]
    set c' : ℕ → ℤ := fun a => c a * ((a : ℤ) - a₀) with hc'
    have hlet : letters M c' = (letters M c).erase a₀ := by
      ext a
      simp only [mem_letters, mem_erase, hc', mul_ne_zero_iff, hfactor]
      tauto
    have hmem : a₀ ∈ letters M c := ha₀
    have := ih c' (fun a ha => by simp [hc', hs a ha])
      ⟨b, mul_ne_zero (mem_letters.mp hb).2 ((hfactor b).mpr hne'.symm)⟩
      (fun j hj => by
        rw [hc', binomMoment_mul_sub, hm (j + 1) (by omega), hm j (by omega)]
        ring)
    rw [hlet, card_erase_of_mem hmem] at this
    omega

/-! ### Integrality of a polynomial phase -/

/-- The integers inside the reals. -/
abbrev integers : Subring ℝ := (Int.castRingHom ℝ).range

/-- `Δ^{k+1} f = 0` determines the next value from the `k+1` before it, with integer coefficients. -/
theorem mem_forward {k : ℕ} {f : ℕ → ℝ} (hf : ∀ n, (fwdDiff (1 : ℕ))^[k + 1] f n = 0) (n : ℕ)
    (h : ∀ i ≤ k, f (n + i) ∈ integers) : f (n + (k + 1)) ∈ integers := by
  have h0 := hf n
  rw [fwdDiff_iter_eq_sum_shift, sum_range_succ] at h0
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, one_smul,
    smul_eq_mul] at h0
  have e : f (n + (k + 1)) = -∑ i ∈ range (k + 1),
      ((-1 : ℤ) ^ (k + 1 - i) * ((k + 1).choose i : ℤ)) • f (n + i) := by
    linarith
  rw [e]
  exact neg_mem (sum_mem fun i hi =>
    zsmul_mem (h i (Nat.lt_succ_iff.mp (mem_range.mp hi))) _)

/-- The same recurrence read backwards: the coefficient of `f n` is `±1`. -/
theorem mem_backward {k : ℕ} {f : ℕ → ℝ} (hf : ∀ n, (fwdDiff (1 : ℕ))^[k + 1] f n = 0) (n : ℕ)
    (h : ∀ i ≤ k, f (n + (i + 1)) ∈ integers) : f n ∈ integers := by
  have h0 := hf n
  rw [fwdDiff_iter_eq_sum_shift, sum_range_succ'] at h0
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, zero_smul, add_zero, Nat.sub_zero,
    smul_eq_mul] at h0
  have hsum : ∑ i ∈ range (k + 1),
      ((-1 : ℤ) ^ (k + 1 - (i + 1)) * ((k + 1).choose (i + 1) : ℤ)) • f (n + (i + 1)) ∈ integers :=
    sum_mem fun i hi => zsmul_mem (h i (Nat.lt_succ_iff.mp (mem_range.mp hi))) _
  rcases neg_one_pow_eq_or ℤ (k + 1) with hs | hs
  · rw [hs, one_smul] at h0
    have e : f n = -∑ i ∈ range (k + 1),
        ((-1 : ℤ) ^ (k + 1 - (i + 1)) * ((k + 1).choose (i + 1) : ℤ)) • f (n + (i + 1)) := by
      linarith
    rw [e]
    exact neg_mem hsum
  · rw [hs, neg_smul, one_smul] at h0
    have e : f n = ∑ i ∈ range (k + 1),
        ((-1 : ℤ) ^ (k + 1 - (i + 1)) * ((k + 1).choose (i + 1) : ℤ)) • f (n + (i + 1)) := by
      linarith
    rw [e]
    exact hsum

/-- **Rigidity.** A phase of degree `k` that is an integer at `k+1` consecutive points is integer
valued. -/
theorem mem_range_of_consecutive {k : ℕ} {f : ℕ → ℝ} (hf : ∀ n, (fwdDiff (1 : ℕ))^[k + 1] f n = 0) {a : ℕ}
    (h : ∀ i ≤ k, f (a + i) ∈ integers) : ∀ n, f n ∈ integers := by
  have hfwd : ∀ d, f (a + d) ∈ integers := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      rcases le_or_gt d k with hd | hd
      · exact h d hd
      · obtain ⟨e, rfl⟩ : ∃ e, d = e + (k + 1) := ⟨d - (k + 1), by omega⟩
        have := mem_forward hf (a + e) (fun i hi => by
          rw [add_assoc]
          exact ih (e + i) (by omega))
        rwa [add_assoc] at this
  have hbwd : ∀ d, d ≤ a → f (a - d) ∈ integers := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro hd
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · simpa using hfwd 0
      · refine mem_backward hf (a - d) fun i _ => ?_
        rcases le_or_gt (i + 1) d with hid | hid
        · have e : a - d + (i + 1) = a - (d - (i + 1)) := by omega
          rw [e]
          exact ih _ (by omega) (by omega)
        · have e : a - d + (i + 1) = a + (i + 1 - d) := by omega
          rw [e]
          exact hfwd _
  intro n
  rcases le_or_gt a n with han | han
  · have e : n = a + (n - a) := by omega
    rw [e]
    exact hfwd _
  · have e : n = a - (a - n) := by omega
    rw [e]
    exact hbwd _ (by omega)

open Classical in
/-- **Floor.** A phase of degree `k` that is not integer valued misses the integers at least once
in each window of `k+1` consecutive points. -/
theorem card_nonintegers_ge {k : ℕ} {f : ℕ → ℝ} (hf : ∀ n, (fwdDiff (1 : ℕ))^[k + 1] f n = 0)
    (hn : ∃ n, f n ∉ integers) (q : ℕ) :
    q ≤ ((range ((k + 1) * q)).filter fun a => f a ∉ integers).card := by
  induction q with
  | zero => simp
  | succ q ih =>
    obtain ⟨i, hi, hbad⟩ : ∃ i ≤ k, f ((k + 1) * q + i) ∉ integers := by
      by_contra hcon
      push Not at hcon
      obtain ⟨n, hn⟩ := hn
      exact hn (mem_range_of_consecutive hf hcon n)
    have hnew : (k + 1) * q + i ∉ (range ((k + 1) * q)).filter fun a => f a ∉ integers := by
      simp
    have hsub : insert ((k + 1) * q + i) ((range ((k + 1) * q)).filter fun a => f a ∉ integers) ⊆
        (range ((k + 1) * (q + 1))).filter fun a => f a ∉ integers := by
      intro x hx
      rw [mem_insert] at hx
      rcases hx with rfl | hx
      · refine mem_filter.mpr ⟨mem_range.mpr ?_, hbad⟩
        rw [Nat.mul_succ]
        omega
      · obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
        refine mem_filter.mpr ⟨mem_range.mpr ?_, hx2⟩
        have := mem_range.mp hx1
        rw [Nat.mul_succ]
        omega
    have := card_le_card hsub
    rw [card_insert_of_notMem hnew] at this
    omega

/-! ### Sharpness: the binomial denominators -/

/-- `C(a, 2^m - 1)` is odd exactly when `2^m ∣ a + 1`. -/
theorem odd_choose_two_pow_sub_one (m a : ℕ) :
    Odd (a.choose (2 ^ m - 1)) ↔ 2 ^ m ∣ a + 1 := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    have hq : 0 < 2 ^ m := by positivity
    have hk1 : (2 ^ (m + 1) - 1) % 2 = 1 := by
      rw [pow_succ]
      omega
    have hk2 : (2 ^ (m + 1) - 1) / 2 = 2 ^ m - 1 := by
      rw [pow_succ]
      omega
    have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := a) (k := 2 ^ (m + 1) - 1) (p := 2)
    rw [hk1, hk2] at h
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha
    · rw [ha, Nat.choose_zero_succ] at h
      simp only [Nat.cast_zero, zero_mul] at h
      constructor
      · intro hodd
        have := Nat.odd_iff.mp hodd
        unfold Int.ModEq at h
        omega
      · intro hd
        exfalso
        have : 2 ∣ a + 1 := (dvd_pow_self 2 (by omega)).trans hd
        omega
    · rw [ha, Nat.choose_self] at h
      simp only [Nat.cast_one, one_mul] at h
      unfold Int.ModEq at h
      have e : a + 1 = 2 * (a / 2 + 1) := by omega
      have hd : 2 ^ (m + 1) ∣ a + 1 ↔ 2 ^ m ∣ a / 2 + 1 := by
        rw [e, pow_succ, mul_comm (2 ^ m) 2, Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)]
        simp only [Nat.mul_add_div (by norm_num : 0 < 2)]
      rw [hd, ← ih, Nat.odd_iff, Nat.odd_iff]
      omega

/-- The exact sum of the sign `(-1)^{C(a, 2^m - 1)}`. -/
theorem sum_neg_one_pow_choose (m N : ℕ) :
    ∑ a ∈ range N, (-1 : ℤ) ^ (a.choose (2 ^ m - 1)) = (N : ℤ) - 2 * ((N / 2 ^ m : ℕ) : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, Nat.succ_div]
    by_cases hd : 2 ^ m ∣ N + 1
    · have hodd := (odd_choose_two_pow_sub_one m N).mpr hd
      rw [hodd.neg_one_pow, if_pos hd]
      push_cast
      ring
    · have heven : Even (N.choose (2 ^ m - 1)) := by
        rw [← Nat.not_odd_iff_even, odd_choose_two_pow_sub_one]
        exact hd
      rw [heven.neg_one_pow, if_neg hd]
      push_cast
      ring

/-- The exotic phase of degree `2^m - 1`. -/
def halfChoose (m a : ℕ) : ℝ := (a.choose (2 ^ m - 1) : ℝ) / 2

theorem fwdDiff_iter_halfChoose (j i : ℕ) :
    (fwdDiff (1 : ℕ))^[j] (fun a : ℕ => (a.choose (j + i) : ℝ) / 2) = fun a => (a.choose i : ℝ) / 2 := by
  induction j generalizing i with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    have e : fwdDiff (1 : ℕ) (fun a : ℕ => (a.choose (j + 1 + i) : ℝ) / 2) =
        fun a : ℕ => (a.choose (j + i) : ℝ) / 2 := by
      funext a
      have h := Nat.choose_succ_succ' a (j + i)
      simp only [fwdDiff]
      rw [show j + 1 + i = j + i + 1 by omega, h]
      push_cast
      ring
    rw [e, ih]

/-- `halfChoose` is a phase of degree `2^m - 1`. -/
theorem fwdDiff_iter_succ_halfChoose (m n : ℕ) :
    (fwdDiff (1 : ℕ))^[2 ^ m - 1 + 1] (halfChoose m) n = 0 := by
  rw [Function.iterate_succ_apply']
  have e : halfChoose m = fun a : ℕ => (a.choose (2 ^ m - 1 + 0) : ℝ) / 2 := by
    funext a
    simp [halfChoose]
  rw [e, fwdDiff_iter_halfChoose]
  simp [fwdDiff]

theorem halfChoose_mem_iff (m a : ℕ) : halfChoose m a ∈ integers ↔ ¬ 2 ^ m ∣ a + 1 := by
  rw [← odd_choose_two_pow_sub_one, Nat.not_odd_iff_even]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : (a.choose (2 ^ m - 1) : ℝ) = 2 * (z : ℝ) := by
      have : (z : ℝ) = (a.choose (2 ^ m - 1) : ℝ) / 2 := by simpa [halfChoose] using hz
      rw [this]
      ring
    have hzz : ((a.choose (2 ^ m - 1) : ℕ) : ℤ) = 2 * z := by exact_mod_cast hz'
    rw [Nat.even_iff]
    omega
  · rintro ⟨r, hr⟩
    refine ⟨(r : ℤ), ?_⟩
    simp only [eq_intCast, Int.cast_natCast, halfChoose, hr]
    push_cast
    ring

open Classical in
/-- **The floor is sharp.** The phase `C(a, 2^m - 1)/2` misses the integers exactly once in each
period `2^m`. -/
theorem card_filter_halfChoose (m q : ℕ) :
    ((range (2 ^ m * q)).filter fun a => halfChoose m a ∉ integers).card = q := by
  have hpos : 0 < 2 ^ m := by positivity
  induction q with
  | zero => simp
  | succ q ih =>
    have e : 2 ^ m * (q + 1) = 2 ^ m * q + 2 ^ m := by ring
    rw [e, range_add, filter_union, card_union_of_disjoint, ih]
    · congr 1
      have hmap : ((range (2 ^ m)).map (addLeftEmbedding (2 ^ m * q))).filter
          (fun a => halfChoose m a ∉ integers) = {2 ^ m * q + (2 ^ m - 1)} := by
        ext x
        simp only [mem_filter, mem_map, mem_range, addLeftEmbedding_apply, mem_singleton,
          halfChoose_mem_iff, not_not]
        constructor
        · rintro ⟨⟨i, hi, rfl⟩, hd⟩
          have hdvd : 2 ^ m ∣ i + 1 := by
            have : 2 ^ m ∣ 2 ^ m * q + (i + 1) := by rwa [← add_assoc]
            exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp this
          have := Nat.le_of_dvd (by omega) hdvd
          omega
        · rintro rfl
          refine ⟨⟨2 ^ m - 1, by omega, rfl⟩, ?_⟩
          have : 2 ^ m * q + (2 ^ m - 1) + 1 = 2 ^ m * (q + 1) := by
            rw [Nat.mul_succ]
            omega
          rw [this]
          exact dvd_mul_right _ _
      rw [hmap, card_singleton]
    · refine disjoint_filter_filter ?_
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨i, _, rfl⟩ := mem_map.mp hx'
      have := mem_range.mp hx
      simp only [addLeftEmbedding_apply] at this
      omega

/-- **The sum.** The exponential sum of the exotic phase is `N - 2⌊N/2^m⌋`: the saving on a
polynomial phase of degree `k = 2^m - 1` that is not integer valued can be as small as `2/(k+1)`. -/
theorem sum_exp_halfChoose (m N : ℕ) :
    ∑ a ∈ range N, Complex.exp (2 * Real.pi * Complex.I * (halfChoose m a : ℝ)) =
      (N : ℂ) - 2 * ((N / 2 ^ m : ℕ) : ℂ) := by
  have h := sum_neg_one_pow_choose m N
  have hc : (((∑ a ∈ range N, (-1 : ℤ) ^ (a.choose (2 ^ m - 1))) : ℤ) : ℂ) =
      (N : ℂ) - 2 * ((N / 2 ^ m : ℕ) : ℂ) := by
    rw [h]
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat]
  rw [← hc]
  push_cast
  refine sum_congr rfl fun a _ => ?_
  have e : 2 * (Real.pi : ℂ) * Complex.I * ((halfChoose m a : ℝ) : ℂ) =
      ((a.choose (2 ^ m - 1) : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    simp only [halfChoose]
    push_cast
    ring
  rw [e, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

end

end GaloisForLFunctions.PrimeTorusTheory
