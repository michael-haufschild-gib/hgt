import GaloisForLFunctions.PrimeTorusTheory.TarryEscottWords

/-!
# Tarry–Escott words forbid alignment

The phases `n^{it}` are multiplicative, and the integers are also an additive set. A word `c` has
`Σ_a c(a) log(x + a) = Σ_{j ≥ e} β_j Δ^j log(x)`, of size `≍ |β_e| (e−1)!/x^e`, and it varies slowly in `x`. So at a suitable integer
`x` the phase `t Σ_a c(a) log(x + a)/2π` sits at distance `≥ ¼` from the integers, while alignment of every integer in
`[x, x + M]` to within `ε` would put it within `(M + 1) ε` of the integers.

**Theorem** (`exists_not_aligned`). If a word with vanishing moments up to `k` exists (`exists_word`), all its nonzero moments
start by `E` (`sum_primes_le_of_moments_vanish`), and `|t|` lies between `3π x₀^E` and `x₂^{k+1}/(M+1)^{k+2}`, then some integer
`n ≤ x₂ + M` has `t log n/2π` at distance more than `ε` from the integers, for every `ε < 1/(4(M + 1))`.

With `M ≈ log t/(log log t)²` this reaches lengths `exp(√(log t) (log log t)^{3/2})`, below the Vinogradov–Korobov length, with
precision a negative power of `log t`. The pigeonhole obstruction `le_of_aligned` has precision a negative power of `t` at those lengths.

It uses that **every** integer in a short interval is a product of the generators. The statement fails over `𝔽_q[T]`, where the
norm does not move under an additive shift of lower degree, and on systems whose integers are rounded.
-/

open Finset Real
open scoped fwdDiff

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The logarithm of a word at `x`. -/
def wordLog (M : ℕ) (c : ℕ → ℤ) (x : ℝ) : ℝ :=
  ∑ a ∈ range (M + 1), (c a : ℝ) * Real.log (x + a)

/-- The difference `Δ^j log`. -/
def logDiff (j : ℕ) (x : ℝ) : ℝ := (fwdDiff (1 : ℝ))^[j] Real.log x

theorem wordLog_eq (M : ℕ) (c : ℕ → ℤ) (x : ℝ) :
    wordLog M c x = ∑ j ∈ range (M + 1), (binomMoment M c j : ℝ) * logDiff j x :=
  sum_word_shift_eq M c Real.log x

theorem logDiff_step (j : ℕ) (x : ℝ) : logDiff j (x + 1) - logDiff j x = logDiff (j + 1) x := by
  unfold logDiff
  rw [Function.iterate_succ_apply']
  rfl

/-- A finite geometric tail. -/
theorem sum_filter_gt_pow_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1 / 2) (e M : ℕ) :
    ∑ j ∈ (range (M + 1)).filter (fun j => e < j), q ^ j ≤ 2 * q ^ (e + 1) := by
  classical
  have hpos : 0 ≤ q ^ (e + 1) := pow_nonneg h0 _
  have key : ∀ n : ℕ, ∑ j ∈ (range (e + 1 + n)).filter (fun j => e < j), q ^ j ≤
      2 * q ^ (e + 1) - 2 * q ^ (e + 1 + n) := by
    intro n
    induction n with
    | zero =>
      have : (range (e + 1 + 0)).filter (fun j => e < j) = ∅ := by
        refine Finset.filter_false_of_mem fun j hj => ?_
        have := Finset.mem_range.mp hj
        omega
      rw [this]
      simp
    | succ n ih =>
      rw [← add_assoc, Finset.range_add_one, Finset.filter_insert, if_pos (by omega),
        Finset.sum_insert (by simp)]
      have hq : q ^ (e + 1 + n + 1) ≤ q ^ (e + 1 + n) / 2 := by
        rw [pow_succ]
        have := pow_nonneg h0 (e + 1 + n)
        nlinarith
      linarith
  by_cases hM : e + 1 ≤ M + 1
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hM
    rw [hn]
    have := key n
    have hp : 0 ≤ q ^ (e + 1 + n) := pow_nonneg h0 _
    linarith
  · have : (range (M + 1)).filter (fun j => e < j) = ∅ := by
      refine Finset.filter_false_of_mem fun j hj => ?_
      have := Finset.mem_range.mp hj
      omega
    rw [this]
    simp [hpos]

/-- `C(m, j+1) (j+1)! ≤ m^{j+1}`. -/
theorem choose_mul_factorial_le (m j : ℕ) :
    (m.choose (j + 1) : ℝ) * ((j + 1).factorial : ℝ) ≤ (m : ℝ) ^ (j + 1) := by
  have h := Nat.descFactorial_le_pow m (j + 1)
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have h' : ((j + 1).factorial * m.choose (j + 1) : ℝ) ≤ (m : ℝ) ^ (j + 1) := by exact_mod_cast h
  linarith

/-- The data of the size estimates for a word with first nonzero moment at `e`. -/
structure LeadingMoment (M : ℕ) (c : ℕ → ℤ) (e : ℕ) : Prop where
  word : IsWord M c
  one_le : 1 ≤ e
  low : ∀ j < e, binomMoment M c j = 0
  ne : binomMoment M c e ≠ 0

/-- The leading size `|β_e| (e−1)!`. -/
def leadSize (M : ℕ) (c : ℕ → ℤ) (e : ℕ) : ℝ := |(binomMoment M c e : ℝ)| * ((e - 1).factorial : ℝ)

theorem LeadingMoment.one_le_abs {M e : ℕ} {c : ℕ → ℤ} (h : LeadingMoment M c e) :
    (1 : ℝ) ≤ |(binomMoment M c e : ℝ)| := by
  have : (1 : ℤ) ≤ |binomMoment M c e| := Int.one_le_abs h.ne
  exact_mod_cast this

theorem LeadingMoment.e_le {M e : ℕ} {c : ℕ → ℤ} (h : LeadingMoment M c e) : e ≤ M := by
  by_contra hcon
  apply h.ne
  unfold binomMoment
  refine Finset.sum_eq_zero fun a ha => ?_
  have := Finset.mem_range.mp ha
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem LeadingMoment.factorial_le_leadSize {M e : ℕ} {c : ℕ → ℤ} (h : LeadingMoment M c e) :
    ((e - 1).factorial : ℝ) ≤ leadSize M c e := by
  unfold leadSize
  have := h.one_le_abs
  have hf : (0 : ℝ) ≤ ((e - 1).factorial : ℝ) := by positivity
  nlinarith

theorem LeadingMoment.leadSize_le {M e : ℕ} {c : ℕ → ℤ} (h : LeadingMoment M c e) :
    leadSize M c e ≤ ((M + 1 : ℕ) : ℝ) ^ (e + 1) := by
  unfold leadSize
  have h1 : |(binomMoment M c e : ℝ)| ≤ ((M + 1).choose (e + 1) : ℝ) := by
    have := abs_binomMoment_le h.word e
    exact_mod_cast this
  have hf : ((e - 1).factorial : ℝ) ≤ ((e + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hc : (0 : ℝ) ≤ ((M + 1).choose (e + 1) : ℝ) := by positivity
  calc |(binomMoment M c e : ℝ)| * ((e - 1).factorial : ℝ)
      ≤ ((M + 1).choose (e + 1) : ℝ) * ((e + 1).factorial : ℝ) :=
        mul_le_mul h1 hf (by positivity) hc
    _ ≤ ((M + 1 : ℕ) : ℝ) ^ (e + 1) := choose_mul_factorial_le _ _

/-- The hypotheses on the base point. -/
structure BaseConditions (M e : ℕ) (x : ℝ) : Prop where
  large : 12 * ((M + 1 : ℕ) : ℝ) ^ (e + 2) ≤ x * ((e - 1).factorial : ℝ)
  e_sq : (e : ℝ) ^ 2 ≤ x
  m : 2 * ((M + 1 : ℕ) : ℝ) ≤ x
  step : 24 * ((e : ℝ) + 1) ≤ x
  pos : 1 ≤ x

theorem BaseConditions.x_pos {M e : ℕ} {x : ℝ} (h : BaseConditions M e x) : 0 < x := by
  linarith [h.pos]

/-- The tail of the Newton series. -/
theorem tail_le {M e : ℕ} {c : ℕ → ℤ} (h : LeadingMoment M c e) {x : ℝ}
    (hx : BaseConditions M e x) :
    ∑ j ∈ (range (M + 1)).filter (fun j => e < j), |(binomMoment M c j : ℝ)| * |logDiff j x| ≤
      ((e - 1).factorial : ℝ) / (6 * x ^ e) := by
  have hxpos := hx.x_pos
  set m : ℝ := ((M + 1 : ℕ) : ℝ) with hm
  have hmpos : 0 < m := by rw [hm]; positivity
  set q : ℝ := m / x with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 2 := by
    rw [hq, div_le_iff₀ hxpos]
    linarith [hx.m]
  have hterm : ∀ j ∈ (range (M + 1)).filter (fun j => e < j),
      |(binomMoment M c j : ℝ)| * |logDiff j x| ≤ m * q ^ j := by
    intro j hj
    have hej := (Finset.mem_filter.mp hj).2
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h1 : |(binomMoment M c (i + 1) : ℝ)| ≤ ((M + 1).choose (i + 1 + 1) : ℝ) := by
      have := abs_binomMoment_le h.word (i + 1)
      exact_mod_cast this
    have h2 : |logDiff (i + 1) x| ≤ (i.factorial : ℝ) / x ^ (i + 1) :=
      abs_fwdDiff_iter_log_le hxpos
    have h3 := choose_mul_factorial_le (M + 1) (i + 1)
    have hf : (i.factorial : ℝ) ≤ ((i + 1 + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hc : (0 : ℝ) ≤ ((M + 1).choose (i + 1 + 1) : ℝ) := by positivity
    calc |(binomMoment M c (i + 1) : ℝ)| * |logDiff (i + 1) x|
        ≤ ((M + 1).choose (i + 1 + 1) : ℝ) * ((i.factorial : ℝ) / x ^ (i + 1)) :=
          mul_le_mul h1 h2 (abs_nonneg _) hc
      _ = ((M + 1).choose (i + 1 + 1) : ℝ) * (i.factorial : ℝ) / x ^ (i + 1) := by ring
      _ ≤ m ^ (i + 1 + 1) / x ^ (i + 1) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact (mul_le_mul_of_nonneg_left hf hc).trans h3
      _ = m * q ^ (i + 1) := by rw [hq, div_pow, pow_succ m (i + 1)]; ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hgeo := sum_filter_gt_pow_le hq0 hq1 e M
  have hlarge : 12 * m ^ (e + 2) ≤ x * ((e - 1).factorial : ℝ) := hx.large
  have hxe : 0 < x ^ e := by positivity
  have hfinal : m * (2 * q ^ (e + 1)) ≤ ((e - 1).factorial : ℝ) / (6 * x ^ e) := by
    have e1 : m * (2 * q ^ (e + 1)) = 12 * m ^ (e + 2) / (6 * x ^ e * x) := by
      rw [hq, div_pow, pow_succ x e]
      field_simp
      ring
    have e2 : ((e - 1).factorial : ℝ) / (6 * x ^ e) = x * ((e - 1).factorial : ℝ) / (6 * x ^ e * x) := by
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hlarge (by positivity)
  calc _ ≤ m * ∑ j ∈ (range (M + 1)).filter (fun j => e < j), q ^ j := hsum
    _ ≤ m * (2 * q ^ (e + 1)) := mul_le_mul_of_nonneg_left hgeo hmpos.le
    _ ≤ _ := hfinal

/-- The Newton series splits into its leading term and a tail. -/
theorem wordLog_sub_lead_le {M e : ℕ} {c : ℕ → ℤ} (h : LeadingMoment M c e) (x : ℝ) :
    |wordLog M c x - (binomMoment M c e : ℝ) * logDiff e x| ≤
      ∑ j ∈ (range (M + 1)).filter (fun j => e < j), |(binomMoment M c j : ℝ)| * |logDiff j x| := by
  classical
  have heM : e ∈ range (M + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le h.e_le)
  rw [wordLog_eq, ← Finset.add_sum_erase _ _ heM, add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsub : (range (M + 1)).filter (fun j => e < j) ⊆ (range (M + 1)).erase e := fun j hj =>
    Finset.mem_erase.mpr ⟨(ne_of_lt (Finset.mem_filter.mp hj).2).symm, (Finset.mem_filter.mp hj).1⟩
  have hzero : ∀ j ∈ (range (M + 1)).erase e, j ∉ (range (M + 1)).filter (fun j => e < j) →
      |(binomMoment M c j : ℝ) * logDiff j x| = 0 := by
    intro j hj1 hj2
    have hj3 := Finset.mem_erase.mp hj1
    have hlt : j < e := by
      by_contra hcon
      exact hj2 (Finset.mem_filter.mpr ⟨hj3.2, by omega⟩)
    rw [h.low j hlt]
    simp
  rw [← Finset.sum_subset hsub hzero]
  exact (Finset.sum_congr rfl fun j _ => abs_mul _ _).le

/-- **Size of the word.** -/
theorem wordLog_size {M e : ℕ} {c : ℕ → ℤ} (h : LeadingMoment M c e) {x : ℝ}
    (hx : BaseConditions M e x) :
    leadSize M c e / (6 * x ^ e) ≤ |wordLog M c x| ∧
      |wordLog M c x| ≤ 7 / 6 * leadSize M c e / x ^ e := by
  have hxpos := hx.x_pos
  have hxe : 0 < x ^ e := by positivity
  have htail := (wordLog_sub_lead_le h x).trans (tail_le h hx)
  obtain ⟨i, hi⟩ : ∃ i, e = i + 1 := ⟨e - 1, by have := h.one_le; omega⟩
  have hF : ((e - 1).factorial : ℝ) ≤ leadSize M c e := h.factorial_le_leadSize
  have hup : |logDiff e x| ≤ ((e - 1).factorial : ℝ) / x ^ e := by
    subst hi
    exact abs_fwdDiff_iter_log_le hxpos
  have hlow : ((e - 1).factorial : ℝ) / (x + e) ^ e ≤ |logDiff e x| := by
    subst hi
    have := le_abs_fwdDiff_iter_log (j := i) hxpos
    have e1 : x + (i : ℝ) + 1 = x + ((i + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1] at this
    exact this
  -- `(x + e)^e ≤ 3 x^e` since `x ≥ e²`.
  have hthree : (x + e) ^ e ≤ 3 * x ^ e := by
    have hee : (0 : ℝ) < e := by exact_mod_cast h.one_le
    have h1 : (x + e) = x * (1 + e / x) := by field_simp
    rw [h1, mul_pow]
    have h2 : (1 + (e : ℝ) / x) ^ e ≤ 3 := by
      have h3 : 1 + (e : ℝ) / x ≤ Real.exp ((e : ℝ) / x) := by
        have := Real.add_one_le_exp ((e : ℝ) / x)
        linarith
      have h4 : (1 + (e : ℝ) / x) ^ e ≤ Real.exp ((e : ℝ) / x) ^ e :=
        pow_le_pow_left₀ (by positivity) h3 _
      rw [← Real.exp_nat_mul] at h4
      have h5 : (e : ℝ) * ((e : ℝ) / x) ≤ 1 := by
        rw [← mul_div_assoc, div_le_one hxpos]
        nlinarith [hx.e_sq]
      have h6 : Real.exp ((e : ℝ) * ((e : ℝ) / x)) ≤ Real.exp 1 := Real.exp_le_exp.mpr h5
      have h7 := Real.exp_one_lt_d9
      linarith
    nlinarith
  have hlead : leadSize M c e / (3 * x ^ e) ≤ |(binomMoment M c e : ℝ) * logDiff e x| := by
    rw [abs_mul]
    unfold leadSize
    have hab : (0 : ℝ) ≤ |(binomMoment M c e : ℝ)| := abs_nonneg _
    have h1 : ((e - 1).factorial : ℝ) / (3 * x ^ e) ≤ ((e - 1).factorial : ℝ) / (x + e) ^ e :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hthree
    calc |(binomMoment M c e : ℝ)| * ((e - 1).factorial : ℝ) / (3 * x ^ e)
        = |(binomMoment M c e : ℝ)| * (((e - 1).factorial : ℝ) / (3 * x ^ e)) := by ring
      _ ≤ |(binomMoment M c e : ℝ)| * |logDiff e x| :=
        mul_le_mul_of_nonneg_left (h1.trans hlow) hab
  have hleadup : |(binomMoment M c e : ℝ) * logDiff e x| ≤ leadSize M c e / x ^ e := by
    rw [abs_mul]
    unfold leadSize
    have hab : (0 : ℝ) ≤ |(binomMoment M c e : ℝ)| := abs_nonneg _
    calc |(binomMoment M c e : ℝ)| * |logDiff e x|
        ≤ |(binomMoment M c e : ℝ)| * (((e - 1).factorial : ℝ) / x ^ e) :=
          mul_le_mul_of_nonneg_left hup hab
      _ = _ := by ring
  have hF6 : ((e - 1).factorial : ℝ) / (6 * x ^ e) ≤ leadSize M c e / (6 * x ^ e) :=
    div_le_div_of_nonneg_right hF (by positivity)
  have htri1 := abs_sub_abs_le_abs_sub ((binomMoment M c e : ℝ) * logDiff e x) (wordLog M c x)
  rw [abs_sub_comm] at htri1
  have htri2 := abs_sub_abs_le_abs_sub (wordLog M c x) ((binomMoment M c e : ℝ) * logDiff e x)
  have e1 : leadSize M c e / (3 * x ^ e) = 2 * (leadSize M c e / (6 * x ^ e)) := by
    field_simp
    ring
  have e2 : 7 / 6 * leadSize M c e / x ^ e =
      leadSize M c e / x ^ e + leadSize M c e / (6 * x ^ e) := by
    field_simp
    ring
  constructor
  · linarith
  · rw [e2]
    linarith

/-- **The word varies slowly.** -/
theorem wordLog_step_le {M e : ℕ} {c : ℕ → ℤ} (h : LeadingMoment M c e) {x : ℝ}
    (hx : BaseConditions M e x) :
    |wordLog M c (x + 1) - wordLog M c x| ≤ (leadSize M c e * ((e : ℝ) + 1)) / x ^ (e + 1) := by
  classical
  have hxpos := hx.x_pos
  have heM : e ∈ range (M + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le h.e_le)
  have hdiff : wordLog M c (x + 1) - wordLog M c x =
      ∑ j ∈ range (M + 1), (binomMoment M c j : ℝ) * logDiff (j + 1) x := by
    rw [wordLog_eq, wordLog_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_sub, logDiff_step]
  rw [hdiff, ← Finset.add_sum_erase _ _ heM]
  refine (abs_add_le _ _).trans ?_
  have hxe : 0 < x ^ (e + 1) := by positivity
  have hlead : |(binomMoment M c e : ℝ) * logDiff (e + 1) x| ≤
      leadSize M c e * (e : ℝ) / x ^ (e + 1) := by
    rw [abs_mul]
    have hb := abs_fwdDiff_iter_log_le (j := e) hxpos
    have hfac : (e.factorial : ℝ) = ((e - 1).factorial : ℝ) * (e : ℝ) := by
      obtain ⟨i, rfl⟩ : ∃ i, e = i + 1 := ⟨e - 1, by have := h.one_le; omega⟩
      simp [Nat.factorial_succ]
      ring
    have hab : (0 : ℝ) ≤ |(binomMoment M c e : ℝ)| := abs_nonneg _
    calc |(binomMoment M c e : ℝ)| * |logDiff (e + 1) x|
        ≤ |(binomMoment M c e : ℝ)| * ((e.factorial : ℝ) / x ^ (e + 1)) :=
          mul_le_mul_of_nonneg_left hb hab
      _ = _ := by rw [hfac]; unfold leadSize; ring
  have hrest : |∑ j ∈ (range (M + 1)).erase e, (binomMoment M c j : ℝ) * logDiff (j + 1) x| ≤
      ((e - 1).factorial : ℝ) / (6 * x ^ e) / x := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    set m : ℝ := ((M + 1 : ℕ) : ℝ) with hm
    have hmpos : 0 < m := by rw [hm]; positivity
    set q : ℝ := m / x with hq
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q ≤ 1 / 2 := by
      rw [hq, div_le_iff₀ hxpos]
      linarith [hx.m]
    have hterm : ∀ j ∈ (range (M + 1)).erase e,
        |(binomMoment M c j : ℝ) * logDiff (j + 1) x| ≤ if e < j then q * q ^ j else 0 := by
      intro j hj
      have hj2 := Finset.mem_erase.mp hj
      split_ifs with hej
      · rw [abs_mul]
        have h1 : |(binomMoment M c j : ℝ)| ≤ ((M + 1).choose (j + 1) : ℝ) := by
          have := abs_binomMoment_le h.word j
          exact_mod_cast this
        have h2 := abs_fwdDiff_iter_log_le (j := j) hxpos
        have h3 := choose_mul_factorial_le (M + 1) j
        have hf : (j.factorial : ℝ) ≤ ((j + 1).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_le (by omega)
        have hc : (0 : ℝ) ≤ ((M + 1).choose (j + 1) : ℝ) := by positivity
        calc |(binomMoment M c j : ℝ)| * |logDiff (j + 1) x|
            ≤ ((M + 1).choose (j + 1) : ℝ) * ((j.factorial : ℝ) / x ^ (j + 1)) :=
              mul_le_mul h1 h2 (abs_nonneg _) hc
          _ = ((M + 1).choose (j + 1) : ℝ) * (j.factorial : ℝ) / x ^ (j + 1) := by ring
          _ ≤ m ^ (j + 1) / x ^ (j + 1) := by
              refine div_le_div_of_nonneg_right ?_ (by positivity)
              exact (mul_le_mul_of_nonneg_left hf hc).trans h3
          _ = q * q ^ j := by rw [hq, ← pow_succ', div_pow]
      · have hlt : j < e := by
          rcases Nat.lt_or_gt_of_ne hj2.1 with h' | h'
          · exact h'
          · exact absurd h' hej
        rw [h.low j hlt]
        simp
    have hsum := Finset.sum_le_sum hterm
    have hmono : ∑ j ∈ (range (M + 1)).erase e, (if e < j then q * q ^ j else 0) ≤
        ∑ j ∈ range (M + 1), (if e < j then q * q ^ j else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ => ?_
      split_ifs <;> positivity
    have hfil : ∑ j ∈ range (M + 1), (if e < j then q * q ^ j else 0) =
        q * ∑ j ∈ (range (M + 1)).filter (fun j => e < j), q ^ j := by
      rw [← Finset.sum_filter, Finset.mul_sum]
    have hgeo := sum_filter_gt_pow_le hq0 hq1 e M
    have hlarge : 12 * m ^ (e + 2) ≤ x * ((e - 1).factorial : ℝ) := hx.large
    have hxe' : 0 < x ^ e := by positivity
    have hfinal : q * (2 * q ^ (e + 1)) ≤ ((e - 1).factorial : ℝ) / (6 * x ^ e) / x := by
      have e1 : q * (2 * q ^ (e + 1)) = 12 * m ^ (e + 2) / (6 * x ^ e * x * x) := by
        rw [hq, div_pow, pow_succ x e]
        field_simp
        ring
      have e2 : ((e - 1).factorial : ℝ) / (6 * x ^ e) / x =
          x * ((e - 1).factorial : ℝ) / (6 * x ^ e * x * x) := by
        field_simp
      rw [e1, e2]
      exact div_le_div_of_nonneg_right hlarge (by positivity)
    calc _ ≤ _ := hsum
      _ ≤ _ := hmono
      _ = _ := hfil
      _ ≤ q * (2 * q ^ (e + 1)) := mul_le_mul_of_nonneg_left hgeo hq0
      _ ≤ _ := hfinal
  have hF : ((e - 1).factorial : ℝ) ≤ leadSize M c e := h.factorial_le_leadSize
  have hrest' : ((e - 1).factorial : ℝ) / (6 * x ^ e) / x ≤ leadSize M c e / x ^ (e + 1) := by
    rw [div_div, pow_succ x e]
    refine div_le_div₀ (by linarith [(by positivity : (0 : ℝ) ≤ ((e - 1).factorial : ℝ))]) hF
      (by positivity) ?_
    have hxe' : 0 < x ^ e := by positivity
    nlinarith [mul_pos hxe' hxpos]
  have e1 : (leadSize M c e * ((e : ℝ) + 1)) / x ^ (e + 1) =
      leadSize M c e * (e : ℝ) / x ^ (e + 1) + leadSize M c e / x ^ (e + 1) := by ring
  rw [e1]
  linarith

/-- A discrete intermediate value lemma: a sequence that loses at most a quarter per step cannot jump over `[¼, ½]`. -/
theorem exists_mem_of_slow {u : ℕ → ℝ} {x₂ : ℕ} :
    ∀ (d x₀ : ℕ), x₀ + d = x₂ → 1 / 4 ≤ u x₀ → u x₂ ≤ 1 / 2 →
      (∀ x, x₀ ≤ x → x < x₂ → 3 / 4 * u x ≤ u (x + 1)) →
      ∃ x, x₀ ≤ x ∧ x ≤ x₂ ∧ 1 / 4 ≤ u x ∧ u x ≤ 1 / 2 := by
  intro d
  induction d with
  | zero =>
    intro x₀ h h0 h2 _
    have hx : x₀ = x₂ := by simpa using h
    subst hx
    exact ⟨x₀, le_rfl, le_rfl, h0, h2⟩
  | succ d ih =>
    intro x₀ h h0 h2 hstep
    by_cases hle : u x₀ ≤ 1 / 2
    · exact ⟨x₀, le_rfl, by omega, h0, hle⟩
    · have h1 : 1 / 4 ≤ u (x₀ + 1) := by
        have := hstep x₀ le_rfl (by omega)
        push Not at hle
        linarith
      obtain ⟨x, hx1, hx2, hx3, hx4⟩ := ih (x₀ + 1) (by omega) h1 h2
        (fun x hx hx2 => hstep x (by omega) hx2)
      exact ⟨x, by omega, hx2, hx3, hx4⟩

theorem BaseConditions.mono {M e : ℕ} {x y : ℝ} (h : BaseConditions M e x) (hxy : x ≤ y) :
    BaseConditions M e y where
  large := h.large.trans (mul_le_mul_of_nonneg_right hxy (by positivity))
  e_sq := h.e_sq.trans hxy
  m := h.m.trans hxy
  step := h.step.trans hxy
  pos := h.pos.trans hxy

/-- **Non-alignment from one word.** See the module docstring. -/
theorem not_aligned_of_leadingMoment {M e : ℕ} {c : ℕ → ℤ} (h : LeadingMoment M c e) {t ε : ℝ}
    {x₀ x₂ : ℕ} (hb : BaseConditions M e (x₀ : ℝ)) (h12 : x₀ ≤ x₂)
    (ht0 : 3 * π * (x₀ : ℝ) ^ e ≤ |t| * ((e - 1).factorial : ℝ))
    (ht2 : |t| * ((M + 1 : ℕ) : ℝ) ^ (e + 1) ≤ (x₂ : ℝ) ^ e)
    (hε : ((M : ℝ) + 1) * ε < 1 / 4) :
    ∃ n, x₀ ≤ n ∧ n ≤ x₂ + M ∧ ∀ j : ℤ, ε < |t * Real.log n / (2 * π) - j| := by
  classical
  have hpi : 0 < π := Real.pi_pos
  have hpi3 : 3 < π := Real.pi_gt_three
  have hbase : ∀ x : ℕ, x₀ ≤ x → BaseConditions M e (x : ℝ) := fun x hx =>
    hb.mono (by exact_mod_cast hx)
  set u : ℕ → ℝ := fun x => |t| * |wordLog M c (x : ℝ)| / (2 * π) with hu
  have hx0pos : (0 : ℝ) < (x₀ : ℝ) := hb.x_pos
  have hu0 : 1 / 4 ≤ u x₀ := by
    have hs := (wordLog_size h hb).1
    have hF := h.factorial_le_leadSize
    have hxe : 0 < (x₀ : ℝ) ^ e := by positivity
    have h1 : ((e - 1).factorial : ℝ) / (6 * (x₀ : ℝ) ^ e) ≤ |wordLog M c (x₀ : ℝ)| :=
      (div_le_div_of_nonneg_right hF (by positivity)).trans hs
    rw [hu]
    simp only
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : |t| * ((e - 1).factorial : ℝ) ≤ |t| * (|wordLog M c (x₀ : ℝ)| * (6 * (x₀ : ℝ) ^ e)) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h3 : 3 * π * (x₀ : ℝ) ^ e ≤ |t| * |wordLog M c (x₀ : ℝ)| * (6 * (x₀ : ℝ) ^ e) := by
      calc _ ≤ _ := ht0
        _ ≤ _ := h2
        _ = _ := by ring
    have h4 : π / 2 * (x₀ : ℝ) ^ e ≤ |t| * |wordLog M c (x₀ : ℝ)| * (x₀ : ℝ) ^ e := by linarith
    have h5 := le_of_mul_le_mul_right h4 hxe
    linarith
  have hx2pos : (0 : ℝ) < (x₂ : ℝ) := lt_of_lt_of_le hx0pos (by exact_mod_cast h12)
  have hu2 : u x₂ ≤ 1 / 2 := by
    have hs := (wordLog_size h (hbase x₂ h12)).2
    have hL := h.leadSize_le
    have hxe : 0 < (x₂ : ℝ) ^ e := by positivity
    rw [hu]
    simp only
    rw [div_le_iff₀ (by positivity)]
    have h1 : |wordLog M c (x₂ : ℝ)| ≤ 7 / 6 * (((M + 1 : ℕ) : ℝ) ^ (e + 1)) / (x₂ : ℝ) ^ e :=
      hs.trans (div_le_div_of_nonneg_right (by linarith) hxe.le)
    have h2 : |t| * |wordLog M c (x₂ : ℝ)| ≤ 7 / 6 := by
      calc |t| * |wordLog M c (x₂ : ℝ)|
          ≤ |t| * (7 / 6 * (((M + 1 : ℕ) : ℝ) ^ (e + 1)) / (x₂ : ℝ) ^ e) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = 7 / 6 * ((|t| * ((M + 1 : ℕ) : ℝ) ^ (e + 1)) / (x₂ : ℝ) ^ e) := by ring
        _ ≤ 7 / 6 * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            rw [div_le_one hxe]
            exact ht2
        _ = 7 / 6 := by ring
    linarith
  have hstep : ∀ x, x₀ ≤ x → x < x₂ → 3 / 4 * u x ≤ u (x + 1) := by
    intro x hx _
    have hbx := hbase x hx
    have hxpos := hbx.x_pos
    have hs := wordLog_step_le h hbx
    have hlow := (wordLog_size h hbx).1
    have hxe : 0 < (x : ℝ) ^ e := by positivity
    have hquarter : leadSize M c e * ((e : ℝ) + 1) / (x : ℝ) ^ (e + 1) ≤
        1 / 4 * (leadSize M c e / (6 * (x : ℝ) ^ e)) := by
      have hL : 0 ≤ leadSize M c e := by unfold leadSize; positivity
      rw [pow_succ, div_le_iff₀ (by positivity)]
      have hmain : 24 * ((e : ℝ) + 1) ≤ (x : ℝ) := hbx.step
      have e1 : 1 / 4 * (leadSize M c e / (6 * (x : ℝ) ^ e)) * ((x : ℝ) ^ e * (x : ℝ)) =
          leadSize M c e * (x : ℝ) / 24 := by
        field_simp
        ring
      rw [e1]
      nlinarith
    have hF : |wordLog M c (x : ℝ)| - |wordLog M c ((x : ℝ) + 1)| ≤
        |wordLog M c ((x : ℝ) + 1) - wordLog M c (x : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (wordLog M c (x : ℝ)) (wordLog M c ((x : ℝ) + 1))
      rwa [abs_sub_comm] at this
    have hkey : 3 / 4 * |wordLog M c (x : ℝ)| ≤ |wordLog M c ((x : ℝ) + 1)| := by
      have h1 : |wordLog M c ((x : ℝ) + 1) - wordLog M c (x : ℝ)| ≤
          1 / 4 * |wordLog M c (x : ℝ)| :=
        hs.trans (hquarter.trans (mul_le_mul_of_nonneg_left hlow (by norm_num)))
      linarith
    rw [hu]
    simp only
    push_cast
    rw [mul_div_assoc', le_div_iff₀ (by positivity), div_mul_cancel₀ _ (by positivity)]
    calc 3 / 4 * (|t| * |wordLog M c (x : ℝ)|) = |t| * (3 / 4 * |wordLog M c (x : ℝ)|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h12
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ := exists_mem_of_slow d x₀ hd.symm hu0 hu2 hstep
  by_contra hcon
  push Not at hcon
  have hal : ∀ a ∈ range (M + 1), ∃ j : ℤ,
      |t * Real.log ((x : ℝ) + a) / (2 * π) - j| ≤ ε := by
    intro a ha
    have haM := Finset.mem_range.mp ha
    obtain ⟨j, hj⟩ := hcon (x + a) (by omega) (by omega)
    refine ⟨j, ?_⟩
    have e1 : ((x + a : ℕ) : ℝ) = (x : ℝ) + a := by push_cast; ring
    rwa [e1] at hj
  have hε0 : 0 ≤ ε := by
    obtain ⟨j, hj⟩ := hal 0 (by simp)
    exact (abs_nonneg _).trans hj
  choose! J hJ using hal
  set v : ℝ := t * wordLog M c (x : ℝ) / (2 * π) with hv
  set W : ℤ := ∑ a ∈ range (M + 1), c a * J a with hW
  have hvu : |v| = u x := by
    rw [hv, hu]
    simp only
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hvW : |v - W| ≤ ((M : ℝ) + 1) * ε := by
    have e1 : v - W = ∑ a ∈ range (M + 1),
        (c a : ℝ) * (t * Real.log ((x : ℝ) + a) / (2 * π) - J a) := by
      rw [hv, hW]
      unfold wordLog
      push_cast
      rw [Finset.mul_sum, Finset.sum_div]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [e1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ a ∈ range (M + 1),
        |(c a : ℝ) * (t * Real.log ((x : ℝ) + a) / (2 * π) - J a)| ≤ ε := by
      intro a ha
      rw [abs_mul]
      have hc1 : |(c a : ℝ)| ≤ 1 := by exact_mod_cast h.word.bound a
      calc _ ≤ 1 * ε := mul_le_mul hc1 (hJ a ha) (abs_nonneg _) zero_le_one
        _ = ε := one_mul _
    have := Finset.sum_le_card_nsmul _ _ ε hterm
    rw [Finset.card_range, nsmul_eq_mul] at this
    push_cast at this
    exact this
  rw [← hvu] at hx3 hx4
  have hsmall : |v - W| < 1 / 4 := lt_of_le_of_lt hvW hε
  by_cases hW0 : W = 0
  · rw [hW0] at hsmall
    simp at hsmall
    linarith
  · have hW1 : (1 : ℝ) ≤ |(W : ℝ)| := by
      have : (1 : ℤ) ≤ |W| := Int.one_le_abs hW0
      exact_mod_cast this
    have htri := abs_sub_abs_le_abs_sub (W : ℝ) v
    rw [abs_sub_comm] at htri
    linarith

/-- **Non-alignment at every height in a range.** See the module docstring. -/
theorem exists_not_aligned {M k E x₀ x₂ : ℕ} {t ε : ℝ}
    (hword : ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ (M + 1))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hSE : ∀ p ∈ S, p ≤ E)
    (hSM : ∀ p ∈ S, M + 1 + p < p * p) (hsum : M < ∑ p ∈ S, (p - 1))
    (hx₀ : x₀ = 12 * (M + 1) ^ (E + 2) + E ^ 2 + 24 * (E + 1) + 2 * (M + 1) + 1)
    (ht0 : 3 * π * (x₀ : ℝ) ^ E ≤ |t|) (h12 : x₀ ≤ x₂)
    (ht2 : |t| * ((M + 1 : ℕ) : ℝ) ^ (k + 2) ≤ (x₂ : ℝ) ^ (k + 1))
    (hε : ((M : ℝ) + 1) * ε < 1 / 4) :
    ∃ n, x₀ ≤ n ∧ n ≤ x₂ + M ∧ ∀ j : ℤ, ε < |t * Real.log n / (2 * π) - j| := by
  classical
  obtain ⟨c, hc, hlow⟩ := exists_word hword
  have hex := exists_binomMoment_ne_zero hc
  set e := Nat.find hex with he
  have hne : binomMoment M c e ≠ 0 := Nat.find_spec hex
  have hbelow : ∀ j < e, binomMoment M c j = 0 := fun j hj => by
    have := Nat.find_min hex hj
    exact not_not.mp this
  have hke : k < e := by
    by_contra hcon
    exact hne (hlow e (by omega))
  have heE : e ≤ E := by
    by_contra hcon
    have := sum_primes_le_of_moments_vanish hc (e := E)
      (fun j hj => hbelow j (by omega)) S hS hSE hSM
    omega
  have hL : LeadingMoment M c e := ⟨hc, by omega, hbelow, hne⟩
  have hfac : (1 : ℝ) ≤ ((e - 1).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm1 : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  have hx₀R : (x₀ : ℝ) = 12 * ((M + 1 : ℕ) : ℝ) ^ (E + 2) + (E : ℝ) ^ 2 + 24 * ((E : ℝ) + 1) +
      2 * ((M + 1 : ℕ) : ℝ) + 1 := by
    rw [hx₀]; push_cast; ring
  have heE' : (e : ℝ) ≤ E := by exact_mod_cast heE
  have he0 : (0 : ℝ) ≤ e := by positivity
  have hpw : ((M + 1 : ℕ) : ℝ) ^ (e + 2) ≤ ((M + 1 : ℕ) : ℝ) ^ (E + 2) :=
    pow_le_pow_right₀ hm1 (by omega)
  have hEsq : (e : ℝ) ^ 2 ≤ (E : ℝ) ^ 2 := pow_le_pow_left₀ he0 heE' 2
  have hEnn : (0 : ℝ) ≤ E := by positivity
  have hmp : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) ^ (E + 2) := by positivity
  have hmnn : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by positivity
  have hEsqnn : (0 : ℝ) ≤ (E : ℝ) ^ 2 := by positivity
  have hx₀1 : (1 : ℝ) ≤ (x₀ : ℝ) := by
    rw [hx₀R]
    linarith
  have hb : BaseConditions M e (x₀ : ℝ) := by
    refine ⟨?_, ?_, ?_, ?_, hx₀1⟩
    · have h1 : 12 * ((M + 1 : ℕ) : ℝ) ^ (e + 2) ≤ (x₀ : ℝ) := by
        rw [hx₀R]
        linarith
      exact h1.trans (le_mul_of_one_le_right (by linarith) hfac)
    · rw [hx₀R]
      linarith
    · rw [hx₀R]
      linarith
    · rw [hx₀R]
      linarith
  have ht0' : 3 * π * (x₀ : ℝ) ^ e ≤ |t| * ((e - 1).factorial : ℝ) := by
    have h1 : (x₀ : ℝ) ^ e ≤ (x₀ : ℝ) ^ E := pow_le_pow_right₀ hx₀1 heE
    have hpi : 0 < π := Real.pi_pos
    calc 3 * π * (x₀ : ℝ) ^ e ≤ 3 * π * (x₀ : ℝ) ^ E :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ |t| := ht0
      _ ≤ |t| * ((e - 1).factorial : ℝ) := le_mul_of_one_le_right (abs_nonneg _) hfac
  have hmx₂ : ((M + 1 : ℕ) : ℝ) ≤ (x₂ : ℝ) := by
    have h1 : (x₀ : ℝ) ≤ (x₂ : ℝ) := by exact_mod_cast h12
    have h2 : ((M + 1 : ℕ) : ℝ) ≤ (x₀ : ℝ) := by
      rw [hx₀R]
      linarith
    exact h2.trans h1
  have ht2' : |t| * ((M + 1 : ℕ) : ℝ) ^ (e + 1) ≤ (x₂ : ℝ) ^ e := by
    obtain ⟨d, hd⟩ : ∃ d, e = k + 1 + d := ⟨e - (k + 1), by omega⟩
    have h1 : ((M + 1 : ℕ) : ℝ) ^ (e + 1) = ((M + 1 : ℕ) : ℝ) ^ (k + 2) * ((M + 1 : ℕ) : ℝ) ^ d := by
      rw [hd, ← pow_add]
      congr 1
      omega
    have h2 : (x₂ : ℝ) ^ e = (x₂ : ℝ) ^ (k + 1) * (x₂ : ℝ) ^ d := by
      rw [hd, pow_add]
    rw [h1, h2, ← mul_assoc]
    exact mul_le_mul ht2 (pow_le_pow_left₀ hmnn hmx₂ d) (by positivity) (by positivity)
  exact not_aligned_of_leadingMoment hL hb h12 ht0' ht2' hε

/-! ### From integers to primes -/

/-- Alignment of the primes up to `N` to within `ε` aligns each `n ≤ N` to within `(log₂ n) ε`. -/
theorem aligned_of_primes {t ε : ℝ} (hε : 0 ≤ ε) {N : ℕ}
    (h : ∀ p, p.Prime → p ≤ N → ∃ j : ℤ, |t * Real.log p / (2 * π) - j| ≤ ε) :
    ∀ n, 1 ≤ n → n ≤ N → ∃ j : ℤ, |t * Real.log n / (2 * π) - j| ≤ (Nat.log 2 n : ℝ) * ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnN
    by_cases h1 : n = 1
    · subst h1
      exact ⟨0, by simp⟩
    · have hp := Nat.minFac_prime h1
      set p := n.minFac with hpdef
      obtain ⟨q, hq⟩ := Nat.minFac_dvd n
      have hqpos : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0, mul_zero] at hq
          omega
        · exact h0
      have hp2 := hp.two_le
      have hqlt : q < n := by
        rw [hq]
        nlinarith
      obtain ⟨j₁, hj₁⟩ := h p hp (le_trans (Nat.minFac_le hn) hnN)
      obtain ⟨j₂, hj₂⟩ := ih q hqlt hqpos (by omega)
      refine ⟨j₁ + j₂, ?_⟩
      have hlog : Real.log n = Real.log p + Real.log q := by
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hqR : (q : ℝ) ≠ 0 := by positivity
        rw [hq]
        push_cast
        exact Real.log_mul hpR hqR
      have e1 : t * Real.log n / (2 * π) - ((j₁ + j₂ : ℤ) : ℝ) =
          (t * Real.log p / (2 * π) - j₁) + (t * Real.log q / (2 * π) - j₂) := by
        rw [hlog]
        push_cast
        ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      have hlogle : Nat.log 2 q + 1 ≤ Nat.log 2 n := by
        rw [← Nat.log_mul_base (by norm_num : 1 < 2) (by omega : q ≠ 0)]
        refine Nat.log_mono_right ?_
        calc q * 2 = 2 * q := mul_comm _ _
          _ ≤ p * q := Nat.mul_le_mul_right q hp2
          _ = n := hq.symm
      have hlogle' : (Nat.log 2 q : ℝ) + 1 ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast hlogle
      nlinarith

/-- **Non-alignment for primes.** The same range of heights, with precision reduced by `log₂` of the length. -/
theorem exists_prime_not_aligned {M k E x₀ x₂ : ℕ} {t ε : ℝ}
    (hword : ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ (M + 1))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hSE : ∀ p ∈ S, p ≤ E)
    (hSM : ∀ p ∈ S, M + 1 + p < p * p) (hsum : M < ∑ p ∈ S, (p - 1))
    (hx₀ : x₀ = 12 * (M + 1) ^ (E + 2) + E ^ 2 + 24 * (E + 1) + 2 * (M + 1) + 1)
    (ht0 : 3 * π * (x₀ : ℝ) ^ E ≤ |t|) (h12 : x₀ ≤ x₂)
    (ht2 : |t| * ((M + 1 : ℕ) : ℝ) ^ (k + 2) ≤ (x₂ : ℝ) ^ (k + 1))
    (hε : ((M : ℝ) + 1) * ((Nat.log 2 (x₂ + M) : ℝ) * ε) < 1 / 4) :
    ∃ p, p.Prime ∧ p ≤ x₂ + M ∧ ∀ j : ℤ, ε < |t * Real.log p / (2 * π) - j| := by
  by_contra hcon
  push Not at hcon
  have hal : ∀ p, p.Prime → p ≤ x₂ + M → ∃ j : ℤ, |t * Real.log p / (2 * π) - j| ≤ ε := by
    intro p hp hpN
    exact hcon p hp hpN
  have hx₀2 : 2 ≤ x₀ := by
    rw [hx₀]
    have : 1 ≤ M + 1 := by omega
    omega
  have hε0 : 0 ≤ ε := by
    obtain ⟨j, hj⟩ := hal 2 Nat.prime_two (by omega)
    exact (abs_nonneg _).trans hj
  obtain ⟨n, hn1, hn2, hn3⟩ := exists_not_aligned hword S hS hSE hSM hsum hx₀ ht0 h12 ht2 hε
  obtain ⟨j, hj⟩ := aligned_of_primes hε0 hal n (by omega) hn2
  have hlog : (Nat.log 2 n : ℝ) ≤ (Nat.log 2 (x₂ + M) : ℝ) := by
    exact_mod_cast Nat.log_mono_right hn2
  have := hn3 j
  nlinarith [hlog, hε0]

end

end GaloisForLFunctions.PrimeTorusTheory
