import GaloisForLFunctions.ArithmeticResonanceTheory.IntegralityForbidsSuperConformalDistortion

/-!
# The Mills boundary

Can primes follow `C aⁿ + O(1)`? For integers `p n` this is the same as bounded **conformal
defects** `m n = p (n + 1) − a · p n` (`abs_defect_le`). A **defect chain** (`IsDefectChain`) is
such a sequence of increasing primes.

**Necessary conditions.** A defect is never `0` (`IsDefectChain.defect_ne_zero`) and is prime to
`a` (`IsDefectChain.not_dvd_defect`); for odd `a` it is even (`IsDefectChain.two_dvd_defect`).
It is not eventually periodic (`not_eventually_periodic_defect`).

**Congruence forcing.** Modulo a fixed `L`, the residues of a chain follow
`x ↦ a x + m` and must avoid `0`.
* If the defect is a function of the residue, the residues follow a self-map of `ZMod L`, become
  eventually periodic, and so do the defects (`IsDefectChain.false_of_determined`).
* For `3 ∤ a` and two defect values in different nonzero classes mod `3`, exactly one value keeps
  the next member prime to `3`: the defect is forced (`IsDefectChain.false_of_two_classes_mod_three`).
* If `a ≡ 1 (mod ℓ)` and every defect is either a fixed `d₀ ≡ 0` or `≡ r ≢ 0`, the residue walks
  `x ↦ x + r` on the `r`-steps; it would pass through `0` after at most `ℓ − 1` of them, so the
  defect is eventually `d₀` (`IsDefectChain.false_of_unipotent`).

**Decided cases.** No chain has defects `|m| ≤ 2` when `a` is even and `3 ∤ a`
(`not_isDefectChain_of_even`), `|m| ≤ 3` when `a` is odd and `3 ∤ a` (`not_isDefectChain_of_odd`),
or `|m| ≤ 1` when `a` is odd (`not_isDefectChain_of_odd_of_abs_le_one`). For every real `C`, the
integer parts `⌊C aⁿ⌋` are not eventually prime for `a = 2, …, 6` (`not_eventually_prime_floor`),
and no primes stay within `1/2` of `C aⁿ` for `a = 2, 4, 5` (`not_eventually_prime_near`).
-/

open Filter Topology

namespace GaloisForLFunctions.ArithmeticResonanceTheory

/-! ## Bounded defects -/

/-- An error `|p n − C aⁿ| ≤ B` at two consecutive indices bounds the defect by `(a + 1) B`. -/
theorem abs_defect_le {p : ℕ → ℕ} {a : ℕ} {C B : ℝ} {n : ℕ}
    (h0 : |(p n : ℝ) - C * (a : ℝ) ^ n| ≤ B) (h1 : |(p (n + 1) : ℝ) - C * (a : ℝ) ^ (n + 1)| ≤ B) :
    |(((p (n + 1) : ℤ) - a * p n : ℤ) : ℝ)| ≤ (a + 1) * B := by
  push_cast
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hrw : (p (n + 1) : ℝ) - a * p n =
      ((p (n + 1) : ℝ) - C * (a : ℝ) ^ (n + 1)) - a * ((p n : ℝ) - C * (a : ℝ) ^ n) := by ring
  rw [hrw]
  calc |((p (n + 1) : ℝ) - C * (a : ℝ) ^ (n + 1)) - a * ((p n : ℝ) - C * (a : ℝ) ^ n)|
      ≤ |(p (n + 1) : ℝ) - C * (a : ℝ) ^ (n + 1)| + |a * ((p n : ℝ) - C * (a : ℝ) ^ n)| :=
        abs_sub _ _
    _ ≤ B + a * B := by
        rw [abs_mul, abs_of_nonneg ha]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h0 ha)
    _ = (a + 1) * B := by ring

/-- A **defect chain**: from the index `N` on, `p n` is prime, increases, and
`p (n + 1) = a · p n + m n`. -/
structure IsDefectChain (p : ℕ → ℕ) (a : ℕ) (m : ℕ → ℤ) (N : ℕ) : Prop where
  prime : ∀ n, N ≤ n → (p n).Prime
  mono : ∀ n, N ≤ n → p n < p (n + 1)
  step : ∀ n, N ≤ n → (p (n + 1) : ℤ) = a * p n + m n

namespace IsDefectChain

variable {p : ℕ → ℕ} {a : ℕ} {m : ℕ → ℤ} {N : ℕ}

theorem mono_from (hc : IsDefectChain p a m N) {N' : ℕ} (h : N ≤ N') : IsDefectChain p a m N' :=
  ⟨fun n hn => hc.prime n (h.trans hn), fun n hn => hc.mono n (h.trans hn),
    fun n hn => hc.step n (h.trans hn)⟩

theorem add_le (hc : IsDefectChain p a m N) (j : ℕ) : p N + j ≤ p (N + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := hc.mono (N + j) (Nat.le_add_right _ _)
    rw [show N + (j + 1) = N + j + 1 by omega]; omega

/-- Far out, the members exceed any bound. -/
theorem lt_of_le (hc : IsDefectChain p a m N) (K : ℕ) {n : ℕ} (hn : N + K ≤ n) : K < p n := by
  have h1 := hc.add_le (n - N)
  have h2 := (hc.prime N le_rfl).two_le
  rw [show N + (n - N) = n by omega] at h1
  omega

/-- A defect is never `0`: `a · p n` is not prime. -/
theorem defect_ne_zero (hc : IsDefectChain p a m N) (ha : 2 ≤ a) {n : ℕ} (hn : N ≤ n) :
    m n ≠ 0 := by
  intro h0
  have h := hc.step n hn
  rw [h0, add_zero] at h
  have : p (n + 1) = a * p n := by exact_mod_cast h
  exact not_prime_mul_of_prime ha (hc.prime n hn) (this ▸ hc.prime (n + 1) (by omega))

/-- A prime dividing `a` does not divide the defect, unless it is the next member. -/
theorem not_dvd_defect (hc : IsDefectChain p a m N) {q : ℕ} (hq : q.Prime) (hqa : q ∣ a)
    {n : ℕ} (hn : N ≤ n) (hne : p (n + 1) ≠ q) : ¬ (q : ℤ) ∣ m n := by
  intro hqm
  have h1 : (q : ℤ) ∣ (p (n + 1) : ℤ) := by
    rw [hc.step n hn]
    exact dvd_add (dvd_mul_of_dvd_left (by exact_mod_cast hqa) _) hqm
  have h2 : q ∣ p (n + 1) := by exact_mod_cast h1
  rcases (Nat.dvd_prime (hc.prime (n + 1) (by omega))).mp h2 with h | h
  · exact hq.one_lt.ne' h
  · exact hne h.symm

/-- For odd `a` the defects are even (both members odd). -/
theorem two_dvd_defect (hc : IsDefectChain p a m N) (ha : ¬ 2 ∣ a) {n : ℕ} (hn : N ≤ n)
    (h0 : p n ≠ 2) (h1 : p (n + 1) ≠ 2) : (2 : ℤ) ∣ m n := by
  have ho0 : Odd (p n) := (hc.prime n hn).odd_of_ne_two h0
  have ho1 : Odd (p (n + 1)) := (hc.prime (n + 1) (by omega)).odd_of_ne_two h1
  have hoa : Odd a := Nat.odd_iff.mpr (by omega)
  have hprod : Odd ((a : ℤ) * p n) := by exact_mod_cast hoa.mul ho0
  have hm : m n = (p (n + 1) : ℤ) - a * p n := by rw [hc.step n hn]; ring
  rw [hm, ← even_iff_two_dvd]
  exact (by exact_mod_cast ho1 : Odd ((p (n + 1) : ℕ) : ℤ)).sub_odd hprod

/-! ## Congruence forcing -/

/-- **Determined defects.** If from some index on the defect is a function of the residue of the
member modulo a fixed `L`, the chain is impossible. -/
theorem false_of_determined (hc : IsDefectChain p a m N) (ha : 1 ≤ a) {L : ℕ} [NeZero L]
    (g : ZMod L → ℤ) (hg : ∀ n, N ≤ n → m n = g (p n)) : False := by
  -- the residues follow a self-map of the finite set `ZMod L`
  let F : ZMod L → ZMod L := fun y => (a : ZMod L) * y + (g y : ZMod L)
  let x : ℕ → ZMod L := fun n => (p (N + n) : ZMod L)
  have hstep : ∀ n, x (n + 1) = F (x n) := by
    intro n
    have h := congrArg (fun z : ℤ => (z : ZMod L)) (hc.step (N + n) (Nat.le_add_right _ _))
    push_cast at h
    show (p (N + (n + 1)) : ZMod L) = (a : ZMod L) * (p (N + n) : ZMod L) + (g (p (N + n)) : ZMod L)
    rw [← Nat.add_assoc, h, hg (N + n) (Nat.le_add_right _ _)]
  -- two equal residues
  obtain ⟨i₀, j₀, hij₀, hx₀⟩ := Finite.exists_ne_map_eq_of_infinite x
  obtain ⟨i, j, hij, hx⟩ : ∃ i j, i < j ∧ x i = x j := by
    rcases lt_or_gt_of_ne hij₀ with h | h
    · exact ⟨i₀, j₀, h, hx₀⟩
    · exact ⟨j₀, i₀, h, hx₀.symm⟩
  have hshift : ∀ t, x (i + t) = x (j + t) := by
    intro t
    induction t with
    | zero => simpa using hx
    | succ t ih => rw [← Nat.add_assoc, ← Nat.add_assoc, hstep, hstep, ih]
  -- so the defects are periodic from `N + i` on, with period `j − i`
  refine not_eventually_periodic_defect ha m (d := j - i) (N := N + i) (by omega)
    (fun n hn => hc.prime n (by omega)) (fun n hn => hc.mono n (by omega))
    (fun n hn => hc.step n (by omega)) (fun n hn => ?_)
  obtain ⟨t, rfl⟩ : ∃ t, n = N + i + t := ⟨n - (N + i), by omega⟩
  rw [hg (N + i + t + (j - i)) (by omega), hg (N + i + t) (by omega)]
  have h1 : (p (N + i + t + (j - i)) : ZMod L) = x (j + t) := by
    show (p (N + i + t + (j - i)) : ZMod L) = (p (N + (j + t)) : ZMod L)
    rw [show N + i + t + (j - i) = N + (j + t) by omega]
  have h2 : (p (N + i + t) : ZMod L) = x (i + t) := by
    show (p (N + i + t) : ZMod L) = (p (N + (i + t)) : ZMod L)
    rw [Nat.add_assoc]
  rw [h1, h2, hshift]

theorem natCast_ne_zero_of_prime_lt {ℓ q : ℕ} (hℓ : ℓ.Prime) (hq : q.Prime) (hlt : ℓ < q) :
    (q : ZMod ℓ) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  rcases (Nat.dvd_prime hq).mp hdvd with h | h
  · exact hℓ.one_lt.ne' h
  · omega

/-- Two distinct nonzero classes mod `3`: the class of `y + d₂ ≠ 0` forces `y + d₁ = 0`. -/
theorem zmod_three_force (y d₁ d₂ : ZMod 3) (hy : y ≠ 0) (h1 : d₁ ≠ 0) (h2 : d₂ ≠ 0)
    (h12 : d₁ ≠ d₂) (hy2 : y + d₂ ≠ 0) : y + d₁ = 0 := by
  revert y d₁ d₂; decide

/-- **Forcing mod `3`.** If `3 ∤ a` and every defect takes one of two values in different nonzero
classes mod `3`, the chain is impossible. -/
theorem false_of_two_classes_mod_three (hc : IsDefectChain p a m N) (ha : 1 ≤ a) (ha3 : ¬ 3 ∣ a)
    {d₁ d₂ : ℤ} (h1 : (d₁ : ZMod 3) ≠ 0) (h2 : (d₂ : ZMod 3) ≠ 0) (h12 : (d₁ : ZMod 3) ≠ d₂)
    (hm : ∀ n, N ≤ n → m n = d₁ ∨ m n = d₂) : False := by
  have ha3' : (a : ZMod 3) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact ha3
  refine (hc.mono_from (N' := N + 3) (by omega)).false_of_determined ha (L := 3)
    (fun y => if (a : ZMod 3) * y + (d₁ : ZMod 3) = 0 then d₂ else d₁) (fun n hn => ?_)
  have hp : (p n : ZMod 3) ≠ 0 :=
    natCast_ne_zero_of_prime_lt Nat.prime_three (hc.prime n (by omega)) (hc.lt_of_le 3 hn)
  have hq : (p (n + 1) : ZMod 3) ≠ 0 :=
    natCast_ne_zero_of_prime_lt Nat.prime_three (hc.prime (n + 1) (by omega))
      (hc.lt_of_le 3 (by omega))
  have hrec : (p (n + 1) : ZMod 3) = (a : ZMod 3) * (p n : ZMod 3) + (m n : ZMod 3) := by
    have h := congrArg (fun z : ℤ => (z : ZMod 3)) (hc.step n (by omega))
    push_cast at h
    exact h
  have hy : (a : ZMod 3) * (p n : ZMod 3) ≠ 0 := mul_ne_zero ha3' hp
  show m n = if (a : ZMod 3) * (p n : ZMod 3) + (d₁ : ZMod 3) = 0 then d₂ else d₁
  rcases hm n (by omega) with h | h
  · rw [if_neg, h]
    rw [← h, ← hrec]; exact hq
  · rw [if_pos, h]
    refine zmod_three_force _ _ _ hy h1 h2 h12 ?_
    rw [← h, ← hrec]; exact hq

/-- In a nat sequence starting at `0` with steps `0` or `1`, every value below an attained bound is
attained. -/
theorem exists_eq_of_le_succ {c : ℕ → ℕ} (h0 : c 0 = 0) (hstep : ∀ n, c (n + 1) ≤ c n + 1)
    {t : ℕ} (ht : ∃ n, t ≤ c n) : ∃ n, c n = t := by
  classical
  let n₀ := Nat.find ht
  have hn₀ : t ≤ c n₀ := Nat.find_spec ht
  rcases Nat.eq_zero_or_pos n₀ with h | h
  · refine ⟨0, ?_⟩
    rw [h, h0] at hn₀
    omega
  · have hprev : ¬ t ≤ c (n₀ - 1) := Nat.find_min ht (by omega)
    have := hstep (n₀ - 1)
    rw [show n₀ - 1 + 1 = n₀ by omega] at this
    exact ⟨n₀, by omega⟩

/-- **Forcing by a unipotent residue walk.** If `a ≡ 1 (mod ℓ)` and every defect is either a fixed
`d₀ ≡ 0` or congruent to a fixed `r ≢ 0`, the chain is impossible: the residues move by `r` on each
`r`-step and would reach `0`, so the defect is eventually `d₀`. -/
theorem false_of_unipotent (hc : IsDefectChain p a m N) (ha : 1 ≤ a) {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (haℓ : (a : ZMod ℓ) = 1) {r : ZMod ℓ} (hr : r ≠ 0) {d₀ : ℤ} (hd₀ : (d₀ : ZMod ℓ) = 0)
    (hm : ∀ n, N ≤ n → m n = d₀ ∨ (m n : ZMod ℓ) = r) : False := by
  classical
  set N' := N + ℓ with hN'
  have hnz : ∀ n, N' ≤ n → (p n : ZMod ℓ) ≠ 0 := fun n hn =>
    natCast_ne_zero_of_prime_lt hℓ.out (hc.prime n (by omega)) (hc.lt_of_le ℓ hn)
  -- the number of `r`-steps
  let c : ℕ → ℕ := fun n => ∑ j ∈ Finset.range n, if m (N' + j) = d₀ then 0 else 1
  have hc0 : c 0 = 0 := by simp [c]
  have hcs : ∀ n, c (n + 1) = c n + if m (N' + n) = d₀ then 0 else 1 := fun n =>
    Finset.sum_range_succ _ n
  have hx : ∀ n, (p (N' + n) : ZMod ℓ) = (p N' : ZMod ℓ) + (c n : ZMod ℓ) * r := by
    intro n
    induction n with
    | zero => simp [hc0]
    | succ n ih =>
      have h := congrArg (fun z : ℤ => (z : ZMod ℓ)) (hc.step (N' + n) (by omega))
      push_cast at h
      rw [← Nat.add_assoc, h, haℓ, one_mul, ih, hcs]
      by_cases hmd : m (N' + n) = d₀
      · rw [if_pos hmd, hmd, hd₀]; simp
      · rw [if_neg hmd, ((hm (N' + n) (by omega)).resolve_left hmd)]
        push_cast; ring
  by_cases hev : ∃ n₀, ∀ n, n₀ ≤ n → m (N' + n) = d₀
  · -- the defect is eventually the constant `d₀`
    obtain ⟨n₀, hn₀⟩ := hev
    refine not_eventually_affine_recurrence ha d₀ (N := N' + n₀)
      (fun n hn => hc.prime n (by omega)) (fun n hn => hc.mono n (by omega)) (fun n hn => ?_)
    have h := hn₀ (n - N') (by omega)
    rw [show N' + (n - N') = n by omega] at h
    rw [hc.step n (by omega), h]
  · -- otherwise the count of `r`-steps passes through the value that reaches `0`
    push Not at hev
    have hmono : Monotone c := monotone_nat_of_le_succ fun n => by rw [hcs]; split_ifs <;> omega
    have hunb : ∀ k, ∃ n, k ≤ c n := by
      intro k
      induction k with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ k ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨n', hn', hne⟩ := hev n
        refine ⟨n' + 1, ?_⟩
        rw [hcs, if_neg hne]
        have := hmono hn'
        omega
    set t := ((-(p N' : ZMod ℓ)) * r⁻¹).val with ht
    obtain ⟨n, hn⟩ := exists_eq_of_le_succ hc0 (fun n => by rw [hcs]; split_ifs <;> omega)
      (hunb t)
    refine hnz (N' + n) (Nat.le_add_right _ _) ?_
    rw [hx, hn, ht, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hr, mul_one,
      add_neg_cancel]

end IsDefectChain

open IsDefectChain

/-! ## Decided cases -/

variable {p : ℕ → ℕ} {a : ℕ} {m : ℕ → ℤ} {N : ℕ}

/-- **Even base, small defects.** For even `a` with `3 ∤ a`, no chain has `|m n| ≤ 2`: the defects
are odd and nonzero, hence `±1`, and forced mod `3`. -/
theorem not_isDefectChain_of_even (ha : 2 ≤ a) (ha2 : 2 ∣ a) (ha3 : ¬ 3 ∣ a)
    (hm : ∀ n, N ≤ n → |m n| ≤ 2) : ¬ IsDefectChain p a m N := by
  intro hc
  refine (hc.mono_from (N' := N + 3) (by omega)).false_of_two_classes_mod_three (by omega) ha3
    (d₁ := 1) (d₂ := -1) (by push_cast; decide) (by push_cast; decide) (by push_cast; decide)
    (fun n hn => ?_)
  have hodd := hc.not_dvd_defect Nat.prime_two ha2 (n := n) (by omega)
    (hc.lt_of_le 2 (by omega)).ne'
  have hne := hc.defect_ne_zero ha (n := n) (by omega)
  have hb := abs_le.mp (hm n (by omega))
  push_cast at hodd
  omega

/-- **Odd base, small defects.** For odd `a` with `3 ∤ a`, no chain has `|m n| ≤ 3`: the defects
are even and nonzero, hence `±2`, and forced mod `3`. -/
theorem not_isDefectChain_of_odd (ha : 2 ≤ a) (ha2 : ¬ 2 ∣ a) (ha3 : ¬ 3 ∣ a)
    (hm : ∀ n, N ≤ n → |m n| ≤ 3) : ¬ IsDefectChain p a m N := by
  intro hc
  refine (hc.mono_from (N' := N + 3) (by omega)).false_of_two_classes_mod_three (by omega) ha3
    (d₁ := 2) (d₂ := -2) (by push_cast; decide) (by push_cast; decide) (by push_cast; decide)
    (fun n hn => ?_)
  have heven := hc.two_dvd_defect ha2 (n := n) (by omega) (hc.lt_of_le 2 (by omega)).ne'
    (hc.lt_of_le 2 (by omega)).ne'
  have hne := hc.defect_ne_zero ha (n := n) (by omega)
  have hb := abs_le.mp (hm n (by omega))
  omega

/-- **Odd base, unit defects.** For odd `a`, no chain has `|m n| ≤ 1`. -/
theorem not_isDefectChain_of_odd_of_abs_le_one (ha : 2 ≤ a) (ha2 : ¬ 2 ∣ a)
    (hm : ∀ n, N ≤ n → |m n| ≤ 1) : ¬ IsDefectChain p a m N := by
  intro hc
  have heven := hc.two_dvd_defect ha2 (n := N + 3) (by omega) (hc.lt_of_le 2 (by omega)).ne'
    (hc.lt_of_le 2 (by omega)).ne'
  have hne := hc.defect_ne_zero ha (n := N + 3) (by omega)
  have hb := abs_le.mp (hm (N + 3) (by omega))
  omega

/-- The defect of integer parts is a base-`a` digit: `a⌊y⌋ ≤ ⌊a y⌋ ≤ a⌊y⌋ + a − 1`. -/
theorem floor_mul_mem {a : ℕ} (ha : 1 ≤ a) (y : ℝ) :
    (a : ℤ) * ⌊y⌋ ≤ ⌊(a : ℝ) * y⌋ ∧ ⌊(a : ℝ) * y⌋ ≤ a * ⌊y⌋ + (a - 1) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  constructor
  · refine Int.le_floor.mpr ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (Int.floor_le y) ha0.le
  · have hlt : ⌊(a : ℝ) * y⌋ < a * ⌊y⌋ + a := by
      refine Int.floor_lt.mpr ?_
      push_cast
      have := Int.lt_floor_add_one y
      nlinarith
    omega

/-- **Integer parts of geometric sequences.** For every real `C` and `a ∈ {2, …, 6}`, the integer
parts `⌊C aⁿ⌋` are not prime for all large `n`. -/
theorem not_eventually_prime_floor (ha : a ∈ ({2, 3, 4, 5, 6} : Finset ℕ)) (C : ℝ) :
    ¬ ∀ᶠ n in atTop, ∃ q : ℕ, q.Prime ∧ (q : ℤ) = ⌊C * (a : ℝ) ^ n⌋ := by
  intro hev
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have ha2 : 2 ≤ a := by simp only [Finset.mem_insert, Finset.mem_singleton] at ha; omega
  -- the members and their digit defects
  let p : ℕ → ℕ := fun n => (⌊C * (a : ℝ) ^ n⌋).toNat
  let m : ℕ → ℤ := fun n => ⌊C * (a : ℝ) ^ (n + 1)⌋ - a * ⌊C * (a : ℝ) ^ n⌋
  have hp : ∀ n, N ≤ n → (p n : ℤ) = ⌊C * (a : ℝ) ^ n⌋ ∧ (p n).Prime := by
    intro n hn
    obtain ⟨q, hq, hqe⟩ := hN n hn
    have hnn : 0 ≤ ⌊C * (a : ℝ) ^ n⌋ := by rw [← hqe]; exact Nat.cast_nonneg q
    refine ⟨Int.toNat_of_nonneg hnn, ?_⟩
    have h1 : ((⌊C * (a : ℝ) ^ n⌋).toNat : ℤ) = q := by rw [Int.toNat_of_nonneg hnn, hqe]
    have h2 : (⌊C * (a : ℝ) ^ n⌋).toNat = q := by exact_mod_cast h1
    show (⌊C * (a : ℝ) ^ n⌋).toNat.Prime
    rw [h2]; exact hq
  have hdigit : ∀ n, 0 ≤ m n ∧ m n ≤ a - 1 := by
    intro n
    have h := floor_mul_mem (by omega : 1 ≤ a) (C * (a : ℝ) ^ n)
    rw [show (a : ℝ) * (C * (a : ℝ) ^ n) = C * (a : ℝ) ^ (n + 1) by ring] at h
    exact ⟨by simp only [m]; omega, by simp only [m]; omega⟩
  have hrec : ∀ n, N ≤ n → (p (n + 1) : ℤ) = a * p n + m n := by
    intro n hn
    rw [(hp (n + 1) (by omega)).1, (hp n hn).1]
    simp only [m]; ring
  have hc : IsDefectChain p a m N := by
    refine ⟨fun n hn => (hp n hn).2, fun n hn => ?_, hrec⟩
    have h1 := hrec n hn
    have h2 := (hp n hn).2.two_le
    have h3 := (hdigit n).1
    have h4 : (p n : ℤ) < p (n + 1) := by
      rw [h1]
      have : (2 : ℤ) ≤ a := by exact_mod_cast ha2
      have : (2 : ℤ) ≤ p n := by exact_mod_cast h2
      nlinarith
    exact_mod_cast h4
  -- the digit is forced or eventually constant
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · -- `a = 2`: the digit is `1`
    refine not_eventually_affine_recurrence (p := p) (a := 2) (by norm_num) 1 (N := N)
      (fun n hn => hc.prime n hn) (fun n hn => hc.mono n hn) (fun n hn => ?_)
    have h0 := hc.defect_ne_zero le_rfl hn
    have hd := hdigit n
    rw [hc.step n hn, show m n = 1 by push_cast at hd; omega]
  · -- `a = 3`: the digit is even and nonzero, hence `2`
    refine not_eventually_affine_recurrence (p := p) (a := 3) (by norm_num) 2 (N := N + 3)
      (fun n hn => hc.prime n (by omega)) (fun n hn => hc.mono n (by omega)) (fun n hn => ?_)
    have h0 := hc.defect_ne_zero (by norm_num) (n := n) (by omega)
    have he := hc.two_dvd_defect (by norm_num) (n := n) (by omega)
      (hc.lt_of_le 2 (by omega)).ne' (hc.lt_of_le 2 (by omega)).ne'
    have hd := hdigit n
    rw [hc.step n (by omega), show m n = 2 by push_cast at hd; omega]
  · -- `a = 4`: the digit is `1` or `3`, and `1`-steps walk mod `3`
    have h41 : ((4 : ℕ) : ZMod 3) = 1 := by push_cast; decide
    have h30 : ((3 : ℤ) : ZMod 3) = 0 := by push_cast; decide
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine (hc.mono_from (N' := N + 3) (by omega)).false_of_unipotent (by norm_num) (ℓ := 3)
      h41 (r := 1) one_ne_zero (d₀ := 3) h30 (fun n hn => ?_)
    have hodd := hc.not_dvd_defect Nat.prime_two (by norm_num) (n := n) (by omega)
      (hc.lt_of_le 2 (by omega)).ne'
    have hd := hdigit n
    push_cast at hodd hd
    rcases (show m n = 1 ∨ m n = 3 by omega) with h | h
    · right; rw [h]; simp
    · left; exact h
  · -- `a = 5`: the digit is `2` or `4`, forced mod `3`
    refine (hc.mono_from (N' := N + 3) (by omega)).false_of_two_classes_mod_three (by norm_num)
      (by norm_num) (d₁ := 2) (d₂ := 4) (by push_cast; decide) (by push_cast; decide)
      (by push_cast; decide) (fun n hn => ?_)
    have h0 := hc.defect_ne_zero (by norm_num) (n := n) (by omega)
    have he := hc.two_dvd_defect (by norm_num) (n := n) (by omega)
      (hc.lt_of_le 2 (by omega)).ne' (hc.lt_of_le 2 (by omega)).ne'
    have hd := hdigit n
    push_cast at hd
    omega
  · -- `a = 6`: the digit is `1` or `5`, and `1`-steps walk mod `5`
    have h61 : ((6 : ℕ) : ZMod 5) = 1 := by push_cast; decide
    have h50 : ((5 : ℤ) : ZMod 5) = 0 := by push_cast; decide
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    refine (hc.mono_from (N' := N + 5) (by omega)).false_of_unipotent (by norm_num) (ℓ := 5)
      h61 (r := 1) one_ne_zero (d₀ := 5) h50 (fun n hn => ?_)
    have h2 := hc.not_dvd_defect Nat.prime_two (by norm_num) (n := n) (by omega)
      (hc.lt_of_le 2 (by omega)).ne'
    have h3 := hc.not_dvd_defect Nat.prime_three (by norm_num) (n := n) (by omega)
      (hc.lt_of_le 3 (by omega)).ne'
    have hd := hdigit n
    push_cast at h2 h3 hd
    rcases (show m n = 1 ∨ m n = 5 by omega) with h | h
    · right; rw [h]; simp
    · left; exact h

/-- **Nearest integers to geometric sequences.** For `C > 0` and `a ∈ {2, 4, 5}`, no sequence of
primes stays within `1/2` of `C aⁿ` from some index on. -/
theorem not_eventually_prime_near (ha : a ∈ ({2, 4, 5} : Finset ℕ)) {C : ℝ} (hC : 0 < C)
    (p : ℕ → ℕ) :
    ¬ ∀ᶠ n in atTop, (p n).Prime ∧ |(p n : ℝ) - C * (a : ℝ) ^ n| ≤ 1 / 2 := by
  intro hev
  have ha2 : 2 ≤ a := by simp only [Finset.mem_insert, Finset.mem_singleton] at ha; omega
  -- the members grow, so the chain is eventually increasing
  have hgrow : ∀ᶠ n in atTop, (4 : ℝ) ≤ C * (a : ℝ) ^ n - 1 / 2 := by
    have ht : Tendsto (fun n : ℕ => C * (a : ℝ) ^ n) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (show 1 < a by omega))).const_mul_atTop hC
    filter_upwards [ht.eventually_ge_atTop (4 + 1 / 2)] with n hn
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hev.and hgrow)
  let m : ℕ → ℤ := fun n => (p (n + 1) : ℤ) - a * p n
  have hbig : ∀ n, N ≤ n → 4 ≤ p n := by
    intro n hn
    have h1 := (hN n hn).1.2
    have h2 := (hN n hn).2
    have : (4 : ℝ) ≤ p n := by linarith [neg_abs_le ((p n : ℝ) - C * (a : ℝ) ^ n)]
    exact_mod_cast this
  have hm : ∀ n, N ≤ n → |m n| ≤ (a + 1) / 2 := by
    intro n hn
    have h := abs_defect_le (hN n hn).1.2 (hN (n + 1) (by omega)).1.2
    have h' : |((m n : ℤ) : ℝ)| ≤ (a + 1) * (1 / 2) := h
    have h2 : ((|m n| : ℤ) : ℝ) * 2 ≤ (a : ℝ) + 1 := by rw [Int.cast_abs]; linarith
    have : |m n| * 2 ≤ (a : ℤ) + 1 := by exact_mod_cast h2
    omega
  have hc : IsDefectChain p a m N := by
    refine ⟨fun n hn => (hN n hn).1.1, fun n hn => ?_, fun n hn => by simp only [m]; ring⟩
    have h1 := hm n hn
    have h2 := hbig n hn
    have h3 : (p (n + 1) : ℤ) = a * p n + m n := by simp only [m]; ring
    have hb := abs_le.mp (show |m n| ≤ (a + 1) / 2 from h1)
    have : (p n : ℤ) < p (n + 1) := by
      rw [h3]
      have : (2 : ℤ) ≤ a := by exact_mod_cast ha2
      have : (4 : ℤ) ≤ p n := by exact_mod_cast h2
      have : (a : ℤ) * p n ≥ 2 * p n + (a - 2) * 4 := by nlinarith
      omega
    exact_mod_cast this
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact not_isDefectChain_of_even le_rfl (by norm_num) (by norm_num)
      (fun n hn => by have := hm n hn; omega) hc
  · exact not_isDefectChain_of_even (by norm_num) (by norm_num) (by norm_num)
      (fun n hn => by have := hm n hn; omega) hc
  · exact not_isDefectChain_of_odd (by norm_num) (by norm_num) (by norm_num)
      (fun n hn => by have := hm n hn; omega) hc

end GaloisForLFunctions.ArithmeticResonanceTheory
