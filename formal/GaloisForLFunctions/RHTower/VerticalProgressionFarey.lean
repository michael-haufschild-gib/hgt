import GaloisForLFunctions.RHTower.VerticalProgressionOffResonance

/-!
# Farey spacing of resonant ratios

* **Spacing** (`one_div_mul_le_abs_sub_div`): distinct reduced fractions `a/b ≠ a'/b'` satisfy
  `|a/b − a'/b'| ≥ 1/(bb')`.
* **Counting** (`card_le_of_window`): reduced fractions with denominators `≤ B` in a window of
  length `λ` number at most `λB² + 1` (the map `a/b ↦ ⌊(a/b − lo) B²⌋` is injective).
-/

open Finset

namespace RHTower.VerticalAP

noncomputable section

theorem div_ne_div_of_coprime {a b a' b' : ℕ} (hab : Nat.Coprime a b) (hab' : Nat.Coprime a' b')
    (hb : 0 < b) (hb' : 0 < b') (hne : (a, b) ≠ (a', b')) :
    (a : ℝ) * b' ≠ (a' : ℝ) * b := by
  intro h
  have h' : a * b' = a' * b := by exact_mod_cast h
  apply hne
  have h1 : b ∣ b' := by
    have : b ∣ a * b' := ⟨a', by rw [h']; ring⟩
    exact hab.symm.dvd_of_dvd_mul_left this
  have h2 : b' ∣ b := by
    have : b' ∣ a' * b := ⟨a, by rw [← h']; ring⟩
    exact hab'.symm.dvd_of_dvd_mul_left this
  have hbb : b = b' := Nat.dvd_antisymm h1 h2
  subst hbb
  rw [Nat.eq_of_mul_eq_mul_right hb h']

/-- **Farey spacing.** -/
theorem one_div_mul_le_abs_sub_div {a b a' b' : ℕ} (hab : Nat.Coprime a b)
    (hab' : Nat.Coprime a' b') (hb : 0 < b) (hb' : 0 < b') (hne : (a, b) ≠ (a', b')) :
    1 / ((b : ℝ) * b') ≤ |(a : ℝ) / b - (a' : ℝ) / b'| := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb'R : (0 : ℝ) < b' := by exact_mod_cast hb'
  have hz : ((a : ℤ) * b' - (a' : ℤ) * b) ≠ 0 := by
    intro h0
    apply div_ne_div_of_coprime hab hab' hb hb' hne
    have : ((a : ℤ) * b' : ℤ) = (a' : ℤ) * b := sub_eq_zero.mp h0
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ |(a : ℝ) * b' - (a' : ℝ) * b| := by
    have := Int.one_le_abs hz
    exact_mod_cast this
  rw [show (a : ℝ) / b - (a' : ℝ) / b' = ((a : ℝ) * b' - (a' : ℝ) * b) / (b * b') by
    field_simp, abs_div, abs_of_pos (mul_pos hbR hb'R)]
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- **Counting reduced fractions in a window.** -/
theorem card_le_of_window (S : Finset (ℕ × ℕ)) {B : ℕ} {lo len : ℝ} (hlen : 0 ≤ len)
    (hS : ∀ c ∈ S, Nat.Coprime c.1 c.2 ∧ 0 < c.2 ∧ c.2 ≤ B ∧ lo ≤ (c.1 : ℝ) / c.2 ∧
      (c.1 : ℝ) / c.2 ≤ lo + len) :
    (S.card : ℝ) ≤ len * (B : ℝ) ^ 2 + 1 := by
  rcases Nat.eq_zero_or_pos B with hB0 | hB0
  · have : S = ∅ := by
      ext c; simp only [Finset.notMem_empty, iff_false]
      intro hc; have := hS c hc; omega
    rw [this]; simp; positivity
  set f : ℕ × ℕ → ℕ := fun c => ⌊((c.1 : ℝ) / c.2 - lo) * (B : ℝ) ^ 2⌋₊
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB0
  have hmaps : ∀ c ∈ S, f c ∈ Finset.range (⌊len * (B : ℝ) ^ 2⌋₊ + 1) := by
    intro c hc
    obtain ⟨_, _, _, h1, h2⟩ := hS c hc
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (by nlinarith)
  have hinj : Set.InjOn f S := by
    intro c hc c' hc' hff
    by_contra hne
    obtain ⟨hcop, hb, hbB, h1, _⟩ := hS c hc
    obtain ⟨hcop', hb', hbB', h1', _⟩ := hS c' hc'
    have hsp := one_div_mul_le_abs_sub_div hcop hcop' hb hb' (by
      intro h; apply hne; exact Prod.ext (by simpa using congrArg Prod.fst h)
        (by simpa using congrArg Prod.snd h))
    have hx : 0 ≤ ((c.1 : ℝ) / c.2 - lo) * (B : ℝ) ^ 2 := by nlinarith
    have hx' : 0 ≤ ((c'.1 : ℝ) / c'.2 - lo) * (B : ℝ) ^ 2 := by nlinarith
    have hlt : |((c.1 : ℝ) / c.2 - lo) * (B : ℝ) ^ 2 - ((c'.1 : ℝ) / c'.2 - lo) * (B : ℝ) ^ 2| < 1 := by
      have e1 := Nat.floor_le hx
      have e2 := Nat.lt_floor_add_one (((c.1 : ℝ) / c.2 - lo) * (B : ℝ) ^ 2)
      have e3 := Nat.floor_le hx'
      have e4 := Nat.lt_floor_add_one (((c'.1 : ℝ) / c'.2 - lo) * (B : ℝ) ^ 2)
      have hff' : (f c : ℝ) = (f c' : ℝ) := by exact_mod_cast hff
      simp only [f] at hff'
      rw [abs_lt]; constructor <;> linarith
    have hbb : (c.2 : ℝ) * c'.2 ≤ (B : ℝ) ^ 2 := by
      have : (c.2 : ℝ) ≤ B := by exact_mod_cast hbB
      have : (c'.2 : ℝ) ≤ B := by exact_mod_cast hbB'
      nlinarith
    have hbb0 : (0 : ℝ) < (c.2 : ℝ) * c'.2 := by
      have : (0 : ℝ) < c.2 := by exact_mod_cast hb
      have : (0 : ℝ) < c'.2 := by exact_mod_cast hb'
      positivity
    rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (B : ℝ) ^ 2),
      show (c.1 : ℝ) / c.2 - lo - ((c'.1 : ℝ) / c'.2 - lo) = (c.1 : ℝ) / c.2 - (c'.1 : ℝ) / c'.2 by
        ring] at hlt
    have : 1 / ((c.2 : ℝ) * c'.2) * (B : ℝ) ^ 2 < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsp (by positivity)) hlt
    rw [div_mul_eq_mul_div, one_mul, div_lt_one hbb0] at this
    linarith
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_range] at hcard
  have : ((⌊len * (B : ℝ) ^ 2⌋₊ + 1 : ℕ) : ℝ) ≤ len * (B : ℝ) ^ 2 + 1 := by
    push_cast
    linarith [Nat.floor_le (by positivity : 0 ≤ len * (B : ℝ) ^ 2)]
  exact le_trans (by exact_mod_cast hcard) this

end

end RHTower.VerticalAP
