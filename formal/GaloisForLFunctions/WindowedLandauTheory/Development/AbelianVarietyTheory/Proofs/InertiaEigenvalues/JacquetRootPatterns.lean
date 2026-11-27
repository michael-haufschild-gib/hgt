import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PatternRootExchange

/-! Moving the roots attached to the middle block one index at a time
preserves the Jacquet trace. -/

noncomputable section
open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq.JacquetPattern

variable {g n : ℕ} [Fact g.Prime]

/-- Indices of the middle block of length k starting at s. -/
def middle (k s a : ℕ) : Prop := s ≤ a ∧ a < s + k

/-- In step i the middle block receives roots from rows strictly before i
and sends roots to the remaining columns of the outer blocks. -/
def allowed (k s i : ℕ) (a b : Fin n) : Prop :=
  (middle k s a ∧ middle k s b ∧ a < b) ∨
  (¬ middle k s a ∧ ¬ middle k s b ∧ a < b) ∨
  ((a : ℕ) < i ∧ middle k s b) ∨
  (middle k s a ∧ ((i < (b : ℕ) ∧ (b : ℕ) < s) ∨
    ((b : ℕ) = s + k ∧ i < s) ∨ s + k < (b : ℕ)))

/-- The character roots connect consecutive indices inside each chain. -/
def selected (k s : ℕ) (a b : Fin n) : Prop :=
  ((b : ℕ) = a + 1 ∧ (b : ℕ) < s) ∨
  ((a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) ∨
  ((b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ)) ∨
  ((b : ℕ) = a + 1 ∧ middle k s a ∧ middle k s b)

private theorem allowed_trans {k s i : ℕ} (hs : i ≤ s) (a b c : Fin n)
    (hab : allowed k s i a b) (hbc : allowed k s i b c) : allowed k s i a c := by
  simp only [allowed, middle, Fin.lt_def] at *
  omega

private theorem allowed_irrefl {k s i : ℕ} (hs : i ≤ s) (a : Fin n) :
    ¬ allowed k s i a a := by
  simp only [allowed, middle, Fin.lt_def]
  omega

private theorem allowed_no_path {k s i : ℕ} (hs : i ≤ s) (a b c : Fin n)
    (hab : allowed k s i a b) (hbc : allowed k s i b c) : ¬ selected k s a c := by
  simp only [allowed, selected, middle, Fin.lt_def] at *
  omega

private theorem allowed_union {k s i : ℕ} (hi : 1 ≤ i) (hs : i ≤ s) (a b : Fin n) :
    (allowed k s i a b ∨ allowed k s (i - 1) a b) ↔
      (middle k s a ∧ middle k s b ∧ a < b) ∨
      (¬ middle k s a ∧ ¬ middle k s b ∧ a < b) ∨
      ((a : ℕ) < i ∧ middle k s b) ∨
      (middle k s a ∧ ¬ middle k s b ∧ i ≤ (b : ℕ)) := by
  simp only [allowed, middle, Fin.lt_def]
  constructor <;> intro h <;> omega

private theorem allowed_union_trans {k s i : ℕ} (hi : 1 ≤ i) (hs : i ≤ s)
    (a b c : Fin n) (hab : allowed k s i a b ∨ allowed k s (i - 1) a b)
    (hbc : allowed k s i b c ∨ allowed k s (i - 1) b c) :
    allowed k s i a c ∨ allowed k s (i - 1) a c := by
  rw [allowed_union hi hs] at hab hbc ⊢
  simp only [middle, Fin.lt_def] at hab hbc ⊢
  omega

private theorem allowed_diff_row {k s i : ℕ} (hi : 1 ≤ i) (hs : i ≤ s)
    {p : Fin n} (hp : (p : ℕ) = i - 1) (a b : Fin n) :
    (allowed k s i a b ∧ ¬ allowed k s (i - 1) a b) ↔ a = p ∧ middle k s b := by
  simp only [allowed, middle, Fin.lt_def, Fin.ext_iff]
  constructor <;> intro h <;> omega

private theorem allowed_diff_column {k s i : ℕ} (hi : 1 ≤ i) {q : Fin n}
    (hq : (i < s ∧ (q : ℕ) = i) ∨ (i = s ∧ (q : ℕ) = s + k)) (a b : Fin n) :
    (allowed k s (i - 1) a b ∧ ¬ allowed k s i a b) ↔ middle k s a ∧ b = q := by
  simp only [allowed, middle, Fin.lt_def, Fin.ext_iff]
  constructor <;> intro h <;> omega

private theorem allowed_conj_row {k s i : ℕ} (hi : 1 ≤ i) (hs : i ≤ s)
    {p q : Fin n} (hp : (p : ℕ) = i - 1)
    (hq : (i < s ∧ (q : ℕ) = i) ∨ (i = s ∧ (q : ℕ) = s + k))
    (w : Fin n) (hw : middle k s w) (a b : Fin n)
    (ha : a = p ∨ (allowed k s i a p ∨ allowed k s (i - 1) a p))
    (hb : w = b ∨ (allowed k s i w b ∨ allowed k s (i - 1) w b)) :
    allowed k s i a b ∧ (selected k s a b → a = p ∧ b = q) := by
  rw [allowed_union hi hs] at ha hb
  simp only [allowed, selected, middle, Fin.lt_def, Fin.ext_iff] at ha hb hw ⊢
  exact ⟨by omega, fun h => by omega⟩

private theorem allowed_conj_column {k s i : ℕ} (hi : 1 ≤ i) (hs : i ≤ s)
    {p q : Fin n} (hp : (p : ℕ) = i - 1)
    (hq : (i < s ∧ (q : ℕ) = i) ∨ (i = s ∧ (q : ℕ) = s + k))
    (w : Fin n) (hw : middle k s w) (a b : Fin n)
    (ha : a = w ∨ (allowed k s i a w ∨ allowed k s (i - 1) a w))
    (hb : q = b ∨ (allowed k s i q b ∨ allowed k s (i - 1) q b)) :
    allowed k s (i - 1) a b ∧ (selected k s a b → a = p ∧ b = q) := by
  rw [allowed_union hi hs] at ha hb
  simp only [allowed, selected, middle, Fin.lt_def, Fin.ext_iff] at ha hb hw ⊢
  exact ⟨by omega, fun h => by omega⟩

/-- One row-column exchange preserves the trace of the character average. -/
theorem tr_step (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) {k s i : ℕ}
    (hn : n = k + 2 * s + 1) (hi : 1 ≤ i) (hs : i ≤ s)
    (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    tr (eDat g n (InPattern (allowed k s i)) (patternEntrySum (selected k s)) ψ) χ =
      tr (eDat g n (InPattern (allowed k s (i - 1))) (patternEntrySum (selected k s)) ψ) χ := by
  obtain ⟨p, hp⟩ : ∃ p : Fin n, (p : ℕ) = i - 1 := ⟨⟨i - 1, by omega⟩, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin n, (i < s ∧ (q : ℕ) = i) ∨ (i = s ∧ (q : ℕ) = s + k) := by
    by_cases h : i < s
    · exact ⟨⟨i, by omega⟩, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨⟨s + k, by omega⟩, Or.inr ⟨by omega, rfl⟩⟩
  have hs' : i - 1 ≤ s := (Nat.sub_le _ _).trans hs
  refine tr_pattern_eq_of_rootExchange ψ hψ _ _ _ (fun a => middle k s a) p q
    ?_ ?_ ?_ ?_ (allowed_irrefl hs) (allowed_irrefl hs')
    (allowed_trans hs) (allowed_trans hs') (allowed_union_trans hi hs)
    (allowed_no_path hs) (allowed_no_path hs') (allowed_diff_row hi hs hp)
    (allowed_diff_column hi hq) (allowed_conj_row hi hs hp hq)
    (allowed_conj_column hi hs hp hq) χ hχ
  · intro a h
    simp only [selected, middle] at h
    omega
  · simp only [selected, middle]
    omega
  · simp only [middle]
    omega
  · simp only [middle]
    omega

end GlobalTheory.GLq.JacquetPattern
