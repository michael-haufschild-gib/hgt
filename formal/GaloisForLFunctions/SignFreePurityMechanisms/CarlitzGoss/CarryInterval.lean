import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PrefixCarryRecursion

/-!
# Carry modification on a residue interval

Apply the descending prefix recursion on `(α,β]`. Its content is unchanged
outside `[α,β]`, gains the singleton at `β`, and loses terminal digits in
every lower affected residue. Inverse-coordinate floors and positive prefix
gaps persist throughout the interval.
-/

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Lower inverse-content rows in the residue interval `(α,β]`, leaving
all other rows unchanged. Prefix lengths are read backwards. -/
def intervalCarryRow (p : ℤ) (α β : ℕ) (w : ℕ → ℕ → ℤ) (h : ℕ) : ℕ → ℤ :=
  if α < h ∧ h ≤ β then
    backwardCarryRows p (fun r => w (β - r) 0) (w (β + 1)) (β + 1 - h)
  else w h

theorem intervalCarryRow_outside (p : ℤ) (α β : ℕ) (w : ℕ → ℕ → ℤ) {h : ℕ}
    (hh : ¬ (α < h ∧ h ≤ β)) : intervalCarryRow p α β w h = w h :=
  if_neg hh

theorem intervalCarryRow_inside (p : ℤ) (α β : ℕ) (w : ℕ → ℕ → ℤ) {h : ℕ}
    (ha : α < h) (hb : h ≤ β) :
    intervalCarryRow p α β w h =
      backwardPrefixRow p (w h 0) (intervalCarryRow p α β w (h + 1)) := by
  have hidx : β + 1 - h = (β - h) + 1 := by omega
  have hwidx : β - (β - h) = h := by omega
  rw [intervalCarryRow, if_pos ⟨ha, hb⟩, hidx, backwardCarryRows, hwidx]
  by_cases he : h = β
  · subst h
    rw [Nat.sub_self, backwardCarryRows,
      intervalCarryRow_outside p α β w (by omega)]
  · have hnext : α < h + 1 ∧ h + 1 ≤ β := by omega
    rw [intervalCarryRow, if_pos hnext]
    have hi : β + 1 - (h + 1) = β - h := by omega
    rw [hi]

/-- Every changed row remains above the number of retained proper parts. -/
theorem intervalCarryRow_floor {p : ℤ} {α β m : ℕ} {w : ℕ → ℕ → ℤ}
    (hp : 1 ≤ p)
    (hhigh : ∀ h, α < h → h ≤ β → (m : ℤ) + 1 ≤ w h 0)
    (hfloor : ∀ h n, n ≤ m → (m : ℤ) - n ≤ w h n) :
    ∀ h n, n ≤ m → (m : ℤ) - n ≤ intervalCarryRow p α β w h n := by
  intro h n hn
  by_cases hh : α < h ∧ h ≤ β
  · rw [intervalCarryRow, if_pos hh]
    apply backwardCarryRows_floor hp (R := β + 1 - h) ?_
      (hfloor (β + 1)) (β + 1 - h) le_rfl n hn
    intro r hr
    exact hhigh (β - r) (by omega) (by omega)
  · rw [intervalCarryRow_outside p α β w hh]
    exact hfloor h n hn

/-- Removing one prefix lowers every modified inverse row by at least one. -/
theorem intervalCarryRow_step {p : ℤ} {α β : ℕ} {w : ℕ → ℕ → ℤ} {h n : ℕ}
    (hw : w h (n + 1) + 1 ≤ w h n) :
    intervalCarryRow p α β w h (n + 1) + 1 ≤ intervalCarryRow p α β w h n := by
  by_cases hh : α < h ∧ h ≤ β
  · rw [intervalCarryRow_inside p α β w hh.1 hh.2]
    exact backwardPrefixRow_step _ _ _ _
  · rw [intervalCarryRow_outside p α β w hh]
    exact hw

theorem intervalCarryRow_empty {p : ℤ} {α β m : ℕ} {w : ℕ → ℕ → ℤ}
    (hp : 1 ≤ p)
    (hhigh : ∀ h, α < h → h ≤ β → (m : ℤ) + 1 ≤ w h 0)
    (hfloor : ∀ h n, n ≤ m → (m : ℤ) - n ≤ w h n)
    (hempty : ∀ h, w h m = 0) : ∀ h, intervalCarryRow p α β w h m = 0 := by
  intro h
  by_cases hh : α < h ∧ h ≤ β
  · rw [intervalCarryRow, if_pos hh]
    apply backwardCarryRows_empty hp (R := β + 1 - h) ?_
      (hfloor (β + 1)) (hempty (β + 1)) (β + 1 - h) le_rfl
    intro r hr
    exact hhigh (β - r) (by omega) (by omega)
  · rw [intervalCarryRow_outside p α β w hh, hempty]

/-- Modified content in an interior row is nonnegative and nested; positive
shorter prefixes have the full `p−1` cardinality gap. -/
theorem intervalCarryRow_content {p : ℤ} {α β : ℕ} {w : ℕ → ℕ → ℤ} {h n : ℕ}
    (hp : 1 ≤ p) (ha : α < h) (hb : h ≤ β)
    (hw : w (h + 1) (n + 1) + 1 ≤ w (h + 1) n) :
    let d := intervalCarryRow p α β w
    let c := fun j => p * d (h + 1) j - d h j
    0 ≤ c n ∧ c (n + 1) ≤ c n ∧ (0 < c (n + 1) → c (n + 1) + (p - 1) ≤ c n) := by
  dsimp only
  rw [intervalCarryRow_inside p α β w ha hb]
  have hs := intervalCarryRow_step (p := p) (α := α) (β := β) hw
  exact ⟨backwardPrefixContent_nonneg _ _ _ _, backwardPrefixContent_step hp hs,
    backwardPrefixContent_gap hp hs⟩

/-- Terminal inverse coordinates decrease throughout the changed interval. -/
theorem intervalCarryRow_terminal_le (p : ℤ) (α β : ℕ) (w : ℕ → ℕ → ℤ) {h : ℕ}
    (ha : α < h) (hb : h ≤ β) : intervalCarryRow p α β w h 0 ≤ w h 0 - 1 := by
  rw [intervalCarryRow_inside p α β w ha hb]
  exact min_le_left _ _

/-- The upper endpoint adds precisely the singleton digit to the terminal prefix. -/
theorem intervalCarryRow_terminal_top {p : ℤ} {α β : ℕ} {w : ℕ → ℕ → ℤ}
    (hab : α < β) (hw : w β 0 ≤ p * w (β + 1) 0) :
    p * intervalCarryRow p α β w (β + 1) 0 - intervalCarryRow p α β w β 0 =
      p * w (β + 1) 0 - w β 0 + 1 := by
  rw [intervalCarryRow_inside p α β w hab le_rfl,
    intervalCarryRow_outside p α β w (by omega)]
  exact backwardPrefixContent_terminal_eq hw

/-- Every lower interior residue loses at least `p−1` terminal digits if nonempty. -/
theorem intervalCarryRow_terminal_interior {p : ℤ} {α β h : ℕ} {w : ℕ → ℕ → ℤ}
    (hp : 0 ≤ p) (ha : α < h) (hb : h < β) :
    p * intervalCarryRow p α β w (h + 1) 0 - intervalCarryRow p α β w h 0 ≤
      max 0 (p * w (h + 1) 0 - w h 0 - (p - 1)) := by
  rw [intervalCarryRow_inside p α β w ha hb.le]
  exact backwardPrefixContent_terminal_le hp
    (intervalCarryRow_terminal_le p α β w (by omega) (by omega))

/-- At the lower boundary the terminal prefix loses at least `p` digits. -/
theorem intervalCarryRow_terminal_boundary {p : ℤ} {α β m : ℕ} {w : ℕ → ℕ → ℤ}
    (hp : 0 ≤ p) (hab : α < β) (hw : w α 0 = m) :
    p * intervalCarryRow p α β w (α + 1) 0 - intervalCarryRow p α β w α 0 ≤
      p * w (α + 1) 0 - m - p := by
  rw [intervalCarryRow_outside p α β w (h := α) (by omega), hw]
  have hm := mul_le_mul_of_nonneg_left
    (intervalCarryRow_terminal_le p α β w (by omega) (by omega)) hp
  nlinarith only [hm]

/-- Content outside the closed interval is unchanged, including its boundary successor. -/
theorem intervalCarryRow_content_outside (p : ℤ) (α β : ℕ) (w : ℕ → ℕ → ℤ)
    {h : ℕ} (hh : ¬ (α ≤ h ∧ h ≤ β)) (n : ℕ) :
    p * intervalCarryRow p α β w (h + 1) n - intervalCarryRow p α β w h n =
      p * w (h + 1) n - w h n := by
  rw [intervalCarryRow_outside p α β w (h := h + 1) (by omega),
    intervalCarryRow_outside p α β w (h := h) (by omega)]

/-- At the unchanged lower boundary, modified prefix contents are nonnegative
and consecutive contents differ by at least `p−1`. -/
theorem intervalCarryRow_content_boundary {p : ℤ} {α β m n : ℕ} {w : ℕ → ℕ → ℤ}
    (hp : 1 ≤ p) (hn : n < m)
    (hhigh : ∀ h, α < h → h ≤ β → (m : ℤ) + 1 ≤ w h 0)
    (hfloor : ∀ h j, j ≤ m → (m : ℤ) - j ≤ w h j)
    (hboundary : ∀ j ≤ m, w α j = (m : ℤ) - j)
    (hstep : w (α + 1) (n + 1) + 1 ≤ w (α + 1) n) :
    let d := intervalCarryRow p α β w
    let c := fun j => p * d (α + 1) j - d α j
    0 ≤ c n ∧ c (n + 1) + (p - 1) ≤ c n := by
  dsimp only
  rw [intervalCarryRow_outside p α β w (h := α) (by omega),
    hboundary n hn.le, hboundary (n + 1) (by omega)]
  exact ⟨boundaryPrefixContent_nonneg hp hn.le
    (intervalCarryRow_floor hp hhigh hfloor (α + 1) n hn.le),
    boundaryPrefixContent_gap (by omega : 0 ≤ p)
      (intervalCarryRow_step (p := p) (α := α) (β := β) hstep)⟩

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.intervalCarryRow_content
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.intervalCarryRow_terminal_boundary
