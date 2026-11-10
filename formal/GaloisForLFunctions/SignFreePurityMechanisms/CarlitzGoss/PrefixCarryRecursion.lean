import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitContents

/-!
# Descending carry recursion for inverse-content prefixes

Read prefix lengths backwards. Given the next residue row `v`, lower the
terminal inverse coordinate by one, then take the smaller of the preceding
coordinate minus one and `p` times the next residue coordinate. The resulting
digit counts are nonnegative and nested. Every positive count drops by at
least `p−1` when one prefix is removed.
-/

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- One row of the carry modification, indexed by the number of removed prefixes. -/
def backwardPrefixRow (p w : ℤ) (v : ℕ → ℤ) : ℕ → ℤ
  | 0 => min (w - 1) (p * v 0)
  | n + 1 => min (backwardPrefixRow p w v n - 1) (p * v (n + 1))

theorem backwardPrefixRow_le_mul (p w : ℤ) (v : ℕ → ℤ) (n : ℕ) :
    backwardPrefixRow p w v n ≤ p * v n := by
  cases n <;> exact min_le_right _ _

theorem backwardPrefixRow_step (p w : ℤ) (v : ℕ → ℤ) (n : ℕ) :
    backwardPrefixRow p w v (n + 1) + 1 ≤ backwardPrefixRow p w v n := by
  have h := min_le_left (backwardPrefixRow p w v n - 1) (p * v (n + 1))
  change backwardPrefixRow p w v (n + 1) ≤ backwardPrefixRow p w v n - 1 at h
  omega

/-- The inverse coordinate remains at least the number of retained proper parts. -/
theorem backwardPrefixRow_floor {p w : ℤ} {v : ℕ → ℤ} {m : ℕ}
    (hp : 1 ≤ p) (hw : (m : ℤ) + 1 ≤ w)
    (hv : ∀ n ≤ m, (m : ℤ) - n ≤ v n) :
    ∀ n ≤ m, (m : ℤ) - n ≤ backwardPrefixRow p w v n := by
  intro n
  induction n with
  | zero =>
    intro hn
    have hv0 := hv 0 hn
    have hm : (0 : ℤ) ≤ m := Nat.cast_nonneg m
    have hmul := mul_le_mul_of_nonneg_left hv0 (by omega : 0 ≤ p)
    apply le_min
    · omega
    · simp only [Nat.cast_zero, sub_zero] at hv0 hmul ⊢
      nlinarith only [hm, hp, hmul]
  | succ n ih =>
    intro hn
    have hn' : n ≤ m := by omega
    have hi := ih hn'
    have hvn := hv (n + 1) hn
    have hfloor : (0 : ℤ) ≤ (m : ℤ) - (n + 1 : ℕ) := by omega
    have hmul := mul_le_mul_of_nonneg_left hvn (by omega : 0 ≤ p)
    change (m : ℤ) - (n + 1 : ℕ) ≤
      min (backwardPrefixRow p w v n - 1) (p * v (n + 1))
    apply le_min
    · push_cast
      omega
    · nlinarith only [hfloor, hp, hmul]

/-- The empty prefix has inverse coordinate zero. -/
theorem backwardPrefixRow_empty {p w : ℤ} {v : ℕ → ℤ} {m : ℕ}
    (hp : 1 ≤ p) (hw : (m : ℤ) + 1 ≤ w)
    (hv : ∀ n ≤ m, (m : ℤ) - n ≤ v n) (hzero : v m = 0) :
    backwardPrefixRow p w v m = 0 := by
  have hlo := backwardPrefixRow_floor hp hw hv m le_rfl
  have hhi := backwardPrefixRow_le_mul p w v m
  rw [hzero, mul_zero] at hhi
  omega

/-- Digit counts associated with the modified inverse-content row. -/
def backwardPrefixContent (p w : ℤ) (v : ℕ → ℤ) (n : ℕ) : ℤ :=
  p * v n - backwardPrefixRow p w v n

theorem backwardPrefixContent_nonneg (p w : ℤ) (v : ℕ → ℤ) (n : ℕ) :
    0 ≤ backwardPrefixContent p w v n :=
  sub_nonneg.mpr (backwardPrefixRow_le_mul p w v n)

/-- A positive shorter prefix forces the full `p−1` increase in digit count. -/
theorem backwardPrefixContent_gap {p w : ℤ} {v : ℕ → ℤ} {n : ℕ}
    (hp : 1 ≤ p) (hv : v (n + 1) + 1 ≤ v n)
    (hpos : 0 < backwardPrefixContent p w v (n + 1)) :
    backwardPrefixContent p w v (n + 1) + (p - 1) ≤
      backwardPrefixContent p w v n := by
  have he : backwardPrefixRow p w v (n + 1) = backwardPrefixRow p w v n - 1 := by
    by_cases hle : backwardPrefixRow p w v n - 1 ≤ p * v (n + 1)
    · exact min_eq_left hle
    · have hz : backwardPrefixContent p w v (n + 1) = 0 := by
        unfold backwardPrefixContent
        rw [backwardPrefixRow, min_eq_right (le_of_not_ge hle), sub_self]
      omega
  have hmul := mul_le_mul_of_nonneg_left hv (by omega : 0 ≤ p)
  unfold backwardPrefixContent
  rw [he]
  nlinarith only [hmul]

/-- Modified residue counts form nested prefixes. -/
theorem backwardPrefixContent_step {p w : ℤ} {v : ℕ → ℤ} {n : ℕ}
    (hp : 1 ≤ p) (hv : v (n + 1) + 1 ≤ v n) :
    backwardPrefixContent p w v (n + 1) ≤ backwardPrefixContent p w v n := by
  have hn := backwardPrefixContent_nonneg p w v (n + 1)
  by_cases hz : backwardPrefixContent p w v (n + 1) = 0
  · rw [hz]
    exact backwardPrefixContent_nonneg p w v n
  · have hg := backwardPrefixContent_gap hp hv (by omega :
        0 < backwardPrefixContent p w v (n + 1))
    omega

/-- At the first affected residue, lowering the inverse coordinate adds one digit. -/
theorem backwardPrefixContent_terminal_eq {p w : ℤ} {v : ℕ → ℤ}
    (hw : w ≤ p * v 0) :
    backwardPrefixContent p w v 0 = p * v 0 - w + 1 := by
  unfold backwardPrefixContent
  rw [backwardPrefixRow, min_eq_left (by omega : w - 1 ≤ p * v 0)]
  omega

/-- In each following residue, the terminal prefix loses at least `p−1`
digits unless it becomes empty. -/
theorem backwardPrefixContent_terminal_le {p w t : ℤ} {v : ℕ → ℤ}
    (hp : 0 ≤ p) (hv : v 0 ≤ t - 1) :
    backwardPrefixContent p w v 0 ≤ max 0 (p * t - w - (p - 1)) := by
  have hm := mul_le_mul_of_nonneg_left hv hp
  unfold backwardPrefixContent
  by_cases hle : w - 1 ≤ p * v 0
  · rw [backwardPrefixRow, min_eq_left hle]
    have hmax := le_max_right (0 : ℤ) (p * t - w - (p - 1))
    nlinarith only [hm, hmax]
  · rw [backwardPrefixRow, min_eq_right (le_of_not_ge hle), sub_self]
    exact le_max_left _ _

/-- Successive residue rows of the carry modification. Row zero is the
unchanged row immediately beyond the affected interval. -/
def backwardCarryRows (p : ℤ) (w : ℕ → ℤ) (v : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => v
  | r + 1 => backwardPrefixRow p (w r) (backwardCarryRows p w v r)

theorem backwardCarryRows_floor {p : ℤ} {w v : ℕ → ℤ} {m R : ℕ}
    (hp : 1 ≤ p) (hw : ∀ r < R, (m : ℤ) + 1 ≤ w r)
    (hv : ∀ n ≤ m, (m : ℤ) - n ≤ v n) :
    ∀ r ≤ R, ∀ n ≤ m, (m : ℤ) - n ≤ backwardCarryRows p w v r n := by
  intro r
  induction r with
  | zero => exact fun _ => hv
  | succ r ih =>
    intro hr
    exact backwardPrefixRow_floor hp (hw r (by omega)) (ih (by omega))

theorem backwardCarryRows_step {p : ℤ} {w v : ℕ → ℤ} {n : ℕ}
    (hv : v (n + 1) + 1 ≤ v n) (r : ℕ) :
    backwardCarryRows p w v r (n + 1) + 1 ≤ backwardCarryRows p w v r n := by
  cases r with
  | zero => exact hv
  | succ r => exact backwardPrefixRow_step p (w r) (backwardCarryRows p w v r) n

theorem backwardCarryRows_empty {p : ℤ} {w v : ℕ → ℤ} {m R : ℕ}
    (hp : 1 ≤ p) (hw : ∀ r < R, (m : ℤ) + 1 ≤ w r)
    (hv : ∀ n ≤ m, (m : ℤ) - n ≤ v n) (hzero : v m = 0) :
    ∀ r ≤ R, backwardCarryRows p w v r m = 0 := by
  intro r
  induction r with
  | zero => exact fun _ => hzero
  | succ r ih =>
    intro hr
    exact backwardPrefixRow_empty hp (hw r (by omega))
      (backwardCarryRows_floor hp hw hv r (by omega)) (ih (by omega))

/-- The residue-prefix counts of every modified row are nonnegative, nested,
and have a gap of at least `p−1` whenever the shorter prefix is nonempty. -/
theorem backwardCarryRows_content {p : ℤ} {w v : ℕ → ℤ} {n : ℕ}
    (hp : 1 ≤ p) (hv : v (n + 1) + 1 ≤ v n) (r : ℕ) :
    let c := backwardPrefixContent p (w r) (backwardCarryRows p w v r)
    0 ≤ c n ∧ c (n + 1) ≤ c n ∧ (0 < c (n + 1) → c (n + 1) + (p - 1) ≤ c n) := by
  dsimp only
  have hs := backwardCarryRows_step (p := p) (w := w) hv r
  exact ⟨backwardPrefixContent_nonneg _ _ _ _, backwardPrefixContent_step hp hs,
    backwardPrefixContent_gap hp hs⟩

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.backwardPrefixContent_gap
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.backwardCarryRows_content
