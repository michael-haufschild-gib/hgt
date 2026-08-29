import Mathlib

/-!
# The greatest common divisor of a tail of a sequence

The running gcd of `b N, b (N+1), …` is a positive decreasing chain under divisibility, hence
stabilizes; its stable value is the gcd of the whole tail: an integer divides every `b k` with
`k ≥ N` exactly when it divides that value.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The gcd of the first `j + 1` members of the tail of `b` starting at `N`. -/
def partialTailGcd (b : ℕ → ℕ) (N : ℕ) : ℕ → ℕ
  | 0 => b N
  | (j + 1) => Nat.gcd (partialTailGcd b N j) (b (N + j + 1))

variable {b : ℕ → ℕ}

theorem partialTailGcd_pos (hpos : ∀ k, 0 < b k) (N j : ℕ) : 0 < partialTailGcd b N j := by
  induction j with
  | zero => exact hpos N
  | succ j ih => exact Nat.gcd_pos_of_pos_left _ ih

theorem partialTailGcd_dvd (N : ℕ) : ∀ j i : ℕ, i ≤ j → partialTailGcd b N j ∣ b (N + i) := by
  intro j
  induction j with
  | zero =>
    intro i hi
    rw [Nat.le_zero.1 hi, Nat.add_zero, partialTailGcd]
  | succ j ih =>
    intro i hi
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact dvd_trans (Nat.gcd_dvd_left _ _) (ih i (by omega))
    · have : i = j + 1 := by omega
      subst this
      exact Nat.gcd_dvd_right _ _

theorem dvd_partialTailGcd {d N j : ℕ} (h : ∀ i, i ≤ j → d ∣ b (N + i)) :
    d ∣ partialTailGcd b N j := by
  induction j with
  | zero => simpa [partialTailGcd] using h 0 le_rfl
  | succ j ih =>
    exact Nat.dvd_gcd (ih fun i hi => h i (by omega)) (h (j + 1) le_rfl)

theorem partialTailGcd_dvd_of_le (N : ℕ) {i j : ℕ} (hij : i ≤ j) :
    partialTailGcd b N j ∣ partialTailGcd b N i := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact dvd_trans (Nat.gcd_dvd_left _ _) (ih (by omega))
    · have : i = j + 1 := by omega
      subst this
      rfl

/-- The gcd of the whole tail of `b` from index `N`. -/
noncomputable def tailGcd (b : ℕ → ℕ) (N : ℕ) : ℕ := sInf (Set.range (partialTailGcd b N))

theorem tailGcd_le (N j : ℕ) : tailGcd b N ≤ partialTailGcd b N j :=
  Nat.sInf_le ⟨j, rfl⟩

theorem exists_partialTailGcd_eq (N : ℕ) : ∃ J, partialTailGcd b N J = tailGcd b N := by
  obtain ⟨J, hJ⟩ := Nat.sInf_mem (s := Set.range (partialTailGcd b N)) ⟨partialTailGcd b N 0, 0, rfl⟩
  exact ⟨J, hJ⟩

theorem tailGcd_pos (hpos : ∀ k, 0 < b k) (N : ℕ) : 0 < tailGcd b N := by
  obtain ⟨J, hJ⟩ := exists_partialTailGcd_eq (b := b) N
  rw [← hJ]
  exact partialTailGcd_pos hpos N J

theorem partialTailGcd_eq_tailGcd (hpos : ∀ k, 0 < b k) {N J : ℕ}
    (hJ : partialTailGcd b N J = tailGcd b N) {j : ℕ} (hj : J ≤ j) :
    partialTailGcd b N j = tailGcd b N := by
  have hdvd : partialTailGcd b N j ∣ tailGcd b N := by
    rw [← hJ]
    exact partialTailGcd_dvd_of_le N hj
  have hle : partialTailGcd b N j ≤ tailGcd b N :=
    Nat.le_of_dvd (tailGcd_pos hpos N) hdvd
  exact le_antisymm hle (tailGcd_le N j)

theorem tailGcd_dvd (hpos : ∀ k, 0 < b k) {N k : ℕ} (hk : N ≤ k) : tailGcd b N ∣ b k := by
  obtain ⟨J, hJ⟩ := exists_partialTailGcd_eq (b := b) N
  obtain ⟨i, rfl⟩ : ∃ i, k = N + i := ⟨k - N, by omega⟩
  have hstab := partialTailGcd_eq_tailGcd hpos hJ (le_max_left J i)
  rw [← hstab]
  exact partialTailGcd_dvd N _ i (le_max_right J i)

/-- **The tail gcd characterizes tail divisibility.** -/
theorem dvd_tailGcd_iff (hpos : ∀ k, 0 < b k) (N d : ℕ) :
    d ∣ tailGcd b N ↔ ∀ k, N ≤ k → d ∣ b k := by
  constructor
  · intro hd k hk
    exact dvd_trans hd (tailGcd_dvd hpos hk)
  · intro hd
    obtain ⟨J, hJ⟩ := exists_partialTailGcd_eq (b := b) N
    rw [← hJ]
    exact dvd_partialTailGcd fun i _ => hd (N + i) (by omega)

end GaloisForLFunctions.HTGeometry
