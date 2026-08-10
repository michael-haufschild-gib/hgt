import GaloisForLFunctions.RHTower.Sieve.FibreStartSeparated

/-!
# Separated points are few

The counting core of every spacing argument: if the points `u i`, `i` in a finite set, are pairwise
separated by `g` and all lie in an interval of length `L`, then there are at most `L/g + 1` of them.

The proof is a cell count rather than an ordering argument: `i ↦ ⌊(u i − c)/g⌋` is injective,
because two points in a common cell of length `g` are less than `g` apart, and its image lies in
`{0, …, ⌊L/g⌋}`.

Applied to the starting points `log(x/a)` of `FibreStartSeparated` — separation `1/(2√x)`, span
`log 2` — this returns `2√x·log 2 + 1`, which matches the `√x` fibres of the block up to a constant:
the separation is sharp, and no room is being lost in the passage to an integral.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **Separated points in an interval are few.** -/
theorem card_le_of_separated {ι : Type*} [DecidableEq ι] {s : Finset ι} {u : ι → ℝ}
    {g L c : ℝ} (hg : 0 < g) (hL : 0 ≤ L)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → g ≤ |u i - u j|)
    (hin : ∀ i ∈ s, c ≤ u i ∧ u i ≤ c + L) :
    (s.card : ℝ) ≤ L / g + 1 := by
  classical
  -- the cell index is injective on `s`
  have hinj : Set.InjOn (fun i => ⌊(u i - c) / g⌋₊) s := by
    intro i hi j hj hij
    by_contra hne
    have hi0 : 0 ≤ (u i - c) / g := div_nonneg (by linarith [(hin i hi).1]) hg.le
    have hj0 : 0 ≤ (u j - c) / g := div_nonneg (by linarith [(hin j hj).1]) hg.le
    have hik : ((⌊(u i - c) / g⌋₊ : ℕ) : ℝ) ≤ (u i - c) / g := Nat.floor_le hi0
    have hik' : (u i - c) / g < ((⌊(u i - c) / g⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hjk : ((⌊(u j - c) / g⌋₊ : ℕ) : ℝ) ≤ (u j - c) / g := Nat.floor_le hj0
    have hjk' : (u j - c) / g < ((⌊(u j - c) / g⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hcast : ((⌊(u i - c) / g⌋₊ : ℕ) : ℝ) = ((⌊(u j - c) / g⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hij
    have hdiff : |(u i - c) / g - (u j - c) / g| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have heq : (u i - c) / g - (u j - c) / g = (u i - u j) / g := by ring
    rw [heq, abs_div, abs_of_pos hg, div_lt_one hg] at hdiff
    exact absurd (hsep i hi j hj hne) (by linarith)
  -- the cell index lands in a range of size `⌊L/g⌋ + 1`
  have hmaps : ∀ i ∈ s, ⌊(u i - c) / g⌋₊ ∈ Finset.range (⌊L / g⌋₊ + 1) := by
    intro i hi
    rw [Finset.mem_range]
    have hle : (u i - c) / g ≤ L / g :=
      div_le_div_of_nonneg_right (by linarith [(hin i hi).2]) hg.le
    have := Nat.floor_le_floor hle
    omega
  have hcard := Finset.card_le_card_of_injOn (fun i => ⌊(u i - c) / g⌋₊) hmaps hinj
  rw [Finset.card_range] at hcard
  have hcardR : (s.card : ℝ) ≤ ((⌊L / g⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
  have hfl : ((⌊L / g⌋₊ : ℕ) : ℝ) ≤ L / g := Nat.floor_le (by positivity)
  linarith

end RHTower.Sieve

end
