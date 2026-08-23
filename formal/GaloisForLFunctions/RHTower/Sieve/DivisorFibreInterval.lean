import GaloisForLFunctions.RHTower.Sieve.DirichletConvolutionRearrange

/-!
# The fibre of a block under multiplication by a fixed divisor

For a fixed `b ≥ 1` the set of `a` with `a·b` in a block `[A, B)` is again a block,
`[(A−1)/b + 1, (B−1)/b + 1)`.  This is what turns the filtered double sum produced by the
convolution rearrangement into an inner sum over an interval, which is the shape the near-diagonal
block estimate consumes.
-/

namespace RHTower.Sieve

open Finset

/-- **Membership in the fibre of a block.** -/
theorem mem_fibre_iff {A B b : ℕ} (hb : 1 ≤ b) (hA : 1 ≤ A) (hB : 1 ≤ B) (a : ℕ) :
    a * b ∈ Finset.Ico A B ↔ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1) := by
  simp only [Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have hnot : ¬ (a ≤ (A - 1) / b) := by
        intro hcon
        have := (Nat.le_div_iff_mul_le (by omega : 0 < b)).1 hcon
        omega
      omega
    · have hle : a * b ≤ B - 1 := by omega
      have := (Nat.le_div_iff_mul_le (by omega : 0 < b)).2 hle
      omega
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hcon
      have hle : a * b ≤ A - 1 := by omega
      have := (Nat.le_div_iff_mul_le (by omega : 0 < b)).2 hle
      omega
    · have hle : a ≤ (B - 1) / b := by omega
      have := (Nat.le_div_iff_mul_le (by omega : 0 < b)).1 hle
      omega

/-- **The fibre of a block is a block.** -/
theorem filter_mul_mem_Ico {A B b : ℕ} (hb : 1 ≤ b) (hA : 1 ≤ A) (hB : 1 ≤ B) (L : ℕ) :
    (Finset.Icc 1 L).filter (fun a => a * b ∈ Finset.Ico A B)
      = (Finset.Icc 1 L).filter (fun a => a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1)) :=
  Finset.filter_congr fun a _ => by
    simpa using mem_fibre_iff hb hA hB a

end RHTower.Sieve
