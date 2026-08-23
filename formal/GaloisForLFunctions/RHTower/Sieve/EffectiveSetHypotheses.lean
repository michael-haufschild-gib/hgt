import GaloisForLFunctions.RHTower.Sieve.PairSumClosedForm

/-!
# The effective set discharges the confinement hypotheses

`effSet_mem_Ico` already places the effective short values inside
`[(A−1)/(Q−1)+1, (B−1)/P+1)`; the confinement and gap hypotheses of the closed-form pair bound are
immediate consequences, with `M₀`, `M₁` and `H` read off from that interval.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The lower end of the effective range. -/
def effLow (A Q : ℕ) : ℕ := (A - 1) / (Q - 1) + 1

/-- The upper end of the effective range. -/
def effHigh (B P : ℕ) : ℕ := (B - 1) / P

/-- The gap bound of the effective range. -/
def effGap (A B P Q : ℕ) : ℕ := effHigh B P - effLow A Q

theorem effSet_confined {A B P Q L : ℕ} (hP : 1 ≤ P) (hQ : 2 ≤ Q) :
    ∀ m ∈ effSet A B P Q L, 1 ≤ m ∧ effLow A Q ≤ m ∧ m ≤ effHigh B P := by
  intro m hm
  have h1 : 1 ≤ m := by
    have := effSet_subset A B P Q L hm
    rw [Finset.mem_Icc] at this
    exact this.1
  have h2 := effSet_mem_Ico hP hQ hm
  rw [Finset.mem_Ico] at h2
  exact ⟨h1, h2.1, by rw [effHigh]; omega⟩

theorem effSet_gap {A B P Q L : ℕ} (hP : 1 ≤ P) (hQ : 2 ≤ Q) :
    ∀ m₁ ∈ effSet A B P Q L, ∀ m₂ ∈ (effSet A B P Q L).erase m₁,
      Nat.dist m₁ m₂ ∈ Finset.Icc 1 (effGap A B P Q) := by
  intro m₁ hm₁ m₂ hm₂
  have hm₂' : m₂ ∈ effSet A B P Q L := Finset.mem_of_mem_erase hm₂
  have hne : m₂ ≠ m₁ := Finset.ne_of_mem_erase hm₂
  obtain ⟨-, hlo₁, hhi₁⟩ := effSet_confined hP hQ m₁ hm₁
  obtain ⟨-, hlo₂, hhi₂⟩ := effSet_confined hP hQ m₂ hm₂'
  rw [Finset.mem_Icc, effGap, Nat.dist]
  constructor
  · omega
  · omega

theorem one_le_effLow (A Q : ℕ) : 1 ≤ effLow A Q := by
  rw [effLow]
  exact Nat.le_add_left 1 _

/-- **The type-II pair sum of a dyadic block, with the confinement hypotheses discharged.** -/
theorem pairSum_block_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) (hQ : 2 ≤ Q) (b : ℕ → ℝ)
    (hfour : ∀ m ∈ effSet A B P Q L, 4 * (r / m) ≤ (P : ℝ))
    (hlam : ∀ m₁ ∈ effSet A B P Q L, ∀ m₂ ∈ effSet A B P Q L,
      curvedLambda (T * |r / m₁ - r / m₂|) (P : ℝ) ≤ 1) :
    (∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
        |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
          maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖)
      ≤ ((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |b m| ^ 2)
        + (∑ m ∈ effSet A B P Q L, |b m| ^ 2)
          * (2 * ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
              gapCorrBound T r (effLow A Q) (effHigh B P) P Q h) :=
  pairSum_closed_le hT hr hA hB hP (one_le_effLow A Q) b
    (effSet_confined hP hQ) (effSet_gap hP hQ) hfour hlam

end

end RHTower.Sieve
