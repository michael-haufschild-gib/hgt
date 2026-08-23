import GaloisForLFunctions.RHTower.Sieve.TypeIIEnergyBound
import GaloisForLFunctions.RHTower.Sieve.DivisorFibreInterval

/-!
# The type-II correlation over a coupled block

In the type-II half the two variables are coupled by `d·m ∈ I`, so the inner range depends on the
outer index.  Masking the summand with the fibre indicator restores the product structure needed
for the correlation expansion, and — because `d·m ∈ I` is symmetric — the resulting correlation
for a pair `(m₁, m₂)` runs over the INTERSECTION of two fibre intervals, which is again an
interval.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- The fibre interval of a block. -/
def fibreIco (A B b : ℕ) : Finset ℕ := Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1)

/-- The type-II summand, masked by the block constraint. -/
def maskedNdExp (T r : ℝ) (A B : ℕ) (d m : ℕ) : ℂ :=
  if m ∈ fibreIco A B d then ndExp T r m d else 0

/-- The masked inner sum is the constrained inner sum. -/
theorem sum_maskedNdExp_eq (T r : ℝ) (A B : ℕ) (d : ℕ) (Ms : Finset ℕ) (b : ℕ → ℂ) :
    (∑ m ∈ Ms, b m * maskedNdExp T r A B d m)
      = ∑ m ∈ Ms.filter (fun m => m ∈ fibreIco A B d), b m * ndExp T r m d := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [maskedNdExp]
  split_ifs <;> simp

/-- **The masked correlation runs over an interval.** -/
theorem sum_masked_correlation_eq {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (T r : ℝ)
    {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (P Q : ℕ) :
    (∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂))
      = ∑ d ∈ Finset.Ico (max P (max ((A - 1) / m₁ + 1) ((A - 1) / m₂ + 1)))
            (min Q (min ((B - 1) / m₁ + 1) ((B - 1) / m₂ + 1))),
          ndExp T r m₁ d * (starRingEnd ℂ) (ndExp T r m₂ d) := by
  classical
  have hmem : ∀ d : ℕ, 1 ≤ d →
      (m₁ ∈ fibreIco A B d ∧ m₂ ∈ fibreIco A B d)
        ↔ (d ∈ fibreIco A B m₁ ∧ d ∈ fibreIco A B m₂) := by
    intro d hd
    rw [fibreIco, fibreIco, fibreIco, fibreIco,
      ← mem_fibre_iff hd hA hB m₁, ← mem_fibre_iff hd hA hB m₂,
      ← mem_fibre_iff hm₁ hA hB d, ← mem_fibre_iff hm₂ hA hB d]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [Nat.mul_comm], by rwa [Nat.mul_comm]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [Nat.mul_comm], by rwa [Nat.mul_comm]⟩
  have hterm : ∀ d ∈ Finset.Ico P Q,
      maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)
        = if d ∈ Finset.Ico (max P (max ((A - 1) / m₁ + 1) ((A - 1) / m₂ + 1)))
              (min Q (min ((B - 1) / m₁ + 1) ((B - 1) / m₂ + 1)))
            then ndExp T r m₁ d * (starRingEnd ℂ) (ndExp T r m₂ d) else 0 := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    rw [maskedNdExp, maskedNdExp]
    by_cases hd0 : 1 ≤ d
    · have hiff := hmem d hd0
      by_cases h1 : m₁ ∈ fibreIco A B d
      · by_cases h2 : m₂ ∈ fibreIco A B d
        · have := hiff.1 ⟨h1, h2⟩
          rw [fibreIco, Finset.mem_Ico] at this
          rw [if_pos h1, if_pos h2, if_pos]
          simp only [Finset.mem_Ico, le_max_iff, max_le_iff, lt_min_iff, min_lt_iff]
          exact ⟨⟨hd.1, this.1.1, this.2.1⟩, hd.2, this.1.2, this.2.2⟩
        · rw [if_pos h1, if_neg h2, if_neg]
          · simp
          · intro hcon
            simp only [Finset.mem_Ico, le_max_iff, max_le_iff, lt_min_iff, min_lt_iff] at hcon
            refine h2 (hiff.2 ⟨?_, ?_⟩).2
            · rw [fibreIco, Finset.mem_Ico]
              exact ⟨hcon.1.2.1, hcon.2.2.1⟩
            · rw [fibreIco, Finset.mem_Ico]
              exact ⟨hcon.1.2.2, hcon.2.2.2⟩
      · rw [if_neg h1, if_neg]
        · simp
        · intro hcon
          simp only [Finset.mem_Ico, le_max_iff, max_le_iff, lt_min_iff, min_lt_iff] at hcon
          refine h1 (hiff.2 ⟨?_, ?_⟩).1
          · rw [fibreIco, Finset.mem_Ico]
            exact ⟨hcon.1.2.1, hcon.2.2.1⟩
          · rw [fibreIco, Finset.mem_Ico]
            exact ⟨hcon.1.2.2, hcon.2.2.2⟩
    · have hd0' : d = 0 := by omega
      subst hd0'
      have hempty : (0 : ℕ) ∉ fibreIco A B m₁ ∨ True := Or.inr trivial
      have h1 : m₁ ∉ fibreIco A B 0 := by
        rw [fibreIco, Finset.mem_Ico]
        simp only [Nat.div_zero]
        omega
      rw [if_neg h1, if_neg]
      · simp
      · simp only [Finset.mem_Ico, le_max_iff, max_le_iff, lt_min_iff, min_lt_iff]
        rintro ⟨⟨-, h, -⟩, -⟩
        omega
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun d _ => rfl
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ico, le_max_iff, max_le_iff, lt_min_iff, min_lt_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩
    exact ⟨⟨h3, h4⟩, h5, h6⟩
  · rintro ⟨⟨h3, h4⟩, h5, h6⟩
    exact ⟨⟨h3, h5.1⟩, ⟨h3, h4⟩, h5, h6⟩

end

end RHTower.Sieve
