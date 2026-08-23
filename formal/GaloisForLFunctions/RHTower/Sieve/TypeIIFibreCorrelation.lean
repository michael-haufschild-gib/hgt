import GaloisForLFunctions.RHTower.Sieve.TypeIIEnergyBound
import GaloisForLFunctions.RHTower.Sieve.DivisorFibreInterval

/-!
# The type-II correlation over a coupled block

In the type-II half the two variables are coupled by `d·m ∈ I`, so the inner range depends on the
outer index.  Masking the summand with the fibre indicator restores the product structure the
correlation expansion needs, and — because `d·m ∈ I` is symmetric — the correlation attached to a
pair `(m₁, m₂)` runs over the INTERSECTION of two fibre intervals, which is again an interval.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- The fibre interval of a block. -/
def fibreIco (A B b : ℕ) : Finset ℕ := Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1)

/-- The fibre relation is symmetric. -/
theorem mem_fibre_symm {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    m ∈ fibreIco A B d ↔ d ∈ fibreIco A B m := by
  rw [fibreIco, fibreIco, ← mem_fibre_iff hd hA hB m, ← mem_fibre_iff hm hA hB d, Nat.mul_comm]

/-- The type-II summand, masked by the block constraint. -/
def maskedNdExp (T r : ℝ) (A B : ℕ) (d m : ℕ) : ℂ :=
  if m ∈ fibreIco A B d then ndExp T r m d else 0

/-- The masked inner sum is the constrained inner sum. -/
theorem sum_maskedNdExp_eq (T r : ℝ) (A B : ℕ) (d : ℕ) (Ms : Finset ℕ) (b : ℕ → ℂ) :
    (∑ m ∈ Ms, b m * maskedNdExp T r A B d m)
      = ∑ m ∈ Ms.filter (fun m => m ∈ fibreIco A B d), b m * ndExp T r m d := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [maskedNdExp]
  split_ifs <;> simp

/-- **The masked correlation runs over an interval.** -/
theorem sum_masked_correlation_eq {A B P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P)
    (T r : ℝ) {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) :
    (∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂))
      = ∑ d ∈ Finset.Ico (max P (max ((A - 1) / m₁ + 1) ((A - 1) / m₂ + 1)))
            (min Q (min ((B - 1) / m₁ + 1) ((B - 1) / m₂ + 1))),
          ndExp T r m₁ d * (starRingEnd ℂ) (ndExp T r m₂ d) := by
  classical
  have hstep : (∑ d ∈ Finset.Ico P Q,
      maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂))
      = ∑ d ∈ (Finset.Ico P Q).filter (fun d => m₁ ∈ fibreIco A B d ∧ m₂ ∈ fibreIco A B d),
          ndExp T r m₁ d * (starRingEnd ℂ) (ndExp T r m₂ d) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [maskedNdExp, maskedNdExp]
    by_cases h1 : m₁ ∈ fibreIco A B d <;> by_cases h2 : m₂ ∈ fibreIco A B d <;> simp [h1, h2]
  rw [hstep]
  refine Finset.sum_congr ?_ fun d _ => rfl
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ico, max_le_iff, lt_min_iff]
  constructor
  · rintro ⟨⟨hPd, hdQ⟩, h1, h2⟩
    have hd1 : 1 ≤ d := le_trans hP hPd
    have e1 := (mem_fibre_symm hA hB hd1 hm₁).1 h1
    have e2 := (mem_fibre_symm hA hB hd1 hm₂).1 h2
    rw [fibreIco, Finset.mem_Ico] at e1 e2
    exact ⟨⟨hPd, e1.1, e2.1⟩, hdQ, e1.2, e2.2⟩
  · rintro ⟨⟨hPd, hA1, hA2⟩, hdQ, hB1, hB2⟩
    have hd1 : 1 ≤ d := le_trans hP hPd
    refine ⟨⟨hPd, hdQ⟩, ?_, ?_⟩
    · exact (mem_fibre_symm hA hB hd1 hm₁).2 (by rw [fibreIco, Finset.mem_Ico]; exact ⟨hA1, hB1⟩)
    · exact (mem_fibre_symm hA hB hd1 hm₂).2 (by rw [fibreIco, Finset.mem_Ico]; exact ⟨hA2, hB2⟩)

end

end RHTower.Sieve
