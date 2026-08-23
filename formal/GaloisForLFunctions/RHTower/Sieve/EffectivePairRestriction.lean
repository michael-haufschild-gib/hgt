import GaloisForLFunctions.RHTower.Sieve.OffDiagonalTotal

/-!
# Restricting the type-II pair sum to the effective short range

Outside the effective range the masked correlation vanishes identically, so the pair sum may be
restricted to the effective set — which is confined to an interval of length `≍ M/D`, exactly what
the off-diagonal total needs.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The effective short values of a block. -/
def effShort (A B P Q : ℕ) : ℕ → Prop :=
  fun m => ¬ ((B - 1) / m + 1 ≤ P) ∧ ¬ (Q ≤ (A - 1) / m + 1)

instance effShortDecidable (A B P Q m : ℕ) : Decidable (effShort A B P Q m) := by
  unfold effShort
  infer_instance

/-- The effective set. -/
def effSet (A B P Q L : ℕ) : Finset ℕ := (Finset.Icc 1 L).filter (effShort A B P Q)

theorem effSet_subset (A B P Q L : ℕ) : effSet A B P Q L ⊆ Finset.Icc 1 L :=
  Finset.filter_subset _ _

/-- Members of the effective set lie in the fibre interval. -/
theorem effSet_mem_Ico {A B P Q L m : ℕ} (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hm : m ∈ effSet A B P Q L) :
    m ∈ Finset.Ico ((A - 1) / (Q - 1) + 1) ((B - 1) / P + 1) := by
  rw [effSet, Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨hm1, -⟩, h1, h2⟩ := hm
  exact effective_short_range hm1 hP hQ h1 h2

/-- The correlation vanishes off the effective set. -/
theorem correlation_eq_zero_of_not_effShort {A B P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P)
    (T r : ℝ) {m₁ : ℕ} (hm₁ : 1 ≤ m₁) (m₂ : ℕ) (hm₂ : 1 ≤ m₂)
    (hnot : ¬ effShort A B P Q m₁) :
    (∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)) = 0 := by
  rw [effShort] at hnot
  by_cases h1 : (B - 1) / m₁ + 1 ≤ P
  · exact masked_correlation_eq_zero_of_large hA hB hP T r hm₁ hm₂ h1
  · have h2 : Q ≤ (A - 1) / m₁ + 1 := by tauto
    exact masked_correlation_eq_zero_of_small hA hB hP T r hm₁ hm₂ h2

/-- **The pair sum restricts to the effective set.** -/
theorem pair_sum_restrict_eff {A B P Q L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P)
    (T r : ℝ) (b : ℕ → ℝ) :
    (∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
        |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
          maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖)
      = ∑ m₁ ∈ effSet A B P Q L, ∑ m₂ ∈ effSet A B P Q L,
          |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
            maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖ := by
  classical
  have hzero₁ : ∀ m₁ ∈ Finset.Icc 1 L, m₁ ∉ effSet A B P Q L →
      (∑ m₂ ∈ Finset.Icc 1 L, |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖) = 0 := by
    intro m₁ hm₁ hnot
    rw [Finset.mem_Icc] at hm₁
    have hnoteff : ¬ effShort A B P Q m₁ := by
      intro hcon
      exact hnot (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hm₁, hcon⟩)
    refine Finset.sum_eq_zero fun m₂ hm₂ => ?_
    rw [Finset.mem_Icc] at hm₂
    rw [correlation_eq_zero_of_not_effShort hA hB hP T r hm₁.1 m₂ hm₂.1 hnoteff]
    simp
  have hzero₂ : ∀ m₁ : ℕ, ∀ m₂ ∈ Finset.Icc 1 L, m₂ ∉ effSet A B P Q L → 1 ≤ m₁ →
      |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖ = 0 := by
    intro m₁ m₂ hm₂ hnot hm₁
    rw [Finset.mem_Icc] at hm₂
    have hnoteff : ¬ effShort A B P Q m₂ := by
      intro hcon
      exact hnot (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hm₂, hcon⟩)
    rw [sum_masked_correlation_conj,
      correlation_eq_zero_of_not_effShort hA hB hP T r hm₂.1 m₁ hm₁ hnoteff]
    simp
  rw [← Finset.sum_subset (effSet_subset A B P Q L) hzero₁]
  refine Finset.sum_congr rfl fun m₁ hm₁ => ?_
  have hm₁1 : 1 ≤ m₁ := by
    have := effSet_subset A B P Q L hm₁
    rw [Finset.mem_Icc] at this
    exact this.1
  exact (Finset.sum_subset (effSet_subset A B P Q L)
    (fun m₂ hm₂ hnot => hzero₂ m₁ m₂ hm₂ hnot hm₁1)).symm

end

end RHTower.Sieve
