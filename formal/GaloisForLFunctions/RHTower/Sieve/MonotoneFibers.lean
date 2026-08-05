import Mathlib

/-!
# Fibres of a monotone classification are intervals

Splitting a sum over `range N` by the fibres of a monotone integer-valued classification
costs the number of distinct values, and each fibre is an integer interval.  This is the
combinatorial skeleton of the derivative tests: the classification is the band-or-gap index
of a monotone derivative, its fibres are the maximal runs, and the number of values is
controlled by the derivative's total variation.
-/

namespace RHTower.Sieve

/-- A sum splits over the fibres of any classification. -/
theorem sum_eq_sum_image_fibers (f : ℕ → ℂ) (K : ℕ → ℤ) (N : ℕ) :
    ∑ n ∈ Finset.range N, f n
      = ∑ v ∈ (Finset.range N).image K,
          ∑ n ∈ (Finset.range N).filter (fun n => K n = v), f n := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (fun n hn => Finset.mem_image_of_mem K hn) f).symm

/-- The fibre split, in norm. -/
theorem norm_sum_le_sum_image_fibers (f : ℕ → ℂ) (K : ℕ → ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, f n‖
      ≤ ∑ v ∈ (Finset.range N).image K,
          ‖∑ n ∈ (Finset.range N).filter (fun n => K n = v), f n‖ := by
  rw [sum_eq_sum_image_fibers f K N]
  exact norm_sum_le _ _

/-- **Fibres of a monotone classification are integer intervals.** -/
theorem filter_eq_Ico_of_monotone {K : ℕ → ℤ} {N : ℕ}
    (hK : ∀ a b : ℕ, a ≤ b → b < N → K a ≤ K b) (v : ℤ) :
    ∃ l u : ℕ, (Finset.range N).filter (fun n => K n = v) = Finset.Ico l u := by
  classical
  rcases Finset.eq_empty_or_nonempty
    ((Finset.range N).filter (fun n => K n = v)) with he | hne
  · exact ⟨0, 0, by rw [he]; simp⟩
  · refine ⟨((Finset.range N).filter (fun n => K n = v)).min' hne,
      ((Finset.range N).filter (fun n => K n = v)).max' hne + 1, ?_⟩
    have hminmem := ((Finset.range N).filter (fun n => K n = v)).min'_mem hne
    have hmaxmem := ((Finset.range N).filter (fun n => K n = v)).max'_mem hne
    rw [Finset.mem_filter, Finset.mem_range] at hminmem hmaxmem
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro hn
      have hmem : n ∈ (Finset.range N).filter (fun n => K n = v) := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact hn
      exact ⟨Finset.min'_le _ n hmem,
        Nat.lt_succ_of_le (Finset.le_max' _ n hmem)⟩
    · intro hn
      have hle1 : K (((Finset.range N).filter (fun n => K n = v)).min' hne) ≤ K n :=
        hK _ n hn.1 (by omega)
      have hle2 : K n ≤ K (((Finset.range N).filter (fun n => K n = v)).max' hne) :=
        hK n _ (by omega) hmaxmem.1
      rw [hminmem.2] at hle1
      rw [hmaxmem.2] at hle2
      exact ⟨by omega, le_antisymm hle2 hle1⟩

/-- **The number of values of a monotone classification.** -/
theorem card_image_le_of_monotone {K : ℕ → ℤ} {N : ℕ} (hN : 1 ≤ N)
    (hK : ∀ a b : ℕ, a ≤ b → b < N → K a ≤ K b) :
    (((Finset.range N).image K).card : ℝ)
      ≤ ((K (N - 1) - K 0 : ℤ) : ℝ) + 1 := by
  classical
  have hsub : (Finset.range N).image K ⊆ Finset.Icc (K 0) (K (N - 1)) := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    have hnN := Finset.mem_range.mp hn
    simp only [Finset.mem_Icc]
    exact ⟨hK 0 n (Nat.zero_le n) hnN, hK n (N - 1) (by omega) (by omega)⟩
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hmono0 : K 0 ≤ K (N - 1) := hK 0 (N - 1) (Nat.zero_le _) (by omega)
  have hnn : (0 : ℤ) ≤ K (N - 1) + 1 - K 0 := by omega
  have hcast : (((K (N - 1) + 1 - K 0).toNat : ℕ) : ℝ)
      = ((K (N - 1) - K 0 : ℤ) : ℝ) + 1 := by
    have h := Int.toNat_of_nonneg hnn
    have h' : (((K (N - 1) + 1 - K 0).toNat : ℕ) : ℝ)
        = ((K (N - 1) + 1 - K 0 : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
    rw [h']
    push_cast
    ring
  calc (((Finset.range N).image K).card : ℝ)
      ≤ (((K (N - 1) + 1 - K 0).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((K (N - 1) - K 0 : ℤ) : ℝ) + 1 := hcast

end RHTower.Sieve
