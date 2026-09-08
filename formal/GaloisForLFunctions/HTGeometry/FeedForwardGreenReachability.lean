import GaloisForLFunctions.HTGeometry.FeedForwardFisherProjector
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Actual Green-column reachability in feed-forward chains

The adjacent-column elimination behind Theorem S4 of arXiv:2609.04996.
Nested geometric Green columns span exactly the disjoint interval fields;
the reachable dimension equals the number of local ports. All propagation
factors are complex, and zero hopping is included.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry


/-- Position of a port in a chain partitioned into nonempty intervals. -/
def feedForwardPortStart (n : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range j, (n k + 1)

theorem feedForwardPortStart_succ (n : ℕ → ℕ) (j : ℕ) :
    feedForwardPortStart n (j + 1) = feedForwardPortStart n j + (n j + 1) := by
  exact Finset.sum_range_succ _ _

theorem feedForwardPortStart_monotone (n : ℕ → ℕ) : Monotone (feedForwardPortStart n) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
  intro k _ _
  exact Nat.zero_le _

/-- Full downstream Green column, with arbitrary complex propagation factor. -/
def feedForwardGreenColumn {m : ℕ} (q : ℂ) (n : ℕ → ℕ) (j : ℕ) :
    (Σ i : Fin m, Fin (n i.val + 1)) → ℂ := fun s =>
  if j ≤ s.1.val then q ^ (feedForwardPortStart n s.1.val + s.2.val -
    feedForwardPortStart n j) else 0

/-- Field supported on exactly one port interval. -/
def feedForwardRawInterval {m : ℕ} (q : ℂ) (n : ℕ → ℕ) (j : ℕ) :
    (Σ i : Fin m, Fin (n i.val + 1)) → ℂ := fun s =>
  if j = s.1.val then q ^ s.2.val else 0

/-- Adjacent-column elimination removes every downstream tail, including at zero hopping. -/
theorem feedForwardGreenColumn_elimination {m : ℕ} (q : ℂ) (n : ℕ → ℕ) (j : ℕ) :
    feedForwardGreenColumn (m := m) q n j -
      q ^ (n j + 1) • feedForwardGreenColumn q n (j + 1) =
        feedForwardRawInterval q n j := by
  funext s
  change (if j ≤ s.1.val then _ else 0) -
    q ^ (n j + 1) * (if j + 1 ≤ s.1.val then _ else 0) =
      (if j = s.1.val then _ else 0)
  by_cases hlt : s.1.val < j
  · simp [show ¬ j ≤ s.1.val by omega, show ¬ j + 1 ≤ s.1.val by omega,
      show j ≠ s.1.val by omega]
  by_cases heq : j = s.1.val
  · subst j
    simp
  have hle : j + 1 ≤ s.1.val := by omega
  have hp := feedForwardPortStart_monotone n hle
  rw [feedForwardPortStart_succ] at hp
  have hexp : feedForwardPortStart n s.1.val + s.2.val - feedForwardPortStart n j =
      n j + 1 + (feedForwardPortStart n s.1.val + s.2.val -
        feedForwardPortStart n (j + 1)) := by
    rw [feedForwardPortStart_succ]
    omega
  simp only [if_pos (show j ≤ s.1.val by omega), if_pos hle, if_neg heq, hexp,
    pow_add, sub_self]

/-- Exact expansion of a nested Green column in disjoint interval fields. -/
theorem feedForwardGreenColumn_decomposition {m : ℕ} (q : ℂ) (n : ℕ → ℕ) (j : ℕ) :
    feedForwardGreenColumn (m := m) q n j =
      ∑ k : Fin m, (if j ≤ k.val then
        q ^ (feedForwardPortStart n k.val - feedForwardPortStart n j) else 0) •
          feedForwardRawInterval q n k.val := by
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single s.1]
  · simp only [feedForwardGreenColumn, feedForwardRawInterval, if_true]
    by_cases h : j ≤ s.1.val
    · have hp := feedForwardPortStart_monotone n h
      have he : feedForwardPortStart n s.1.val + s.2.val - feedForwardPortStart n j =
          (feedForwardPortStart n s.1.val - feedForwardPortStart n j) + s.2.val := by omega
      simp [h, he, pow_add]
    · simp [h]
  · intro k _ hk
    have hne : k.val ≠ s.1.val := fun h => hk (Fin.ext h)
    simp [feedForwardRawInterval, hne]
  · simp

/-- Every port beyond the finite chain has zero Green column. -/
theorem feedForwardGreenColumn_pastEnd {m : ℕ} (q : ℂ) (n : ℕ → ℕ) (j : ℕ) :
    feedForwardGreenColumn (m := m) q n (m + j) = 0 := by
  funext s
  have hi := s.1.isLt
  simp [feedForwardGreenColumn, show ¬m + j ≤ s.1.val by omega]

theorem feedForwardGreenColumn_mem_span {m : ℕ} (q : ℂ) (n : ℕ → ℕ) (j : ℕ) :
    feedForwardGreenColumn (m := m) q n j ∈
      Submodule.span ℂ (Set.range fun k : Fin m => feedForwardGreenColumn (m := m) q n k.val) := by
  by_cases h : j < m
  · exact Submodule.subset_span ⟨⟨j, h⟩, rfl⟩
  · have hj : j = m + (j - m) := by omega
    rw [hj, feedForwardGreenColumn_pastEnd]
    exact Submodule.zero_mem _

/-- The actual local-port reachable space equals the disjoint-interval space in (S85). -/
theorem feedForwardGreenColumn_span {m : ℕ} (q : ℂ) (n : ℕ → ℕ) :
    Submodule.span ℂ (Set.range fun k : Fin m => feedForwardGreenColumn (m := m) q n k.val) =
      Submodule.span ℂ (Set.range fun k : Fin m => feedForwardRawInterval (m := m) q n k.val) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change feedForwardGreenColumn (m := m) q n j.val ∈ _
    rw [feedForwardGreenColumn_decomposition]
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change feedForwardRawInterval (m := m) q n j.val ∈ _
    rw [← feedForwardGreenColumn_elimination]
    exact Submodule.sub_mem _ (feedForwardGreenColumn_mem_span q n j.val)
      (Submodule.smul_mem _ _ (feedForwardGreenColumn_mem_span q n (j.val + 1)))

/-- Sampling interval starts recovers all disjoint-field coefficients exactly. -/
theorem feedForwardRawInterval_coefficient {m : ℕ} (q : ℂ) (n : ℕ → ℕ)
    (c : Fin m → ℂ) (j : Fin m) :
    (∑ k : Fin m, c k • feedForwardRawInterval q n k.val) ⟨j, 0⟩ = c j := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, feedForwardRawInterval,
    Fin.val_zero, pow_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [show k.val ≠ j.val from fun h => hk (Fin.ext h)]
  · simp

/-- Distinct local ports contribute independent reachable directions for every propagation factor. -/
theorem feedForwardRawInterval_linearIndependent {m : ℕ} (q : ℂ) (n : ℕ → ℕ) :
    LinearIndependent ℂ (fun j : Fin m => feedForwardRawInterval (m := m) q n j.val) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have he := congrFun hc ⟨j, 0⟩
  simpa only [feedForwardRawInterval_coefficient, Pi.zero_apply] using he


/-- Reachable dimension is exactly the number of ports, independent of hopping and interval lengths. -/
theorem feedForwardGreenColumn_finrank {m : ℕ} (q : ℂ) (n : ℕ → ℕ) :
    Module.finrank ℂ (Submodule.span ℂ
      (Set.range fun j : Fin m => feedForwardGreenColumn (m := m) q n j.val)) = m := by
  rw [feedForwardGreenColumn_span]
  simpa only [Fintype.card_fin] using
    finrank_span_eq_card (feedForwardRawInterval_linearIndependent (m := m) q n)

/-- Every local Green column is indispensable: the actual port responses are linearly independent. -/
theorem feedForwardGreenColumn_linearIndependent {m : ℕ} (q : ℂ) (n : ℕ → ℕ) :
    LinearIndependent ℂ (fun j : Fin m => feedForwardGreenColumn (m := m) q n j.val) := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  change m = Module.finrank ℂ (Submodule.span ℂ
    (Set.range fun j : Fin m => feedForwardGreenColumn (m := m) q n j.val))
  exact (feedForwardGreenColumn_finrank q n).symm

end GaloisForLFunctions.HTGeometry
