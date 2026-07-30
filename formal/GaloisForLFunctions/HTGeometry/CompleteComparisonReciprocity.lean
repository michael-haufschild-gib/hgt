import GaloisForLFunctions.HTGeometry.HochsterCycleRealization
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Complete-comparison reciprocity rigidity

For `n` raw accounts with every unordered pair directly comparable, the complete comparison layer
has `n.choose 2` channels.  Quotienting the common account mode leaves `n - 1` independent account
modes, so the comparison disagreement count is

`n.choose 2 - (n - 1) = (n - 1).choose 2`.

Requiring exactly one disagreement forces `n = 3`.  The resulting empty triangle has comparison
rank `2`, cochain rank `3`, and first-cohomology rank `1`.  This is the finite mathematical content
of the complete-comparison fact--disagreement bridge; it carries no physical interpretation by
itself.
-/

namespace GaloisForLFunctions.HTGeometry

open SimpleGraph

noncomputable section

/-- Number of unordered pairwise channels among `n` raw accounts. -/
def completeComparisonChannels (n : ℕ) : ℕ := n.choose 2

/-- Number of account modes left after quotienting the common constant mode. -/
def independentAccountModes (n : ℕ) : ℕ := n - 1

/-- Excess pairwise channels over independent account modes. -/
def completeComparisonDisagreements (n : ℕ) : ℕ :=
  completeComparisonChannels n - independentAccountModes n

/-- The cochain space on the edges of the complete graph has rank `n.choose 2`. -/
theorem finrank_completeComparisonEdgeCochains (n : ℕ) (F : Type*) [Field F] :
    Module.finrank F (((⊤ : SimpleGraph (Fin n)).edgeFinset) → F) = n.choose 2 := by
  rw [Module.finrank_pi, Fintype.card_coe, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin]

/-- Pairwise-complete disagreement is the second binomial coefficient of the reduced account
count. -/
theorem completeComparisonDisagreements_eq_choose_pred (n : ℕ) :
    completeComparisonDisagreements n = (n - 1).choose 2 := by
  cases n with
  | zero => rfl
  | succ n =>
      simp [completeComparisonDisagreements, completeComparisonChannels,
        independentAccountModes, Nat.choose_succ_succ, Nat.choose_one_right]

/-- **Complete-comparison reciprocity rigidity.** Exactly one independent disagreement occurs
precisely for three raw accounts. -/
theorem completeComparisonDisagreements_eq_one_iff (n : ℕ) :
    completeComparisonDisagreements n = 1 ↔ n = 3 := by
  rw [completeComparisonDisagreements_eq_choose_pred, Nat.choose_eq_one_iff]
  omega

/-- One-disagreement rigidity simultaneously yields three comparison channels, two independent
account modes, and the no-residual equality `3 = 2 + 1`. -/
theorem completeComparison_one_disagreement_dimensions {n : ℕ}
    (h : completeComparisonDisagreements n = 1) :
    n = 3 ∧ completeComparisonChannels n = 3 ∧
      independentAccountModes n = 2 ∧
      completeComparisonChannels n = independentAccountModes n + 1 := by
  have hn := (completeComparisonDisagreements_eq_one_iff n).mp h
  subst n
  norm_num [completeComparisonChannels, independentAccountModes, Nat.choose]

/-- The oriented coboundary of the selected empty triangle has rank two. -/
theorem finrank_triangle_orientedCoboundary_range (F : Type*) [Field F] :
    Module.finrank F
        (LinearMap.range (orientedCoboundary (cycleGraph 3) F)) = 2 := by
  rw [finrank_orientedCoboundary_range,
    card_connectedComponent_eq_one (cycleGraph 3) cycleGraph_connected,
    Fintype.card_fin]

/-- The selected empty triangle has three comparison cochains.  This is derived from rank two of
the coboundary and rank one of its quotient, rather than by enumerating edges. -/
theorem finrank_triangle_comparisonCochains (F : Type*) [Field F] :
    Module.finrank F (orientedEdges (cycleGraph 3) → F) = 3 := by
  have hq := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (orientedCoboundary (cycleGraph 3) F))
  rw [finrank_reducedH1_cycleGraph3,
    finrank_triangle_orientedCoboundary_range] at hq
  omega

/-- **Exact `2 → 3 → 1` triangle witness dimensions.**  The reduced account image has rank two,
the comparison space rank three, and the irreducible loop-disagreement quotient rank one. -/
theorem triangle_witness_dimensions (F : Type*) [Field F] :
    Module.finrank F
        (LinearMap.range (orientedCoboundary (cycleGraph 3) F)) = 2
      ∧ Module.finrank F (orientedEdges (cycleGraph 3) → F) = 3
      ∧ Module.finrank F
          ((orientedEdges (cycleGraph 3) → F)
            ⧸ LinearMap.range (orientedCoboundary (cycleGraph 3) F)) = 1 := by
  exact ⟨finrank_triangle_orientedCoboundary_range F,
    finrank_triangle_comparisonCochains F,
    finrank_reducedH1_cycleGraph3 F⟩

end

end GaloisForLFunctions.HTGeometry
