import Mathlib

/-!
# Restricting a family to its nonzero coefficients

A finite family with some vanishing coefficients has the same sum as the subfamily of its nonzero
ones, reindexed by a `Fin`.  This is the bookkeeping that lets residue theorems — which need every
coefficient of a family to be nonzero — be applied to a presentation that makes no such promise.
-/

open Finset

namespace GaloisForLFunctions

/-- **The nonzero subfamily.**  Terms whose coefficient vanishes contribute nothing, so the sum is a
sum over an injectively reindexed family all of whose coefficients are nonzero. -/
theorem exists_reindex_support {M : ℕ} {A : Type*} [AddCommMonoid A] (a : Fin M → ℂ)
    (g : Fin M → A) (hg : ∀ α, a α = 0 → g α = 0) :
    ∃ (M' : ℕ) (ι : Fin M' → Fin M), Function.Injective ι ∧ (∀ j, a (ι j) ≠ 0) ∧
      ∑ α : Fin M, g α = ∑ j : Fin M', g (ι j) := by
  classical
  refine ⟨(univ.filter (fun α => a α ≠ 0)).card,
    fun j => (((univ.filter (fun α => a α ≠ 0)).equivFin.symm j : {x // x ∈ _}) : Fin M),
    ?_, ?_, ?_⟩
  · intro j k hjk
    have h : (univ.filter (fun α => a α ≠ 0)).equivFin.symm j
        = (univ.filter (fun α => a α ≠ 0)).equivFin.symm k := Subtype.ext hjk
    exact (univ.filter (fun α => a α ≠ 0)).equivFin.symm.injective h
  · intro j
    exact (Finset.mem_filter.mp ((univ.filter (fun α => a α ≠ 0)).equivFin.symm j).2).2
  · have h1 : ∑ α ∈ univ.filter (fun α => a α ≠ 0), g α = ∑ α : Fin M, g α := by
      refine Finset.sum_subset (Finset.subset_univ _) fun α _ hα => hg α ?_
      by_contra h
      exact hα (Finset.mem_filter.mpr ⟨Finset.mem_univ α, h⟩)
    have h2 : ∑ j : Fin (univ.filter (fun α => a α ≠ 0)).card,
        g (((univ.filter (fun α => a α ≠ 0)).equivFin.symm j : Fin M))
        = ∑ α ∈ univ.filter (fun α => a α ≠ 0), g α := by
      rw [← Finset.sum_attach (univ.filter (fun α => a α ≠ 0)) g]
      exact Fintype.sum_equiv (univ.filter (fun α => a α ≠ 0)).equivFin.symm _ _ fun j => rfl
    rw [← h1, ← h2]

/-- **A `Fin`-indexed reindexing of a `Finset`-indexed sum.** -/
theorem exists_fin_reindex_of_finset {M : ℕ} {A : Type*} [AddCommMonoid A] (S : Finset (Fin M))
    (g : Fin M → A) :
    ∃ (M' : ℕ) (ι : Fin M' → Fin M), Function.Injective ι ∧ (∀ j, ι j ∈ S)
      ∧ (∀ α ∈ S, ∃ j, ι j = α)
      ∧ ∑ α ∈ S, g α = ∑ j : Fin M', g (ι j) := by
  classical
  refine ⟨S.card, fun j => ((S.equivFin.symm j : {x // x ∈ S}) : Fin M), ?_, ?_, ?_, ?_⟩
  · intro j k hjk
    exact S.equivFin.symm.injective (Subtype.ext hjk)
  · intro j
    exact (S.equivFin.symm j).2
  · intro α hα
    refine ⟨S.equivFin ⟨α, hα⟩, ?_⟩
    show ((S.equivFin.symm (S.equivFin ⟨α, hα⟩) : {x // x ∈ S}) : Fin M) = α
    rw [Equiv.symm_apply_apply]
  · rw [← Finset.sum_attach S g]
    exact (Fintype.sum_equiv S.equivFin.symm _ _ fun j => rfl).symm

end GaloisForLFunctions
