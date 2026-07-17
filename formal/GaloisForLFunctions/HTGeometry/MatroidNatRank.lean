import GaloisForLFunctions.HTGeometry.DifferentialMatroidGluing
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# Natural rank of a matroid on finite sets

Every matroid has a finite natural-valued rank on finite subsets.  This file packages that rank as
the `MatroidGluing.Rank` used by the orbit-gluing engine and identifies its `IndepSet` predicate
with ordinary matroid independence for finitary matroids.
-/

namespace GaloisForLFunctions.MatroidGluing

open Matroid

variable {Ω : Type*} [DecidableEq Ω]

omit [DecidableEq Ω] in
/-- A finite set has finite extended matroid rank. -/
theorem matroid_eRk_ne_top (M : Matroid Ω) (s : Finset Ω) :
    M.eRk (↑s : Set Ω) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (M.eRk_le_encard (↑s : Set Ω))
  simp

/-- The natural-valued rank of a matroid on finite subsets. -/
noncomputable def matroidRank (M : Matroid Ω) : Rank Ω where
  ρ s := (M.eRk (↑s : Set Ω)).toNat
  mono := by
    intro s t h
    refine ENat.toNat_le_toNat (M.eRk_mono ?_) (matroid_eRk_ne_top M t)
    exact_mod_cast Finset.coe_subset.mpr h
  submodular := by
    intro s t
    have hsub := M.eRk_submod (↑s : Set Ω) (↑t : Set Ω)
    rw [← Finset.coe_union, ← Finset.coe_inter] at hsub
    have hu : M.eRk (↑(s ∪ t) : Set Ω) ≠ ⊤ := matroid_eRk_ne_top M (s ∪ t)
    have hi : M.eRk (↑(s ∩ t) : Set Ω) ≠ ⊤ := matroid_eRk_ne_top M (s ∩ t)
    have hs : M.eRk (↑s : Set Ω) ≠ ⊤ := matroid_eRk_ne_top M s
    have ht : M.eRk (↑t : Set Ω) ≠ ⊤ := matroid_eRk_ne_top M t
    have key := ENat.toNat_le_toNat hsub ((WithTop.add_ne_top).mpr ⟨hs, ht⟩)
    rwa [ENat.toNat_add hi hu, ENat.toNat_add hs ht,
      Nat.add_comm (M.eRk (↑(s ∩ t) : Set Ω)).toNat] at key
  ρ_le_card := by
    intro s
    have h := M.eRk_le_encard (↑s : Set Ω)
    rw [Set.encard_coe_eq_coe_finsetCard] at h
    exact ENat.toNat_le_toNat h (by simp)

@[simp]
theorem matroidRank_rho (M : Matroid Ω) (s : Finset Ω) :
    (matroidRank M).ρ s = (M.eRk (↑s : Set Ω)).toNat := rfl

/-- Full natural rank on a finite set is equivalent to matroid independence. -/
theorem matroidRank_rho_eq_card_iff (M : Matroid Ω) (s : Finset Ω) :
    (matroidRank M).ρ s = s.card ↔ M.Indep (↑s : Set Ω) := by
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite (by simp), matroidRank_rho,
    Set.encard_coe_eq_coe_finsetCard]
  constructor
  · intro h
    calc
      M.eRk (↑s : Set Ω) = ((M.eRk (↑s : Set Ω)).toNat : ℕ∞) :=
        (ENat.coe_toNat (matroid_eRk_ne_top M s)).symm
      _ = (s.card : ℕ∞) := by exact_mod_cast h
  · intro h
    simpa using congrArg ENat.toNat h

/-- For a finitary matroid, the gluing engine's independence predicate is exactly matroid
independence, including for infinite coordinate sets. -/
theorem matroidRank_indepSet_iff (M : Matroid Ω) [M.Finitary] (S : Set Ω) :
    (matroidRank M).IndepSet S ↔ M.Indep S := by
  constructor
  · intro h
    rw [Matroid.indep_iff_forall_finite_subset_indep]
    intro J hJS hJfin
    let t := hJfin.toFinset
    have ht : (↑t : Set Ω) ⊆ S := by simpa [t] using hJS
    have hr := h t ht
    rw [matroidRank_rho_eq_card_iff] at hr
    simpa [t] using hr
  · intro h t ht
    rw [matroidRank_rho_eq_card_iff]
    exact h.subset ht

end GaloisForLFunctions.MatroidGluing
