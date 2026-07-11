import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Combinatorics.Matroid.Rank.Finite
import Mathlib.Combinatorics.Matroid.Rank.Cardinal
import GaloisForLFunctions.DifferentialMatroidGluing

/-!
# The transcendence-degree rank is a `Rank`

`mathlib`'s algebraic matroid `matroid R A` has independent sets the algebraically independent
subsets of `A`, and its cardinal rank is the transcendence degree.  Its finite rank function `eRk`
is monotone, submodular and bounded by cardinality — exactly the axioms of the abstract
`GaloisForLFunctions.MatroidGluing.Rank`.  This file packages it, giving a concrete instance of the
rank abstraction that drives the differential-matroid gluing engine: transcendence degree over a
fixed base field really is such a rank, so the abstraction is not vacuous.
-/

namespace GaloisForLFunctions.MatroidGluing

open Matroid

variable (R A : Type*) [CommRing R] [Field A] [Algebra R A] [FaithfulSMul R A] [DecidableEq A]

omit [DecidableEq A] in
/-- Finite sets have finite matroid rank. -/
theorem algMatroid_eRk_ne_top (s : Finset A) :
    (AlgebraicIndependent.matroid R A).eRk (↑s : Set A) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ ((AlgebraicIndependent.matroid R A).eRk_le_encard (↑s : Set A))
  simp

/-- Transcendence degree over `R`, as a rank on finite subsets of the field `A`:
`ρ(s)` is the matroid rank (= transcendence degree) of `s`.  Monotone, submodular, subcardinal. -/
noncomputable def transcendenceRank : Rank A where
  ρ s := ((AlgebraicIndependent.matroid R A).eRk (↑s : Set A)).toNat
  mono := by
    intro s t h
    refine ENat.toNat_le_toNat ((AlgebraicIndependent.matroid R A).eRk_mono ?_) (algMatroid_eRk_ne_top R A t)
    exact_mod_cast Finset.coe_subset.mpr h
  submodular := by
    intro s t
    have hsub := (AlgebraicIndependent.matroid R A).eRk_submod (↑s : Set A) (↑t : Set A)
    rw [← Finset.coe_union, ← Finset.coe_inter] at hsub
    -- take `toNat` of the submodular inequality; every term is finite
    have hu : (AlgebraicIndependent.matroid R A).eRk (↑(s ∪ t) : Set A) ≠ ⊤ := algMatroid_eRk_ne_top R A (s ∪ t)
    have hi : (AlgebraicIndependent.matroid R A).eRk (↑(s ∩ t) : Set A) ≠ ⊤ := algMatroid_eRk_ne_top R A (s ∩ t)
    have hs : (AlgebraicIndependent.matroid R A).eRk (↑s : Set A) ≠ ⊤ := algMatroid_eRk_ne_top R A s
    have ht : (AlgebraicIndependent.matroid R A).eRk (↑t : Set A) ≠ ⊤ := algMatroid_eRk_ne_top R A t
    -- convert to ℕ
    have key := ENat.toNat_le_toNat hsub (by
      exact (WithTop.add_ne_top).mpr ⟨hs, ht⟩)
    rwa [ENat.toNat_add hi hu, ENat.toNat_add hs ht, Nat.add_comm
      (((AlgebraicIndependent.matroid R A).eRk (↑(s ∩ t) : Set A)).toNat)] at key
  ρ_le_card := by
    intro s
    have h := (AlgebraicIndependent.matroid R A).eRk_le_encard (↑s : Set A)
    rw [Set.encard_coe_eq_coe_finsetCard] at h
    calc ((AlgebraicIndependent.matroid R A).eRk (↑s : Set A)).toNat
        ≤ ((s.card : ℕ∞)).toNat := ENat.toNat_le_toNat h (by simp)
      _ = s.card := by simp

end GaloisForLFunctions.MatroidGluing
