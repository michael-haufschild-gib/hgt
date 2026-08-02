import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Complex.Basic

/-!
# Arbitrarily large independent families inside a set of infinite rank

A set whose span has infinite rank contains arbitrarily large linearly independent finite families:
extract a basis of the span from the set itself; a finite basis would bound the rank, so the basis is
infinite, and any injection from a finite index type into it stays independent.

This is the step from "the exponent group has infinite rational rank" — the hypothesis of the
Dirichlet-series criterion — to "the spectrum contains independent families of every size", which is
the hypothesis the frequency-rank exclusion consumes.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **Infinite rank produces independent families of every size.** -/
theorem exists_independent_family_of_infinite_rank {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [StrongRankCondition K] {S : Set V}
    (hrank : ∀ n : ℕ, ¬ Module.rank K ↥(Submodule.span K S) ≤ (n : Cardinal)) (m : ℕ) :
    ∃ ν : Fin m → V, LinearIndependent K ν ∧ ∀ i, ν i ∈ S := by
  classical
  obtain ⟨b, hbS, hspan, hbind⟩ := exists_linearIndependent K S
  -- a finite generating subset would bound the rank
  have hinf : b.Infinite := by
    intro hfin
    refine hrank hfin.toFinset.card ?_
    have hle : Module.rank K ↥(Submodule.span K S) ≤ Cardinal.mk ↥b := by
      rw [← hspan]
      exact rank_span_le b
    have hcard : Cardinal.mk ↥b = (hfin.toFinset.card : Cardinal) := by
      have hmk : Cardinal.mk ↥((hfin.toFinset : Finset V) : Set V)
          = (hfin.toFinset.card : Cardinal) := Cardinal.mk_coe_finset
      rw [hfin.coe_toFinset] at hmk
      exact hmk
    exact hle.trans (le_of_eq hcard)
  -- an injection from a finite index type into the basis
  set g : ℕ ↪ ↥b := hinf.natEmbedding
  refine ⟨fun i => ((g (i : ℕ) : ↥b) : V), ?_, fun i => hbS (g (i : ℕ)).2⟩
  have hcomp : LinearIndependent K
      ((Subtype.val : ↥b → V) ∘ (fun i : Fin m => g (i : ℕ))) := by
    refine hbind.comp _ ?_
    intro i j hij
    exact Fin.val_injective (g.injective hij)
  exact hcomp

end GaloisForLFunctions.HTGeometry
