import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.GDelta.Basic
import Mathlib.Order.Filter.CountableInter

/-!
# Generic avoidance of countably many nowhere-dense loci

The comeager gauge-selection theorems (`fixed-divisor-full-complex-translation-freeness`,
`symmetry-caged-fixed-divisor-full-orbit-freeness`, and the maximal-HT Bohr-boundary cards) all have
the same logical backbone: there are only countably many "relation loci" — one for each finite
family of distinct translates and each nonzero differential polynomial — and each locus is shown to
be nowhere dense (a closed set with empty interior) in the Baire space of admissible gauges.  The
Baire category theorem then yields a comeager, hence dense and nonempty, set of gauges lying in the
complement of every locus.

This file isolates that backbone as reusable, ring-agnostic lemmas: the analytic content of the
cards is exactly the hypothesis that each locus is nowhere dense; the passage to a generic gauge is
then pure topology.
-/

namespace GaloisForLFunctions

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- A closed set with empty interior is nowhere dense. -/
theorem isNowhereDense_of_isClosed_of_interior_eq_empty {s : Set X}
    (hclosed : IsClosed s) (hint : interior s = ∅) : IsNowhereDense s := by
  rw [IsNowhereDense, hclosed.closure_eq, hint]

/-- **Generic avoidance.**  In a Baire space, the set of points avoiding every member of a countable
family of nowhere-dense sets is dense.  Its complement `⋃ n, S n` is meagre, so the intersection of
complements is comeager. -/
theorem dense_setOf_forall_notMem_of_isNowhereDense [BaireSpace X]
    (S : ℕ → Set X) (hS : ∀ n, IsNowhereDense (S n)) :
    Dense {x | ∀ n, x ∉ S n} := by
  have hset : {x | ∀ n, x ∉ S n} = ⋂ n, (S n)ᶜ := by
    ext x; simp
  rw [hset]
  exact dense_of_mem_residual (countable_iInter_mem.mpr fun n => (hS n).isMeagre)

/-- In a nonempty Baire space, there is a point avoiding every member of a countable family of
nowhere-dense sets. -/
theorem exists_forall_notMem_of_isNowhereDense [BaireSpace X] [Nonempty X]
    (S : ℕ → Set X) (hS : ∀ n, IsNowhereDense (S n)) :
    ∃ x, ∀ n, x ∉ S n :=
  (dense_setOf_forall_notMem_of_isNowhereDense S hS).nonempty

/-- Generic avoidance packaged for the cards' hypothesis form: each relation locus is a closed set
with empty interior. -/
theorem dense_setOf_forall_notMem_of_isClosed_interior_empty [BaireSpace X]
    (S : ℕ → Set X) (hclosed : ∀ n, IsClosed (S n)) (hint : ∀ n, interior (S n) = ∅) :
    Dense {x | ∀ n, x ∉ S n} :=
  dense_setOf_forall_notMem_of_isNowhereDense S fun n =>
    isNowhereDense_of_isClosed_of_interior_eq_empty (hclosed n) (hint n)

end GaloisForLFunctions
