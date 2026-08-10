import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite-dimensional rank of an independent finite supremum
-/

namespace GaloisForLFunctions.HTGeometry

variable {R V ι : Type*} [Field R] [AddCommGroup V] [Module R V]

/-- Finrank is additive over a finite supremum drawn from an independent family of submodules. -/
theorem finrank_finset_sup_of_iSupIndep (p : ι → Submodule R V)
    [∀ i, FiniteDimensional R (p i)] (hind : iSupIndep p) (s : Finset ι) :
    Module.finrank R (s.sup p : Submodule R V) = ∑ i ∈ s, Module.finrank R (p i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      have hdis : Disjoint (p a) (s.sup p) := by
        have h := hind.disjoint_biSup (y := (s : Set ι)) ha
        simpa [Finset.sup_eq_iSup] using h
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq (p a) (s.sup p)
      rw [hdis.eq_bot, finrank_bot, add_zero] at hdim
      rw [Finset.sup_insert, Finset.sum_insert ha, ← ih]
      exact hdim

end GaloisForLFunctions.HTGeometry
