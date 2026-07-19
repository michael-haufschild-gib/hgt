import GaloisForLFunctions.HTGeometry.LeafNodeDivergence
import GaloisForLFunctions.HTGeometry.NevanlinnaClassicalInterface

/-!
# The denominator fibers are pairwise disjoint

A point in the fibers of two distinct finite parameters would satisfy `B x · τ₁ = D x = B x · τ₂`,
forcing `B x = 0` and then `D x = 0`.  The determinant condition `A D − B C = 1` forbids that, so
the
fibers are disjoint — and likewise a finite fiber is disjoint from the fiber at infinity.

This is what makes the leaves of an extremal family distinct: they are carried by disjoint sets.
-/

open scoped BigOperators

namespace HTGeometry

open GaloisForLFunctions.HTGeometry

variable {X : Type*}

/-- The determinant condition forbids `B` and `D` vanishing together. -/
theorem D_ne_zero_of_B_eq_zero (W : ClassicalNevanlinnaMatrixData X) {x : X}
    (hB : W.B x = 0) : W.D x ≠ 0 := by
  intro hD
  have hdet := W.det_one x
  rw [hB, hD] at hdet
  simp at hdet

/-- **Fibers of distinct finite parameters are disjoint.** -/
theorem disjoint_finiteDenominatorFiber (W : ClassicalNevanlinnaMatrixData X) {t1 t2 : ℝ}
    (hne : t1 ≠ t2) :
    Disjoint (W.finiteDenominatorFiber t1) (W.finiteDenominatorFiber t2) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  simp only [ClassicalNevanlinnaMatrixData.finiteDenominatorFiber, Set.mem_setOf_eq] at hx1 hx2
  have hB : W.B x = 0 := by
    have hsub : W.B x * (t1 - t2) = 0 := by ring_nf; linarith [hx1, hx2]
    rcases mul_eq_zero.mp hsub with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have hD : W.D x = 0 := by
    rw [hB, zero_mul] at hx1
    linarith
  exact D_ne_zero_of_B_eq_zero W hB hD

/-- **A finite fiber is disjoint from the fiber at infinity.** -/
theorem disjoint_finite_infinityDenominatorFiber (W : ClassicalNevanlinnaMatrixData X) (t : ℝ) :
    Disjoint (W.finiteDenominatorFiber t) W.infinityDenominatorFiber := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  simp only [ClassicalNevanlinnaMatrixData.finiteDenominatorFiber, Set.mem_setOf_eq] at hx1
  simp only [ClassicalNevanlinnaMatrixData.infinityDenominatorFiber, Set.mem_setOf_eq] at hx2
  have hD : W.D x = 0 := by
    rw [hx2, zero_mul] at hx1
    linarith
  exact D_ne_zero_of_B_eq_zero W hx2 hD

end HTGeometry
