import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Complex.Basic

/-!
# Bounding the orders and degrees occurring in a palette relation

A relation among the jets of a palette involves finitely many monomials, each involving finitely many
jets.  So one bound serves for the whole relation: no jet of order above it occurs, and no carrier
appears in a monomial more often than it.

Both bounds are what lets a relation be read as a *graded* combination over a finite index of
multi-degrees, with orders drawn from a fixed finite box.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {n : ℕ}

/-- **No jet of order above a fixed bound occurs in a relation.** -/
theorem exists_order_bound (Q : MvPolynomial (Fin n × ℕ) ℂ) :
    ∃ N : ℕ, ∀ m ∈ Q.support, ∀ (k : Fin n) (j : ℕ), N < j → m (k, j) = 0 := by
  classical
  refine ⟨Q.support.sup fun m => m.support.sup fun q => q.2, ?_⟩
  intro m hm k j hj
  by_contra hne
  have hmem : (k, j) ∈ m.support := Finsupp.mem_support_iff.mpr hne
  have h1 : j ≤ m.support.sup fun q : Fin n × ℕ => q.2 :=
    Finset.le_sup (f := fun q : Fin n × ℕ => q.2) hmem
  have h2 : (m.support.sup fun q : Fin n × ℕ => q.2)
      ≤ Q.support.sup fun m => m.support.sup fun q => q.2 :=
    Finset.le_sup (f := fun m : (Fin n × ℕ) →₀ ℕ => m.support.sup fun q => q.2) hm
  omega

/-- **A carrier occurs in a monomial no more often than the total degree.**  The orders are drawn
from a box, so the multi-degree of a monomial is bounded by the total degree of the relation. -/
theorem sum_le_totalDegree (Q : MvPolynomial (Fin n × ℕ) ℂ) {m : (Fin n × ℕ) →₀ ℕ}
    (hm : m ∈ Q.support) (k : Fin n) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), m (k, j)) ≤ Q.totalDegree := by
  classical
  refine le_trans ?_ (le_totalDegree hm)
  have himg : (∑ j ∈ Finset.range (N + 1), m (k, j))
      = ∑ q ∈ (Finset.range (N + 1)).image (fun j => (k, j)), m q := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    simpa using hxy
  have hfil : (∑ q ∈ (Finset.range (N + 1)).image (fun j => (k, j)), m q)
      = ∑ q ∈ ((Finset.range (N + 1)).image (fun j => (k, j))).filter
          (fun q => q ∈ m.support), m q := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro q _ hq
    exact Finsupp.mem_support_iff.mpr hq
  rw [himg, hfil, Finsupp.sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
  intro q hq
  exact (Finset.mem_filter.mp hq).2

end

end GaloisForLFunctions.HTGeometry
