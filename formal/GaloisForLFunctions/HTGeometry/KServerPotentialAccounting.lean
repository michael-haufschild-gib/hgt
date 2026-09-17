import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Abel

/-!
# Extended-cost and potential accounting

The purely algebraic telescoping layer of the k-server proof. It separates the online-algorithm
and potential estimates from the final accounting argument.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- Extended-cost accounting: a pointwise bound on movement plus the work increment telescopes. -/
theorem extendedCost_accounting
    {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    (T : ℕ) (work movement extendedCost : ℕ → α)
    (hwork0 : work 0 = 0)
    (hstep : ∀ t < T,
      movement t + (work (t + 1) - work t) ≤ extendedCost t) :
    (∑ t ∈ Finset.range T, movement t) + work T ≤
      ∑ t ∈ Finset.range T, extendedCost t := by
  calc
    (∑ t ∈ Finset.range T, movement t) + work T =
        (∑ t ∈ Finset.range T, movement t) + (work T - work 0) := by
          rw [hwork0, sub_zero]
    _ = ∑ t ∈ Finset.range T, (movement t + (work (t + 1) - work t)) := by
      rw [Finset.sum_add_distrib, Finset.sum_range_sub]
    _ ≤ ∑ t ∈ Finset.range T, extendedCost t := by
      exact Finset.sum_le_sum fun t ht => hstep t (Finset.mem_range.mp ht)

/-- If the potential pays every request, the sum of extended costs is at most its net increase. -/
theorem potential_pays_sum
    {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    (T : ℕ) (extendedCost potential : ℕ → α)
    (hstep : ∀ t < T,
      extendedCost t ≤ potential (t + 1) - potential t) :
    (∑ t ∈ Finset.range T, extendedCost t) ≤ potential T - potential 0 := by
  calc
    (∑ t ∈ Finset.range T, extendedCost t) ≤
        ∑ t ∈ Finset.range T, (potential (t + 1) - potential t) := by
      exact Finset.sum_le_sum fun t ht => hstep t (Finset.mem_range.mp ht)
    _ = potential T - potential 0 := Finset.sum_range_sub potential T

/-- One-step potential sandwich: a common minor bound cancels, leaving the auxiliary improvement
to pay the request cost. This is the arithmetic passage from Lemmas 4.1--4.3 to Corollary 4.4. -/
theorem potential_pays_request_of_sandwich
    {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    (oldPotential newPotential common oldAux newAux cost : α)
    (hold : oldPotential ≤ common + oldAux)
    (hnew : common + newAux ≤ newPotential)
    (hcost : cost ≤ newAux - oldAux) :
    cost ≤ newPotential - oldPotential := by
  calc
    cost ≤ newAux - oldAux := hcost
    _ = (common + newAux) - (common + oldAux) := by abel
    _ ≤ newPotential - oldPotential := sub_le_sub hnew hold

/-- The final competitive-ratio algebra: extended-cost accounting plus a paying potential with
the paper's initial and terminal bounds yields the coefficient `k`. -/
theorem kServer_competitive_of_potential
    {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (T k : ℕ) (work movement extendedCost potential : ℕ → α)
    (initialClique terminalClique : α)
    (hwork0 : work 0 = 0)
    (haccount : ∀ t < T,
      movement t + (work (t + 1) - work t) ≤ extendedCost t)
    (hpays : ∀ t < T,
      extendedCost t ≤ potential (t + 1) - potential t)
    (hinitial : potential 0 = -initialClique)
    (hterminal : potential T ≤ ((k + 1 : ℕ) : α) * work T - terminalClique) :
    (∑ t ∈ Finset.range T, movement t) ≤
      (k : α) * work T + initialClique - terminalClique := by
  have hmovement := extendedCost_accounting T work movement extendedCost hwork0 haccount
  have hpotential := potential_pays_sum T extendedCost potential hpays
  have htotal :
      (∑ t ∈ Finset.range T, movement t) + work T ≤
        ((k + 1 : ℕ) : α) * work T + initialClique - terminalClique := by
    calc
      (∑ t ∈ Finset.range T, movement t) + work T ≤
          ∑ t ∈ Finset.range T, extendedCost t := hmovement
      _ ≤ potential T - potential 0 := hpotential
      _ ≤ (((k + 1 : ℕ) : α) * work T - terminalClique) - potential 0 :=
        sub_le_sub_right hterminal _
      _ = ((k + 1 : ℕ) : α) * work T + initialClique - terminalClique := by
        rw [hinitial, sub_neg_eq_add]
        abel
  calc
    (∑ t ∈ Finset.range T, movement t) =
        ((∑ t ∈ Finset.range T, movement t) + work T) - work T := by abel
    _ ≤ (((k + 1 : ℕ) : α) * work T + initialClique - terminalClique) - work T :=
      sub_le_sub_right htotal _
    _ = (k : α) * work T + initialClique - terminalClique := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      abel

end GaloisForLFunctions.HTGeometry
