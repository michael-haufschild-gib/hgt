import Mathlib

/-!
# Exact signed supported-column exchange for Euler deletion

A filtered-cardinality column can be reversed before any estimate. The
identity preserves each outer signed coefficient, so the resulting inner
columns retain the complete inserted-prime cancellation.
-/

noncomputable section
set_option autoImplicit false
open Finset
open scoped BigOperators

namespace RHTower.DeletionSignedFilterExchange

/-- Exact finite exchange of a signed outer sum with a filtered-cardinality column. -/
theorem weighted_filter_card_exchange {α β : Type*}
    (s : Finset α) (t : Finset β) (P : α → β → Prop)
    [Pdec : (d : α) → DecidablePred (P d)] (w : α → ℝ) :
    ∑ d ∈ s, w d * ((t.filter (P d)).card : ℝ) =
      ∑ n ∈ t, ∑ d ∈ s, w d * (if P d n then 1 else 0) := by
  have hcard (d : α) : ((t.filter (P d)).card : ℝ) =
      ∑ n ∈ t, if P d n then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp
  simp_rw [hcard]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]

end RHTower.DeletionSignedFilterExchange
