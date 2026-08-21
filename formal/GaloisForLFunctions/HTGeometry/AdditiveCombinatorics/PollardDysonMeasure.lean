import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardStabSmall

/-!
# The Dyson transform and the induction measure

`repSum_dyson_le` says the Dyson transform does not increase `repSum`, and `dyson_measure_drop`
says it preserves `#A + #B` while strictly decreasing `min (#A) (#B)` whenever the small part is a
proper subset of `B`.  Together these are exactly what makes Grynkiewicz's lexicographic induction
measure `(repSum, 2·repSum − (#A + #B), min (#A) (#B))` decrease at CASE 4.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- The Dyson transform does not increase `repSum`. -/
theorem repSum_dyson_le (A B : Finset G) (x : G) (t : ℕ) :
    repSum (dysonLarge A B x) (dysonSmall A B x) t ≤ repSum A B t := by
  rw [repSum, repSum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  calc (repSet (dysonLarge A B x) (dysonSmall A B x) i).card
      ≤ (x • repSet A B i).card := Finset.card_le_card (repSet_dyson_subset A B x i)
    _ = (repSet A B i).card := Finset.card_smul_finset _ _

omit [Fintype G] in
/-- The Dyson transform strictly decreases the last component of the induction measure, while the
first two do not increase. -/
theorem dyson_measure_drop {A B : Finset G} {x : G} (hBA : B.card ≤ A.card)
    (hlt : (dysonSmall A B x).card < B.card) :
    (dysonLarge A B x).card + (dysonSmall A B x).card = A.card + B.card
      ∧ min (dysonLarge A B x).card (dysonSmall A B x).card < min A.card B.card := by
  refine ⟨card_dysonLarge_add_card_dysonSmall A B x, ?_⟩
  have hmin : min A.card B.card = B.card := min_eq_right hBA
  rw [hmin]
  exact lt_of_le_of_lt (min_le_right _ _) hlt

end GaloisForLFunctions.HTGeometry.AddComb
