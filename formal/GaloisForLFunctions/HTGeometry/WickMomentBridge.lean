import GaloisForLFunctions.HTGeometry.WickFieldTheorem
import GaloisForLFunctions.HTGeometry.QuasiFreeWickExpansion

/-!
# The vacuum expectation is the Isserlis moment

`QuasiFreeWickExpansion.wickMoment` is the Isserlis sum over perfect matchings, taken there as the
*definition* of a quasi-free moment.  `CompletePairing.completePairing` is the same recursion; this
file identifies them and hence turns the quasi-free hypothesis of that development into a theorem:
for any creation/annihilation system with a vacuum, the vacuum expectation of a word of fields *is*
the Isserlis moment of its two-point functions.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type w} {A : Type v} [CommRing A]

private theorem completePairing_eq_wickMoment_aux (c : ι → ι → A) :
    ∀ (n : ℕ) (l : List ι), l.length ≤ n → completePairing c l = wickMoment c l := by
  intro n
  induction n with
  | zero =>
      intro l hl
      match l with
      | [] => simp
      | (_ :: _) => simp at hl
  | succ n ih =>
      intro l hl
      match l with
      | [] => simp
      | (u :: t) =>
        have ht : t.length ≤ n := by simpa using hl
        rw [completePairing_cons, wickMoment_cons]
        simp only [positionSum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht)]
        rfl

/-- The complete-pairing sum is the Isserlis moment. -/
theorem completePairing_eq_wickMoment (c : ι → ι → A) (l : List ι) :
    completePairing c l = wickMoment c l :=
  completePairing_eq_wickMoment_aux c l.length l le_rfl

namespace WickVacuum

variable {K : Type u} [CommRing K] [Algebra K A]
variable {W : WickSystem K A ι} (V : WickVacuum W)

/-- **A vacuum state of a creation/annihilation system is quasi-free.**  Its correlation functions
are the Isserlis moments of the two-point function. -/
theorem vacuum_prod_field_eq_wickMoment (l : List ι) :
    V.ω ((l.map W.field).prod) = wickMoment W.κ l := by
  rw [V.vacuum_prod_field l, completePairing_eq_wickMoment]

/-- The same for a word of pure creation and annihilation letters. -/
theorem vacuum_prod_op_eq_wickMoment (l : List (WickMode ι)) :
    V.ω ((l.map W.op).prod) = wickMoment W.contract l := by
  rw [V.vacuum_prod_op l, completePairing_eq_wickMoment]

end WickVacuum

end GaloisForLFunctions.HTGeometry
