import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheCountOfASectionOnTwoGraphsIsTheSplitNorm
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TwoBranchContact

/-!
# The conductor of two graphs is their contact

The split norm of a section forgets the contact between the graphs.
The conductor of the actual order recovers it exactly: multiplication by
`(a,b)` carries the split ambient algebra into the order precisely when both
coordinates belong to the graph-contact ideal. This applies the two-branch
conductor mechanism of Du, Theorem 8.12, to the ghost-coordinate square.
-/

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The conductor in the split ambient algebra is `J × J`. -/
theorem pairRing_contact_conductor (J : Ideal ℤ) (z : ℤ × ℤ) :
    (∀ w : ℤ × ℤ, z * w ∈ pairRing J) ↔ z.1 ∈ J ∧ z.2 ∈ J :=
  ArithmeticCastelnuovoSeveri.product_contact_conductor_iff J z

/-- The conductor of the actual two-graph restriction recovers its exact contact ideal. -/
theorem ghostPair_contact_conductor (m n : ℕ+) (z : ℤ × ℤ) :
    (∀ w : ℤ × ℤ, ∃ x : ghostRing,
      (ghostComponent m x, ghostComponent n x) = z * w) ↔
        z.1 ∈ graphIdeal m n ∧ z.2 ∈ graphIdeal m n := by
  calc
    _ ↔ ∀ w : ℤ × ℤ, z * w ∈ pairRing (graphIdeal m n) := by
      apply forall_congr'
      intro w
      change z * w ∈ Set.range (fun x : ghostRing =>
        (ghostComponent m x, ghostComponent n x)) ↔ _
      rw [range_ghostComponent_pair]
      rfl
    _ ↔ _ := pairRing_contact_conductor _ _

#print axioms pairRing_contact_conductor
#print axioms ghostPair_contact_conductor

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
