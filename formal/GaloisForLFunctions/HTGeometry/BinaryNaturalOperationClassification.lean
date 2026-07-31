import GaloisForLFunctions.HTGeometry.BareSourceNaturalCompositionNoGo

/-!
# The natural binary operations are exactly the two projections

The bare-source classification shows that a binary operation natural under every map of bare types
must be a coordinate projection.  The converse was never recorded, so the naturality interface had
no producer and the non-commutativity no-go quantified over a class never shown to be nonempty.

Both projections are natural — by definition, with no proof obligation beyond `rfl` — so the
classification upgrades to an equivalence, the class has exactly two elements, and the no-go has
exactly two witnesses.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The first projection is natural. -/
theorem binaryFirstProjection_natural : binaryFirstProjection.Natural :=
  fun _ _ _ => rfl

/-- The second projection is natural. -/
theorem binarySecondProjection_natural : binarySecondProjection.Natural :=
  fun _ _ _ => rfl

/-- The two projections are different operations. -/
theorem binaryFirstProjection_ne_binarySecondProjection :
    binaryFirstProjection ≠ binarySecondProjection := by
  intro h
  have hval := congrFun (congrFun h Bool) (false, true)
  exact Bool.false_ne_true hval

/-- **Binary Yoneda classification, as an equivalence.**  A binary operation on all bare types is
natural under every map exactly when it is one of the two coordinate projections. -/
theorem binaryNaturalOperation_natural_iff (op : BinaryNaturalOperation) :
    op.Natural ↔ op = binaryFirstProjection ∨ op = binarySecondProjection := by
  constructor
  · exact binaryNaturalOperation_eq_projection op
  · rintro (rfl | rfl)
    · exact binaryFirstProjection_natural
    · exact binarySecondProjection_natural

/-- The class of natural binary operations is exactly the pair of projections. -/
theorem setOf_binaryNaturalOperation_natural :
    {op : BinaryNaturalOperation | op.Natural} =
      {binaryFirstProjection, binarySecondProjection} := by
  ext op
  simpa using binaryNaturalOperation_natural_iff op

/-- **The no-go has exactly two witnesses.**  Both projections are natural, they are distinct, and
neither is commutative. -/
theorem binaryNaturalOperation_witnesses :
    binaryFirstProjection.Natural ∧ binarySecondProjection.Natural ∧
      binaryFirstProjection ≠ binarySecondProjection ∧
      ¬ binaryFirstProjection.Commutative ∧ ¬ binarySecondProjection.Commutative :=
  ⟨binaryFirstProjection_natural, binarySecondProjection_natural,
    binaryFirstProjection_ne_binarySecondProjection,
    no_commutative_binaryNaturalOperation _ binaryFirstProjection_natural,
    no_commutative_binaryNaturalOperation _ binarySecondProjection_natural⟩

end GaloisForLFunctions.HTGeometry
