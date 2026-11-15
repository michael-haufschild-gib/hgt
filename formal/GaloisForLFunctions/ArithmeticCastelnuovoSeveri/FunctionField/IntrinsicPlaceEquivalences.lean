import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalConstantPlaces

/-!
# Intrinsic places under constant-field isomorphisms

A constant-field isomorphism transports proper valuation rings by
pullback. Its induced residue isomorphism preserves rationality, giving
an equivalence of intrinsic rational places and equality of their counts.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-- Pullback of a proper constant-field place along a constant-field isomorphism. -/
def constantFieldPlaceComap (e : L ≃ₐ[K] L') (W : ConstantFieldPlaces K L') :
    ConstantFieldPlaces K L := by
  refine ⟨W.val.comap e.toRingHom, ?_, ?_⟩
  · intro h
    apply W.property.1
    apply top_unique
    intro x _
    have hx : e.symm x ∈ W.val.comap e.toRingHom := by rw [h]; trivial
    change e (e.symm x) ∈ W.val at hx
    simpa only [e.apply_symm_apply] using hx
  · intro a
    change e (algebraMap K L a) ∈ W.val
    rw [e.commutes]
    exact W.property.2 a

/-- A constant-field isomorphism gives a bijection of all intrinsic places. -/
def constantFieldPlaceEquiv (e : L ≃ₐ[K] L') : ConstantFieldPlaces K L ≃ ConstantFieldPlaces K L' where
  toFun := constantFieldPlaceComap e.symm
  invFun := constantFieldPlaceComap e
  left_inv W := by
    apply Subtype.ext
    ext x
    change e.symm (e x) ∈ W.val ↔ x ∈ W.val
    rw [e.symm_apply_apply]
  right_inv W := by
    apply Subtype.ext
    ext x
    change e (e.symm x) ∈ W.val ↔ x ∈ W.val
    rw [e.apply_symm_apply]

/-- Pullback of a rational place remains rational because the constant residue maps commute. -/
def rationalConstantFieldPlaceComap (e : L ≃ₐ[K] L') (W : RationalConstantFieldPlaces K L') :
    RationalConstantFieldPlaces K L :=
  ⟨constantFieldPlaceComap e W.val,
    (valuationConstantResidue_comap_surjective_iff e W.val.val W.val.property.2).mpr W.property⟩

/-- A constant-field isomorphism gives a bijection of intrinsic rational places. -/
def rationalConstantFieldPlaceEquiv (e : L ≃ₐ[K] L') :
    RationalConstantFieldPlaces K L ≃ RationalConstantFieldPlaces K L' where
  toFun := rationalConstantFieldPlaceComap e.symm
  invFun := rationalConstantFieldPlaceComap e
  left_inv W := Subtype.ext ((constantFieldPlaceEquiv e).left_inv W.val)
  right_inv W := Subtype.ext ((constantFieldPlaceEquiv e).right_inv W.val)

/-- Intrinsic rational-place counts are invariant under isomorphism over the constants. -/
theorem rationalConstantFieldPlaces_card_congr (e : L ≃ₐ[K] L') :
    Nat.card (RationalConstantFieldPlaces K L) = Nat.card (RationalConstantFieldPlaces K L') :=
  Nat.card_congr (rationalConstantFieldPlaceEquiv e)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
