import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Spherical `F₁` scalar extension does not produce arithmetic localization

For an additive monoid `M`, ordinary integral scalar extension of its spherical
monoid object has coefficient ring `AddMonoidAlgebra ℤ M`.  This cannot be the
arithmetic localization `ℤ[1/p]` when `p ≥ 2`.

The obstruction is functorial and independent of `M`: augmentation sends every
monomial to `1`, so a scalar that were a unit in the monoid algebra would already
be a unit in `ℤ`.  Thus `p` remains a nonunit in the monoid algebra, whereas its
image is a unit in `Localization.Away p`.

This is a no-go for *ordinary scalar extension only*.  It leaves open, and
forces, loss-aware comparison maps using evaluation, localization, completion,
or a point functor.
-/

namespace GaloisForLFunctions.HTGeometry.FieldOneCore

noncomputable section

/-- Augmentation of an additive monoid algebra: every monomial is sent to `1`. -/
def integralMonoidAugmentation (M : Type*) [AddMonoid M] :
    AddMonoidAlgebra ℤ M →ₐ[ℤ] ℤ :=
  AddMonoidAlgebra.lift ℤ ℤ M 1

/-- A natural scalar `p ≥ 2` is not a unit in any integral additive monoid
algebra.  Augmentation detects the obstruction already in `ℤ`. -/
theorem integralScalar_nonunit_in_addMonoidAlgebra
    {M : Type*} [AddMonoid M] {p : ℕ} (hp : 2 ≤ p) :
    ¬ IsUnit (algebraMap ℤ (AddMonoidAlgebra ℤ M) (p : ℤ)) := by
  intro h
  have hu : IsUnit (p : ℤ) := by
    simpa using h.map (integralMonoidAugmentation M).toRingHom
  have habs : |(p : ℤ)| = 1 := Int.isUnit_iff_abs_eq.mp hu
  have hcast : (p : ℤ) = 1 := by
    simpa using habs
  have hp_ne_one : p ≠ 1 :=
    Nat.ne_of_gt (lt_of_lt_of_le Nat.one_lt_two hp)
  apply hp_ne_one
  exact_mod_cast hcast

/-- The same scalar is a unit after localization away from `p`. -/
theorem integralScalar_isUnit_in_away (p : ℕ) :
    IsUnit (algebraMap ℤ (Localization.Away (p : ℤ)) (p : ℤ)) :=
  IsLocalization.Away.algebraMap_isUnit _

/-- A canonical comparison exists after collapsing every monomial by
augmentation and then mapping coefficients into `ℤ[1/p]`. -/
def augmentedAwayComparison (M : Type*) [AddMonoid M] (p : ℕ) :
    AddMonoidAlgebra ℤ M →ₐ[ℤ] Localization.Away (p : ℤ) :=
  (Algebra.ofId ℤ (Localization.Away (p : ℤ))).comp
    (integralMonoidAugmentation M)

/-- The canonical augmentation--localization comparison sends every monomial
to `1`.  This is its exact loss ledger. -/
theorem augmentedAwayComparison_of
    (M : Type*) [AddMonoid M] (p : ℕ) (m : Multiplicative M) :
    augmentedAwayComparison M p (AddMonoidAlgebra.of ℤ M m) = 1 := by
  simp [augmentedAwayComparison, integralMonoidAugmentation]

/-- Consequently the comparison identifies every pair of monomials. -/
theorem augmentedAwayComparison_identifies_monomials
    (M : Type*) [AddMonoid M] (p : ℕ) (m n : Multiplicative M) :
    augmentedAwayComparison M p (AddMonoidAlgebra.of ℤ M m) =
      augmentedAwayComparison M p (AddMonoidAlgebra.of ℤ M n) := by
  rw [augmentedAwayComparison_of, augmentedAwayComparison_of]

/-- If the exponent monoid has two distinct elements, the canonical comparison
is not injective. -/
theorem augmentedAwayComparison_not_injective
    {M : Type*} [AddMonoid M] (p : ℕ) {m n : Multiplicative M}
    (hmn : m ≠ n) :
    ¬ Function.Injective (augmentedAwayComparison M p) := by
  intro hinj
  apply hmn
  exact AddMonoidAlgebra.of_injective
    (hinj (augmentedAwayComparison_identifies_monomials M p m n))

/-- Ordinary integral scalar extension of any additive monoid object cannot be
`ℤ[1/p]` as a `ℤ`-algebra when `p ≥ 2`. -/
theorem addMonoidAlgebra_not_algEquiv_away
    {M : Type*} [AddMonoid M] {p : ℕ} (hp : 2 ≤ p) :
    ¬ Nonempty
      (AddMonoidAlgebra ℤ M ≃ₐ[ℤ] Localization.Away (p : ℤ)) := by
  rintro ⟨e⟩
  have hloc := integralScalar_isUnit_in_away p
  have hback := hloc.map e.symm.toRingEquiv.toRingHom
  have hsource :
      IsUnit (algebraMap ℤ (AddMonoidAlgebra ℤ M) (p : ℤ)) := by
    simpa using hback
  exact integralScalar_nonunit_in_addMonoidAlgebra hp hsource

end

end GaloisForLFunctions.HTGeometry.FieldOneCore
