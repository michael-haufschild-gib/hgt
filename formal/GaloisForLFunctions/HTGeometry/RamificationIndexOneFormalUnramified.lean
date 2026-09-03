import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Formal unramifiedness from pointwise ramification index one

For a finite integral domain extension, formal unramifiedness is checked at every target prime.
The generic prime always has ramification index one; at every nonzero prime, ramification index one
and a perfect residue field give Mathlib's exact local unramifiedness criterion.
-/

namespace Algebra

noncomputable section

universe u v

/-- The generic prime of a finite faithful domain extension has ramification index one. -/
theorem Ideal.ramificationIdx_bot_eq_one
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [Module.Finite A B] :
    (⊥ : Ideal B).ramificationIdx A = 1 := by
  let S := Localization.AtPrime (⊥ : Ideal B)
  have hmax : IsLocalRing.maximalIdeal S = ⊥ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (⊥ : Ideal B) S, Ideal.map_bot]
  letI : Field S := IsField.toField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax)
  rw [Ideal.ramificationIdx_def, Ideal.under_bot, Ideal.map_bot]
  have hlen : Module.length S (S ⧸ (⊥ : Ideal S)) = 1 := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
    exact Ideal.bot_isMaximal (K := S)
  rw [hlen]
  simp

/-- A finite domain extension is formally unramified when every nonzero prime has ramification
index one and every base residue field occurring below a target prime is perfect. -/
theorem formallyUnramified_of_ramificationIdx_eq_one
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [Module.Finite A B]
    (hperfect : ∀ (q : Ideal B) (_ : q.IsPrime),
      PerfectField (q.under A).ResidueField)
    (hram : ∀ (q : Ideal B) [q.IsPrime], q ≠ ⊥ → q.ramificationIdx A = 1) :
    FormallyUnramified A B := by
  rw [Algebra.formallyUnramified_iff_forall]
  intro q
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : PerfectField (q.asIdeal.under A).ResidueField :=
    hperfect q.asIdeal q.isPrime
  rcases eq_or_ne q.asIdeal ⊥ with hq0 | hq0
  · exact Ideal.ramificationIdx_eq_one_iff.mp <| by
      simpa only [hq0] using
        (Ideal.ramificationIdx_bot_eq_one (A := A) (B := B))
  · exact Ideal.ramificationIdx_eq_one_iff.mp (hram q.asIdeal hq0)

end
end Algebra
