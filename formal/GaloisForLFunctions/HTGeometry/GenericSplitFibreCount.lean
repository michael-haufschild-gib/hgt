import GaloisForLFunctions.HTGeometry.SeparableSplitDivisorCount
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The generic fibre of the factorization map

The generic monic split polynomial of degree `L` is the one whose roots are `L` independent
indeterminates.  Distinct indeterminates are distinct, so it is separable, and the count of its monic
divisors of a prescribed degree is the binomial coefficient.

This is the generic fibre of a factorization map, counted without intersection theory: genericity is
realised as independence of the roots rather than as an open condition, and the separability that a
generic-etaleness argument would supply is then immediate.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable (K : Type*) [Field K] (L : ℕ)

/-- The generic root: the image of the `i`-th indeterminate in the field of rational functions. -/
noncomputable def genericSplitRoot (i : Fin L) : FractionRing (MvPolynomial (Fin L) K) :=
  algebraMap (MvPolynomial (Fin L) K) (FractionRing (MvPolynomial (Fin L) K)) (MvPolynomial.X i)

/-- The generic split monic polynomial of degree `L`. -/
noncomputable def genericSplitPoly : (FractionRing (MvPolynomial (Fin L) K))[X] :=
  ∏ i : Fin L, (X - C (genericSplitRoot K L i))

/-- **The generic roots are distinct.** -/
theorem genericSplitRoot_injective : Function.Injective (genericSplitRoot K L) := by
  intro i j h
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin L) K)
      (FractionRing (MvPolynomial (Fin L) K))) :=
    IsFractionRing.injective (MvPolynomial (Fin L) K) (FractionRing (MvPolynomial (Fin L) K))
  exact MvPolynomial.X_injective (hinj h)

theorem genericSplitPoly_monic : (genericSplitPoly K L).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem genericSplitPoly_natDegree : (genericSplitPoly K L).natDegree = L := by
  rw [genericSplitPoly, Polynomial.natDegree_prod _ _ fun _ _ => X_sub_C_ne_zero _]
  simp

theorem genericSplitPoly_splits : (genericSplitPoly K L).Splits :=
  Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _

/-- **The generic split polynomial is separable**, because its roots are independent
indeterminates. -/
theorem genericSplitPoly_separable : (genericSplitPoly K L).Separable :=
  Polynomial.separable_prod_X_sub_C_iff.2 (genericSplitRoot_injective K L)

/-! ## The count -/

/-- **The generic fibre of the factorization map has exactly a binomial coefficient of points.**
For the generic target no intersection theory is needed: its monic divisors of a prescribed degree
are the subsets of its root set of that size. -/
theorem nat_card_monic_divisors_genericSplitPoly (m : ℕ) :
    Nat.card {A : (FractionRing (MvPolynomial (Fin L) K))[X] //
        A.Monic ∧ A ∣ genericSplitPoly K L ∧ A.natDegree = m}
      = L.choose m := by
  classical
  have h := nat_card_monic_divisors (genericSplitPoly_monic K L) (genericSplitPoly_separable K L)
    (genericSplitPoly_splits K L) m
  rwa [genericSplitPoly_natDegree K L] at h

end GaloisForLFunctions.HTGeometry
