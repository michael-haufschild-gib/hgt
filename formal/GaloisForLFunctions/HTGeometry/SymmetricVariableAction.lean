import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.GroupTheory.Perm.Fin

/-!
# Permuting the variables of a rational function field

Renaming variables by a permutation is an action of the symmetric group on a multivariate
polynomial ring, and it extends to the field of rational functions.  The action is faithful,
because a permutation moving an index moves the corresponding variable.

Artin's theorem then says the rational function field is Galois over its symmetric part, of degree
the order of the symmetric group.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- Renaming variables by a permutation is a semiring action of the symmetric group. -/
noncomputable scoped instance permMvPolynomialAction (σ : Type*) (K : Type*) [CommSemiring K] :
    MulSemiringAction (Equiv.Perm σ) (MvPolynomial σ K) where
  smul e p := rename (e : σ → σ) p
  one_smul p := by
    show rename ((1 : Equiv.Perm σ) : σ → σ) p = p
    simp
  mul_smul a b p := by
    show rename ((a * b : Equiv.Perm σ) : σ → σ) p =
      rename (a : σ → σ) (rename (b : σ → σ) p)
    rw [rename_rename]
    rfl
  smul_zero e := map_zero (rename (e : σ → σ))
  smul_add e p q := map_add (rename (e : σ → σ)) p q
  smul_one e := map_one (rename (e : σ → σ))
  smul_mul e p q := map_mul (rename (e : σ → σ)) p q

theorem perm_smul_mvPolynomial {σ K : Type*} [CommSemiring K] (e : Equiv.Perm σ)
    (p : MvPolynomial σ K) : e • p = rename (e : σ → σ) p := rfl

@[simp]
theorem perm_smul_X {σ K : Type*} [CommSemiring K] (e : Equiv.Perm σ) (i : σ) :
    e • (MvPolynomial.X i : MvPolynomial σ K) = MvPolynomial.X (e i) := by
  rw [perm_smul_mvPolynomial, rename_X]

noncomputable scoped instance permMvPolynomialFaithful (σ : Type*) (K : Type*) [CommSemiring K]
    [Nontrivial K] : FaithfulSMul (Equiv.Perm σ) (MvPolynomial σ K) where
  eq_of_smul_eq_smul {a b} h := by
    refine Equiv.ext fun i => ?_
    have hi := h (MvPolynomial.X i)
    rw [perm_smul_X, perm_smul_X] at hi
    exact MvPolynomial.X_injective hi

/-! ## The rational function field -/

/-- The field of rational functions in `d` variables. -/
abbrev SymmetricRationalField (K : Type*) [Field K] (d : ℕ) : Type _ :=
  FractionRing (MvPolynomial (Fin d) K)

noncomputable scoped instance permSymmetricRationalFieldAction (K : Type*) [Field K] (d : ℕ) :
    MulSemiringAction (Equiv.Perm (Fin d)) (SymmetricRationalField K d) :=
  IsFractionRing.mulSemiringAction (Equiv.Perm (Fin d)) (MvPolynomial (Fin d) K)
    (SymmetricRationalField K d)

noncomputable scoped instance permSymmetricRationalFieldFaithful (K : Type*) [Field K] (d : ℕ) :
    FaithfulSMul (Equiv.Perm (Fin d)) (SymmetricRationalField K d) :=
  IsFractionRing.faithfulSMul (Equiv.Perm (Fin d)) (MvPolynomial (Fin d) K)
    (SymmetricRationalField K d)

/-- The symmetric part of the rational function field: the rational functions invariant under every
permutation of the variables. -/
noncomputable abbrev symmetricPart (K : Type*) [Field K] (d : ℕ) :
    Subfield (SymmetricRationalField K d) :=
  FixedPoints.subfield (Equiv.Perm (Fin d)) (SymmetricRationalField K d)

/-- **Artin's theorem for variable permutations.**  The rational function field in `d` variables has
degree `d!` over its symmetric part. -/
theorem finrank_symmetricPart (K : Type*) [Field K] (d : ℕ) :
    Module.finrank (symmetricPart K d) (SymmetricRationalField K d) = Nat.factorial d := by
  rw [symmetricPart, FixedPoints.finrank_eq_card, Fintype.card_perm, Fintype.card_fin]

end GaloisForLFunctions.HTGeometry
