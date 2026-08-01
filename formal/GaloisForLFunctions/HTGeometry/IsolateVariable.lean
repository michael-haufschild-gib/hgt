import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Isolating one variable of a multivariate polynomial ring

A polynomial ring in a family of variables is a polynomial ring in one distinguished variable over
the polynomial ring in the others.  Mathlib provides this for `Option σ` and for `Fin (n+1)`, where
the distinguished variable is a designated point of the index type; here it is provided for an
arbitrary index of an arbitrary index type with decidable equality.

This is what turns a statement about the degree in one variable into a statement about an ordinary
one-variable polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Splitting an index type at one of its elements. -/
def optionNeEquiv {σ : Type v} [DecidableEq σ] (j : σ) : Option {i : σ // i ≠ j} ≃ σ where
  toFun o := o.elim j Subtype.val
  invFun i := if h : i = j then none else some ⟨i, h⟩
  left_inv o := by
    cases o with
    | none => simp
    | some a => simp [a.2]
  right_inv i := by
    by_cases h : i = j
    · simp [h]
    · simp [h]

@[simp] theorem optionNeEquiv_symm_self {σ : Type v} [DecidableEq σ] (j : σ) :
    (optionNeEquiv j).symm j = none := by
  simp [optionNeEquiv]

@[simp] theorem optionNeEquiv_symm_of_ne {σ : Type v} [DecidableEq σ] {j i : σ} (h : i ≠ j) :
    (optionNeEquiv j).symm i = some ⟨i, h⟩ := by
  simp [optionNeEquiv, h]

variable (K : Type u) [CommRing K] {σ : Type v} [DecidableEq σ]

/-- **A polynomial ring is a one-variable polynomial ring over the ring in the other variables.** -/
noncomputable def isolateVar (j : σ) :
    MvPolynomial σ K ≃ₐ[K] Polynomial (MvPolynomial {i : σ // i ≠ j} K) :=
  (MvPolynomial.renameEquiv K (optionNeEquiv j)).symm.trans (MvPolynomial.optionEquivLeft K _)

@[simp] theorem isolateVar_X_self (j : σ) :
    isolateVar K j (MvPolynomial.X j) = Polynomial.X := by
  rw [isolateVar, AlgEquiv.trans_apply, show (MvPolynomial.renameEquiv K (optionNeEquiv j)).symm
      (MvPolynomial.X j) = MvPolynomial.X none from ?_, MvPolynomial.optionEquivLeft_X_none]
  rw [AlgEquiv.symm_apply_eq, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  rfl

@[simp] theorem isolateVar_X_of_ne {j i : σ} (h : i ≠ j) :
    isolateVar K j (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X ⟨i, h⟩) := by
  rw [isolateVar, AlgEquiv.trans_apply, show (MvPolynomial.renameEquiv K (optionNeEquiv j)).symm
      (MvPolynomial.X i) = MvPolynomial.X (some ⟨i, h⟩) from ?_,
    MvPolynomial.optionEquivLeft_X_some]
  rw [AlgEquiv.symm_apply_eq, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  rfl

end GaloisForLFunctions.HTGeometry
