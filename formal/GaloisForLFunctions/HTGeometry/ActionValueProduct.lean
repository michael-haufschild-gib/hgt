/-
# The symmetrised value of a one-variable polynomial at every labelled spectral action

The elimination step of the transversality tail needs more than the symmetrised action polynomial:
it needs the product, over every labelling of the spectrum, of the value at that labelling of a
*given* one-variable polynomial whose coefficients live in the coordinate ring.  That product is
again symmetric in the eigenvalues, hence again a polynomial in the elementary symmetric functions
and therefore in the coordinates alone; and it vanishes as soon as the given polynomial vanishes at
one labelled action value.

Main results:
* `isSymmetric_prod_of_equivariant` — an equivariant family has a symmetric product.
* `actionValueProduct` — the product of the values at all labelled actions.
* `isSymmetric_actionValueProduct`, `exists_esymmAlgHom_actionValueProduct` — **it is a polynomial
  in the elementary symmetric functions**.
* `eval₂_actionValueProduct`, `eval₂_actionValueProduct_eq_zero` — **its evaluation, and the
  vanishing criterion**.
-/
import GaloisForLFunctions.HTGeometry.LabeledActionSymmetricPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

/-- **An equivariant family has a symmetric product.** -/
theorem isSymmetric_prod_of_equivariant {F : Equiv.Perm σ → MvPolynomial σ R}
    (hF : ∀ τ π : Equiv.Perm σ, rename (τ : σ → σ) (F π) = F (τ * π)) :
    MvPolynomial.IsSymmetric (∏ π : Equiv.Perm σ, F π) := by
  intro τ
  rw [map_prod]
  rw [Finset.prod_congr rfl fun π _ => hF τ π]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun π => rfl

/-- The value of a one-variable polynomial over the coordinate ring at one labelled action. -/
def actionValue (Q : Polynomial R) (k : σ → R) (π : Equiv.Perm σ) : MvPolynomial σ R :=
  Polynomial.eval₂ (MvPolynomial.C : R →+* MvPolynomial σ R) (labeledAction k π) Q

omit [DecidableEq σ] in
theorem rename_actionValue (Q : Polynomial R) (k : σ → R) (π τ : Equiv.Perm σ) :
    rename (τ : σ → σ) (actionValue Q k π) = actionValue Q k (τ * π) := by
  rw [actionValue, actionValue]
  have h := Polynomial.hom_eval₂ Q (MvPolynomial.C : R →+* MvPolynomial σ R)
    ((rename (τ : σ → σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) :
      MvPolynomial σ R →+* MvPolynomial σ R) (labeledAction k π)
  refine Eq.trans h ?_
  congr 1
  · exact RingHom.ext fun r => by simp
  · exact rename_labeledAction k π τ

/-- The product of the values at all labellings of the spectrum. -/
def actionValueProduct (Q : Polynomial R) (k : σ → R) : MvPolynomial σ R :=
  ∏ π : Equiv.Perm σ, actionValue Q k π

/-- **The product of the values at all labellings is symmetric.** -/
theorem isSymmetric_actionValueProduct (Q : Polynomial R) (k : σ → R) :
    MvPolynomial.IsSymmetric (actionValueProduct Q k) :=
  isSymmetric_prod_of_equivariant fun τ π => rename_actionValue Q k π τ

/-- **Hence it is a polynomial in the elementary symmetric functions.** -/
theorem exists_esymmAlgHom_actionValueProduct (Q : Polynomial R) (k : σ → R) :
    ∃ P : MvPolynomial (Fin (Fintype.card σ)) R,
      ((esymmAlgHom σ R (Fintype.card σ)) P : MvPolynomial σ R) = actionValueProduct Q k := by
  classical
  refine ⟨(esymmAlgEquiv σ R rfl).symm
    ⟨actionValueProduct Q k, isSymmetric_actionValueProduct Q k⟩, ?_⟩
  have h : (esymmAlgHom σ R (Fintype.card σ))
      ((esymmAlgEquiv σ R (n := Fintype.card σ) rfl).symm
        ⟨actionValueProduct Q k, isSymmetric_actionValueProduct Q k⟩)
      = ⟨actionValueProduct Q k, isSymmetric_actionValueProduct Q k⟩ := by
    simp_rw [esymmAlgEquiv, AlgEquiv.ofBijective_apply_symm_apply]
  exact congrArg Subtype.val h

variable {S : Type*} [CommRing S]

/-- **The evaluation of the symmetrised value product at a spectrum.** -/
theorem eval₂_actionValueProduct (f : R →+* S) (lam : σ → S) (Q : Polynomial R) (k : σ → R) :
    MvPolynomial.eval₂ f lam (actionValueProduct Q k)
      = ∏ π : Equiv.Perm σ, Polynomial.eval₂ f (∑ j, f (k j) * lam (π j)) Q := by
  have h1 : MvPolynomial.eval₂ f lam (actionValueProduct Q k)
      = ∏ π : Equiv.Perm σ, MvPolynomial.eval₂ f lam (actionValue Q k π) := by
    rw [actionValueProduct]
    exact map_prod (MvPolynomial.eval₂Hom f lam) _ _
  rw [h1]
  refine Finset.prod_congr rfl fun π _ => ?_
  have h2 := Polynomial.hom_eval₂ Q (MvPolynomial.C : R →+* MvPolynomial σ R)
    (MvPolynomial.eval₂Hom f lam) (labeledAction k π)
  rw [actionValue]
  refine Eq.trans h2 ?_
  congr 1
  · exact RingHom.ext fun r => by simp
  · rw [labeledAction, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    simp

/-- **The vanishing criterion.**  If the given polynomial vanishes at one labelled action value,
the symmetrised product vanishes at that spectrum. -/
theorem eval₂_actionValueProduct_eq_zero (f : R →+* S) (lam : σ → S) (Q : Polynomial R)
    (k : σ → R) (π₀ : Equiv.Perm σ)
    (h : Polynomial.eval₂ f (∑ j, f (k j) * lam (π₀ j)) Q = 0) :
    MvPolynomial.eval₂ f lam (actionValueProduct Q k) = 0 := by
  rw [eval₂_actionValueProduct]
  exact Finset.prod_eq_zero (Finset.mem_univ π₀) h

end

end GaloisForLFunctions.HTGeometry
