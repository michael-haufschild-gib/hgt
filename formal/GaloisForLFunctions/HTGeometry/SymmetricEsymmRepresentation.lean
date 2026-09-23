/-
# Symmetric polynomials as polynomials in the elementary symmetric functions, in evaluable form

The fundamental theorem of symmetric polynomials is stated in mathlib through an algebra
isomorphism onto the symmetric subalgebra.  For the elimination step of a spectral tail one needs
it in the form actually used at a spectrum: a symmetric polynomial *is* a substitution of the
elementary symmetric functions into some polynomial, so its value at any spectrum is that
polynomial evaluated at the elementary symmetric functions of that spectrum.

Main results:
* `exists_bind₁_esymm_of_isSymmetric` — **the fundamental theorem as a substitution**.
* `eval₂_of_bind₁_esymm` — **hence the value at a spectrum is a polynomial in the elementary
  symmetric functions of the spectrum**.
* `exists_eval₂_esymm_repr_of_isSymmetric` — the two combined.
-/
import GaloisForLFunctions.HTGeometry.ActionValueProduct
import Mathlib.Algebra.MvPolynomial.Monad

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- **The fundamental theorem of symmetric polynomials, as a substitution.** -/
theorem exists_bind₁_esymm_of_isSymmetric (p : MvPolynomial σ R) (hp : p.IsSymmetric) :
    ∃ P : MvPolynomial (Fin (Fintype.card σ)) R,
      bind₁ (fun i : Fin (Fintype.card σ) => MvPolynomial.esymm σ R (i + 1)) P = p := by
  classical
  refine ⟨(esymmAlgEquiv σ R rfl).symm ⟨p, hp⟩, ?_⟩
  have h : (esymmAlgHom σ R (Fintype.card σ))
      ((esymmAlgEquiv σ R (n := Fintype.card σ) rfl).symm ⟨p, hp⟩) = ⟨p, hp⟩ := by
    simp_rw [esymmAlgEquiv, AlgEquiv.ofBijective_apply_symm_apply]
  have h' := congrArg Subtype.val h
  rw [esymmAlgHom_apply] at h'
  rw [← aeval_eq_bind₁]
  exact h'

variable {S : Type*} [CommRing S]

/-- **The value of a substituted polynomial at a spectrum.** -/
theorem eval₂_of_bind₁_esymm (f : R →+* S) (μ : σ → S)
    (P : MvPolynomial (Fin (Fintype.card σ)) R) :
    MvPolynomial.eval₂ f μ
        (bind₁ (fun i : Fin (Fintype.card σ) => MvPolynomial.esymm σ R (i + 1)) P)
      = MvPolynomial.eval₂ f
          (fun i : Fin (Fintype.card σ) =>
            MvPolynomial.eval₂ f μ (MvPolynomial.esymm σ R (i + 1))) P := by
  have h := MvPolynomial.eval₂Hom_bind₁ f μ
    (fun i : Fin (Fintype.card σ) => MvPolynomial.esymm σ R (i + 1)) P
  exact h

/-- **A symmetric polynomial evaluates at any spectrum to a fixed polynomial in the elementary
symmetric functions of that spectrum.** -/
theorem exists_eval₂_esymm_repr_of_isSymmetric (p : MvPolynomial σ R) (hp : p.IsSymmetric) :
    ∃ P : MvPolynomial (Fin (Fintype.card σ)) R, ∀ (f : R →+* S) (μ : σ → S),
      MvPolynomial.eval₂ f μ p
        = MvPolynomial.eval₂ f
            (fun i : Fin (Fintype.card σ) =>
              MvPolynomial.eval₂ f μ (MvPolynomial.esymm σ R (i + 1))) P := by
  obtain ⟨P, hP⟩ := exists_bind₁_esymm_of_isSymmetric p hp
  refine ⟨P, fun f μ => ?_⟩
  rw [← hP, eval₂_of_bind₁_esymm]

variable [DecidableEq σ]

/-- **The symmetrised action-value product is a polynomial in the elementary symmetric functions of
the spectrum, evaluated at that spectrum.** -/
theorem exists_eval₂_esymm_repr (Q : Polynomial R) (k : σ → R) :
    ∃ P : MvPolynomial (Fin (Fintype.card σ)) R, ∀ (f : R →+* S) (μ : σ → S),
      (∏ π : Equiv.Perm σ, Polynomial.eval₂ f (∑ j, f (k j) * μ (π j)) Q)
        = MvPolynomial.eval₂ f
            (fun i : Fin (Fintype.card σ) =>
              MvPolynomial.eval₂ f μ (MvPolynomial.esymm σ R (i + 1))) P := by
  obtain ⟨P, hP⟩ := exists_eval₂_esymm_repr_of_isSymmetric (S := S) (actionValueProduct Q k)
    (isSymmetric_actionValueProduct Q k)
  refine ⟨P, fun f μ => ?_⟩
  rw [← hP f μ, eval₂_actionValueProduct]

end

end GaloisForLFunctions.HTGeometry
