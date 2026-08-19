/-
# The symmetrised labeled spectral action is a polynomial in the elementary symmetric functions

A spectral action `∑_j k_j E_j` depends on the labelling of the spectrum.  Taking the product over
every labelling removes that dependence: the resulting polynomial in an auxiliary variable has
coefficients which are symmetric in the eigenvalues, hence -- by the fundamental theorem of
symmetric polynomials -- polynomials in the elementary symmetric functions, i.e. in the
characteristic coefficients of the Hamiltonian, i.e. in the shell coordinates.

This is the elimination step that turns statements about spectral actions into statements about
genuine polynomials in the coefficient vector.

Main results:
* `labeledAction`, `labeledActionPoly` — the labelled action and its symmetrisation.
* `rename_labeledAction` — relabelling the variables translates the labelling.
* `isSymmetric_coeff_labeledActionPoly` — **the coefficients are symmetric**.
* `exists_esymmAlgHom_coeff_labeledActionPoly` — **hence polynomials in the elementary symmetric
  functions**.
* `eval_map_labeledActionPoly` — **every labelled action value is a root**.
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.Perm

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

/-- The spectral action of a coefficient vector at one labelling of the spectrum. -/
def labeledAction (k : σ → R) (π : Equiv.Perm σ) : MvPolynomial σ R :=
  ∑ j, C (k j) * X (π j)

omit [DecidableEq σ] in
theorem rename_labeledAction (k : σ → R) (π τ : Equiv.Perm σ) :
    rename (τ : σ → σ) (labeledAction k π) = labeledAction k (τ * π) := by
  rw [labeledAction, labeledAction, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, rename_C, rename_X]
  rfl

/-- The symmetrised labelled action polynomial `∏_π (Y − ∑_j k_j X_{π j})`. -/
def labeledActionPoly (k : σ → R) : Polynomial (MvPolynomial σ R) :=
  ∏ π : Equiv.Perm σ, (Polynomial.X - Polynomial.C (labeledAction k π))

/-- Relabelling the variables permutes the factors, hence fixes the symmetrised polynomial. -/
theorem map_rename_labeledActionPoly (k : σ → R) (τ : Equiv.Perm σ) :
    Polynomial.map ((rename (τ : σ → σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) :
        MvPolynomial σ R →+* MvPolynomial σ R) (labeledActionPoly k)
      = labeledActionPoly k := by
  rw [labeledActionPoly, ← Polynomial.coe_mapRingHom, map_prod, Polynomial.coe_mapRingHom]
  have hfac : ∀ π : Equiv.Perm σ,
      Polynomial.map ((rename (τ : σ → σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) :
          MvPolynomial σ R →+* MvPolynomial σ R)
        (Polynomial.X - Polynomial.C (labeledAction k π))
        = Polynomial.X - Polynomial.C (labeledAction k (τ * π)) := by
    intro π
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 1
    congr 1
    exact rename_labeledAction k π τ
  rw [Finset.prod_congr rfl fun π _ => hfac π]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun π => rfl

/-- **Every coefficient of the symmetrised action polynomial is a symmetric polynomial.** -/
theorem isSymmetric_coeff_labeledActionPoly (k : σ → R) (m : ℕ) :
    MvPolynomial.IsSymmetric ((labeledActionPoly k).coeff m) := by
  intro τ
  have h := congrArg (fun p : Polynomial (MvPolynomial σ R) => p.coeff m)
    (map_rename_labeledActionPoly k τ)
  simpa [Polynomial.coeff_map] using h

/-- **The coefficients are polynomials in the elementary symmetric functions.** -/
theorem exists_esymmAlgHom_coeff_labeledActionPoly (k : σ → R) (m : ℕ) :
    ∃ Q : MvPolynomial (Fin (Fintype.card σ)) R,
      ((esymmAlgHom σ R (Fintype.card σ)) Q : MvPolynomial σ R)
        = (labeledActionPoly k).coeff m := by
  classical
  refine ⟨(esymmAlgEquiv σ R rfl).symm
    ⟨(labeledActionPoly k).coeff m, isSymmetric_coeff_labeledActionPoly k m⟩, ?_⟩
  have h : (esymmAlgHom σ R (Fintype.card σ))
      ((esymmAlgEquiv σ R (n := Fintype.card σ) rfl).symm
        ⟨(labeledActionPoly k).coeff m, isSymmetric_coeff_labeledActionPoly k m⟩)
      = ⟨(labeledActionPoly k).coeff m, isSymmetric_coeff_labeledActionPoly k m⟩ := by
    simp_rw [esymmAlgEquiv, AlgEquiv.ofBijective_apply_symm_apply]
  exact congrArg Subtype.val h

omit [DecidableEq σ] in
theorem eval_labeledAction (k lam : σ → R) (π : Equiv.Perm σ) :
    MvPolynomial.eval lam (labeledAction k π) = ∑ j, k j * lam (π j) := by
  rw [labeledAction, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- **Every labelled action value is a root of the symmetrised polynomial.** -/
theorem eval_map_labeledActionPoly (k lam : σ → R) (π₀ : Equiv.Perm σ) :
    Polynomial.eval (∑ j, k j * lam (π₀ j))
      (Polynomial.map (MvPolynomial.eval lam : MvPolynomial σ R →+* R) (labeledActionPoly k))
      = 0 := by
  rw [labeledActionPoly, ← Polynomial.coe_mapRingHom, map_prod, Polynomial.coe_mapRingHom,
    Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ π₀) ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, eval_labeledAction, sub_self]

end

end GaloisForLFunctions.HTGeometry
