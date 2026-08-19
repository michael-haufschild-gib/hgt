/-
# Base change through the fundamental theorem of symmetric polynomials

The fundamental theorem writes a symmetric polynomial uniquely as a polynomial in the elementary
symmetric functions.  That representation is natural in the coefficient ring: changing the
coefficients by a ring homomorphism and then descending gives the same answer as descending and
then changing the coefficients.  Mathlib states the theorem but not its naturality.

The proof does not touch the construction of the inverse.  The forward substitution
`Xᵢ ↦ eᵢ₊₁` is visibly natural, because the elementary symmetric polynomials have coefficients
`1`; and the forward map is injective, being one half of an algebra equivalence.  So the two
candidate representatives have the same image and therefore coincide.

Applied to the labeling-orbit obstruction of the quadratic-rate relation, naturality is what lets
the rate be carried as a variable: the obstruction may be built once over a polynomial ring in the
Hamiltonian parameters and specialised afterwards, instead of being rebuilt at every parameter
value.

Main results:
* `map_esymmAlgEquiv_symm` — naturality of the symmetric-polynomial descent.
* `map_fieldQuadraticRateOrbitPolynomial`, `map_fieldQuadraticRateCoefficientPolynomial` — the
  labeling-orbit obstruction and its characteristic-coefficient form are natural.
-/
import GaloisForLFunctions.HTGeometry.QuadraticRateOrbitPolynomialField

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {σ : Type*} [Fintype σ] {R S : Type*} [CommRing R] [CommRing S]

/-- The substitution `Xᵢ ↦ eᵢ₊₁` is natural in the coefficient ring. -/
theorem map_esymmAlgHom (f : R →+* S) (F : MvPolynomial (Fin (Fintype.card σ)) R) :
    ((esymmAlgHom σ S (Fintype.card σ)) (MvPolynomial.map f F) : MvPolynomial σ S)
      = MvPolynomial.map f ((esymmAlgHom σ R (Fintype.card σ)) F : MvPolynomial σ R) := by
  rw [esymmAlgHom_apply, esymmAlgHom_apply, MvPolynomial.aeval_def, MvPolynomial.aeval_def,
    MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq]
  rw [MvPolynomial.eval₂_comp_left (MvPolynomial.map f) MvPolynomial.C
    (fun i : Fin (Fintype.card σ) => esymm σ R ((i : ℕ) + 1)) F]
  have hC : (MvPolynomial.map f).comp (MvPolynomial.C : R →+* MvPolynomial σ R)
      = (MvPolynomial.C : S →+* MvPolynomial σ S).comp f := by
    ext r
    simp
  have hg : (fun i : Fin (Fintype.card σ) => (MvPolynomial.map f) (esymm σ R ((i : ℕ) + 1)))
      = fun i : Fin (Fintype.card σ) => esymm σ S ((i : ℕ) + 1) := by
    funext i
    exact MvPolynomial.map_esymm σ R _ f
  rw [hC]
  rw [show ((MvPolynomial.map f) ∘ fun i : Fin (Fintype.card σ) => esymm σ R ((i : ℕ) + 1))
      = fun i : Fin (Fintype.card σ) => esymm σ S ((i : ℕ) + 1) from hg]
  exact MvPolynomial.eval₂_map f (fun i : Fin (Fintype.card σ) => esymm σ S ((i : ℕ) + 1))
    (MvPolynomial.C : S →+* MvPolynomial σ S) F

theorem injective_esymmAlgHom :
    Function.Injective (esymmAlgHom σ S (Fintype.card σ)) := by
  intro a b hab
  have h : (esymmAlgEquiv σ S (rfl : Fintype.card σ = Fintype.card σ)) a
      = (esymmAlgEquiv σ S (rfl : Fintype.card σ = Fintype.card σ)) b := hab
  exact (esymmAlgEquiv σ S (rfl : Fintype.card σ = Fintype.card σ)).injective h

/-- **Naturality of the symmetric-polynomial descent.**  Descending a symmetric polynomial to a
polynomial in the elementary symmetric functions commutes with any change of coefficients. -/
theorem map_esymmAlgEquiv_symm (f : R →+* S) (p : MvPolynomial σ R) (hp : p.IsSymmetric) :
    MvPolynomial.map f ((esymmAlgEquiv σ R (rfl : Fintype.card σ = Fintype.card σ)).symm ⟨p, hp⟩)
      = (esymmAlgEquiv σ S (rfl : Fintype.card σ = Fintype.card σ)).symm
          ⟨MvPolynomial.map f p, hp.map f⟩ := by
  refine injective_esymmAlgHom ?_
  refine Subtype.ext ?_
  rw [map_esymmAlgHom f]
  have hR : ((esymmAlgHom σ R (Fintype.card σ))
      ((esymmAlgEquiv σ R (rfl : Fintype.card σ = Fintype.card σ)).symm ⟨p, hp⟩)
        : MvPolynomial σ R) = p := by
    change ((esymmAlgEquiv σ R (rfl : Fintype.card σ = Fintype.card σ))
      ((esymmAlgEquiv σ R (rfl : Fintype.card σ = Fintype.card σ)).symm ⟨p, hp⟩) : _) = p
    rw [AlgEquiv.apply_symm_apply]
  have hS : ((esymmAlgHom σ S (Fintype.card σ))
      ((esymmAlgEquiv σ S (rfl : Fintype.card σ = Fintype.card σ)).symm
        ⟨MvPolynomial.map f p, hp.map f⟩) : MvPolynomial σ S) = MvPolynomial.map f p := by
    change ((esymmAlgEquiv σ S (rfl : Fintype.card σ = Fintype.card σ))
      ((esymmAlgEquiv σ S (rfl : Fintype.card σ = Fintype.card σ)).symm
        ⟨MvPolynomial.map f p, hp.map f⟩) : _) = MvPolynomial.map f p
    rw [AlgEquiv.apply_symm_apply]
  rw [hR, hS]

/-! ## The quadratic-rate obstruction carries its rate as a variable -/

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem map_fieldQuadraticRateRelationPolynomial (f : R →+* S) (c : I → R) (κ : R) :
    MvPolynomial.map f (fieldQuadraticRateRelationPolynomial c κ)
      = fieldQuadraticRateRelationPolynomial (fun i => f (c i)) (f κ) := by
  simp [fieldQuadraticRateRelationPolynomial]

theorem map_fieldQuadraticRateOrbitPolynomial (f : R →+* S) (c : I → R) (κ : R) :
    MvPolynomial.map f (fieldQuadraticRateOrbitPolynomial c κ)
      = fieldQuadraticRateOrbitPolynomial (fun i => f (c i)) (f κ) := by
  classical
  rw [fieldQuadraticRateOrbitPolynomial, fieldQuadraticRateOrbitPolynomial, map_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_rename, map_fieldQuadraticRateRelationPolynomial]

/-- **The characteristic-coefficient obstruction is natural in the coefficient ring.**  This is
what allows the quadratic rate to be built once as a variable and specialised afterwards. -/
theorem map_fieldQuadraticRateCoefficientPolynomial (f : R →+* S) (c : I → R) (κ : R) :
    MvPolynomial.map f (fieldQuadraticRateCoefficientPolynomial c κ)
      = fieldQuadraticRateCoefficientPolynomial (fun i => f (c i)) (f κ) := by
  rw [fieldQuadraticRateCoefficientPolynomial, map_esymmAlgEquiv_symm,
    fieldQuadraticRateCoefficientPolynomial]
  congr 1
  exact Subtype.ext (map_fieldQuadraticRateOrbitPolynomial f c κ)

end GaloisForLFunctions.HTGeometry
