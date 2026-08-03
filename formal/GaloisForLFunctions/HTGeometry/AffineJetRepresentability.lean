import GaloisForLFunctions.HTGeometry.TruncatedArcCoordinates
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.CategoryTheory.Yoneda

/-!
# Representability of affine-space jet functors

For every commutative base ring `K`, variable type `ι`, and finite order `n`, the functor

`R ↦ Hom_K(K[X_i], R[t]/(t^(n+1)))`

on commutative `K`-algebras is corepresented by the polynomial algebra with variables
`(i,j) : ι × Fin (n+1)`.  The proof gives the natural equivalence explicitly and proves
base-change naturality.  Taking `Spec` produces the genuine affine jet scheme, whose function
field is therefore mathlib's scheme function field when the base is a field.
-/

open CategoryTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Order-`n` affine-space jets valued in a commutative `K`-algebra. -/
abbrev AffineSpaceJetPoint (K : Type u) [CommRing K] (ι : Type u)
    (n : ℕ) (R : CommAlgCat.{u} K) :=
  MvPolynomial ι K →ₐ[K] TruncatedArcAlgebra R n

/-- The functor of order-`n` affine-space jets on commutative `K`-algebras. -/
noncomputable def affineSpaceJetPointFunctor (K : Type u) [CommRing K] (ι : Type u)
    (n : ℕ) : CommAlgCat.{u} K ⥤ Type u where
  obj R := AffineSpaceJetPoint K ι n R
  map {R S} f := ↾fun φ : AffineSpaceJetPoint K ι n R =>
    (mapTruncatedArcAlgHom n f.hom).comp φ
  map_id R := by
    ext φ i
    change mapTruncatedArcAlgHom n (AlgHom.id K R) (φ (MvPolynomial.X i)) =
      φ (MvPolynomial.X i)
    rw [mapTruncatedArcAlgHom_id]
    rfl
  map_comp f g := by
    ext φ i
    change mapTruncatedArcAlgHom n (g.hom.comp f.hom) (φ (MvPolynomial.X i)) =
      mapTruncatedArcAlgHom n g.hom
        (mapTruncatedArcAlgHom n f.hom (φ (MvPolynomial.X i)))
    rw [← mapTruncatedArcAlgHom_comp]
    rfl

/-- Coordinate ring representing order-`n` jets of affine `ι`-space. -/
abbrev AffineSpaceJetCoordinateRing (K : Type u) [CommRing K] (ι : Type u) (n : ℕ) :=
  MvPolynomial (ι × Fin (n + 1)) K

/-- The natural pointwise equivalence underlying affine jet representability. -/
noncomputable def affineSpaceJetPointEquiv (K : Type u) [CommRing K]
    (ι : Type u) (n : ℕ) (R : CommAlgCat.{u} K) :
    (CommAlgCat.of K (AffineSpaceJetCoordinateRing K ι n) ⟶ R) ≃
      AffineSpaceJetPoint K ι n R where
  toFun ψ := MvPolynomial.aeval (fun i =>
    (truncatedArcCoordinateEquiv R n).symm (fun j => ψ.hom (MvPolynomial.X (i, j))))
  invFun φ := CommAlgCat.ofHom (MvPolynomial.aeval (fun ij =>
    truncatedArcCoordinateEquiv R n (φ (MvPolynomial.X ij.1)) ij.2))
  left_inv ψ := by
    ext ij
    simp
  right_inv φ := by
    apply MvPolynomial.algHom_ext
    intro i
    apply (truncatedArcCoordinateEquiv R n).injective
    ext j
    simp

@[simp]
theorem affineSpaceJetPointEquiv_apply_X (K : Type u) [CommRing K]
    (ι : Type u) (n : ℕ) (R : CommAlgCat.{u} K)
    (ψ : CommAlgCat.of K (AffineSpaceJetCoordinateRing K ι n) ⟶ R) (i : ι) :
    affineSpaceJetPointEquiv K ι n R ψ (MvPolynomial.X i) =
      (truncatedArcCoordinateEquiv R n).symm
        (fun j => ψ.hom (MvPolynomial.X (i, j))) := by
  simp [affineSpaceJetPointEquiv]

@[simp]
theorem affineSpaceJetPointFunctor_map_apply (K : Type u) [CommRing K]
    (ι : Type u) (n : ℕ) {R S : CommAlgCat.{u} K} (g : R ⟶ S)
    (φ : AffineSpaceJetPoint K ι n R) :
    (affineSpaceJetPointFunctor K ι n).map g φ =
      (mapTruncatedArcAlgHom n g.hom).comp φ := by
  rfl

/-- Base-change naturality of the affine jet point equivalence. -/
theorem affineSpaceJetPointEquiv_natural (K : Type u) [CommRing K]
    (ι : Type u) (n : ℕ) {R S : CommAlgCat.{u} K}
    (g : R ⟶ S) (f : CommAlgCat.of K (AffineSpaceJetCoordinateRing K ι n) ⟶ R) :
    affineSpaceJetPointEquiv K ι n S (f ≫ g) =
      (affineSpaceJetPointFunctor K ι n).map g (affineSpaceJetPointEquiv K ι n R f) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [affineSpaceJetPointEquiv_apply_X, affineSpaceJetPointFunctor_map_apply]
  simp only [AlgHom.comp_apply]
  rw [affineSpaceJetPointEquiv_apply_X]
  apply (truncatedArcCoordinateEquiv S n).injective
  ext j
  rw [LinearEquiv.apply_symm_apply]
  rw [truncatedArcCoordinateEquiv_map]
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- **Affine jet representability.** The affine-space jet functor is corepresented by its
explicit polynomial coordinate ring. -/
noncomputable def affineSpaceJetCorepresentable (K : Type u) [CommRing K]
    (ι : Type u) (n : ℕ) :
    (affineSpaceJetPointFunctor K ι n).CorepresentableBy
      (CommAlgCat.of K (AffineSpaceJetCoordinateRing K ι n)) where
  homEquiv := affineSpaceJetPointEquiv K ι n _
  homEquiv_comp := affineSpaceJetPointEquiv_natural K ι n

/-- The scheme representing order-`n` jets of affine `ι`-space. -/
abbrev AffineSpaceJetScheme (K : Type u) [CommRing K] (ι : Type u) (n : ℕ) :
    AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (.of (AffineSpaceJetCoordinateRing K ι n))

/-- Function field of the represented affine jet scheme over a field. -/
abbrev AffineSpaceJetFunctionField (K : Type u) [Field K] (ι : Type u) (n : ℕ) :=
  (AffineSpaceJetScheme K ι n).functionField

end

end GaloisForLFunctions.HTGeometry
