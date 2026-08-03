import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Affine point separation and coaction stabilizers

Coordinate functions separate algebra-valued affine points.  For an affine coaction
`B → B ⊗ A` and a point `x : B → C`, the stabilizer of `x` among `A`-points is the zero
locus of the explicit coefficients `orbitMap x b - x b`.  Thus stabilizer closedness is a theorem,
not an assumption on an abstract action.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {C : Type u} {A : Type v} {B : Type w}
variable [CommRing C] [CommRing A] [CommRing B]
variable [Algebra C A] [Algebra C B]

/-- Zero locus of affine coordinate functions among `C`-valued points of `A`. -/
def affinePointZeroLocus (S : Set A) : Set (A →ₐ[C] C) :=
  {p | ∀ a ∈ S, p a = 0}

/-- Zariski-closed subsets of affine `C`-points, presented by coordinate equations. -/
def IsAffinePointZariskiClosed (Z : Set (A →ₐ[C] C)) : Prop :=
  ∃ S : Set A, Z = affinePointZeroLocus S

/-- Affine coordinate functions separate distinct `C`-valued points. -/
theorem affineCoordinate_separates_points {p q : A →ₐ[C] C} (hpq : p ≠ q) :
    ∃ a : A, p a ≠ q a := by
  contrapose! hpq
  exact AlgHom.ext hpq

/-- Specialize left tensor factor of a coaction at `x`, leaving its group-coordinate factor. -/
def affineCoactionOrbitMap (rho : B →ₐ[C] TensorProduct C B A) (x : B →ₐ[C] C) :
    B →ₐ[C] A :=
  (Algebra.TensorProduct.lid C A).toAlgHom.comp
    ((Algebra.TensorProduct.map x (AlgHom.id C A)).comp rho)

/-- Action on affine points induced by an affine coaction. -/
def affineCoactionAct (rho : B →ₐ[C] TensorProduct C B A)
    (x : B →ₐ[C] C) (g : A →ₐ[C] C) : B →ₐ[C] C :=
  g.comp (affineCoactionOrbitMap rho x)

/-- Coordinate equations cutting out the stabilizer of `x`. -/
def affineCoactionStabilizerEquations (rho : B →ₐ[C] TensorProduct C B A)
    (x : B →ₐ[C] C) : Set A :=
  Set.range fun b : B ↦
    affineCoactionOrbitMap rho x b - algebraMap C A (x b)

/-- Stabilizer of an affine point under the coaction. -/
def affineCoactionStabilizer (rho : B →ₐ[C] TensorProduct C B A)
    (x : B →ₐ[C] C) : Set (A →ₐ[C] C) :=
  {g | affineCoactionAct rho x g = x}

/-- A coaction stabilizer is exactly the zero locus of its explicit coefficient equations. -/
theorem affineCoactionStabilizer_eq_zeroLocus
    (rho : B →ₐ[C] TensorProduct C B A) (x : B →ₐ[C] C) :
    affineCoactionStabilizer rho x =
      affinePointZeroLocus (affineCoactionStabilizerEquations rho x) := by
  ext g
  constructor
  · intro hg a ha
    obtain ⟨b, rfl⟩ := ha
    have hb := AlgHom.congr_fun hg b
    change g (affineCoactionOrbitMap rho x b) = x b at hb
    rw [map_sub, g.commutes]
    exact sub_eq_zero.mpr hb
  · intro hg
    apply AlgHom.ext
    intro b
    have hb := hg
      (affineCoactionOrbitMap rho x b - algebraMap C A (x b)) ⟨b, rfl⟩
    change g (affineCoactionOrbitMap rho x b) = x b
    rw [map_sub, g.commutes] at hb
    exact sub_eq_zero.mp hb

/-- Stabilizers of affine coactions are Zariski closed on `C`-valued points. -/
theorem affineCoactionStabilizer_isZariskiClosed
    (rho : B →ₐ[C] TensorProduct C B A) (x : B →ₐ[C] C) :
    IsAffinePointZariskiClosed (affineCoactionStabilizer rho x) := by
  exact ⟨affineCoactionStabilizerEquations rho x,
    affineCoactionStabilizer_eq_zeroLocus rho x⟩

/-- Distinct points in an affine quotient are separated by a quotient coordinate. -/
theorem affineQuotientCoordinate_separates_points
    {Q : Type*} [CommRing Q] [Algebra C Q] {p q : Q →ₐ[C] C} (hpq : p ≠ q) :
    ∃ f : Q, p f ≠ q f :=
  affineCoordinate_separates_points hpq

end

end GaloisForLFunctions.HTGeometry
