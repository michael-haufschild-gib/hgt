import GaloisForLFunctions.RepresentationLifting.ScalarCohomologySplitting
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.SymmetricSquareCharacteristicTwo

/-!
# Cohomology of binary symmetric squares in characteristic two

The binary quadratic matrices define an actual representation. Their pure-square
plane is the Frobenius twist, and their mixed-coordinate quotient is the determinant
character. The resulting short exact sequence gives a connecting homomorphism:
a determinant-valued cohomology class lifts precisely when its image vanishes.

Over a field, the three-dimensional symmetric square also has a trace retraction
from endomorphism-valued cohomology to scalar cohomology in every degree. These
apply the quadratic sequence and trace mechanisms of Scavia §3.1 and Lemma 6.1
to the symmetric-square matrices used for arithmetic correspondences.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open RepresentationLifting

universe u

section Ring

variable {k G : Type u} [CommRing k] [CharP k 2] [Group G]

/-- The action on the three coefficients of a binary quadratic product. -/
def binarySymmetricSquareRepresentation (ρ : G →* Matrix (Fin 2) (Fin 2) k) :
    Representation k G (Fin 3 → k) where
  toFun g := Matrix.toLin' (HTGeometry.symmetricSquareMatrix (ρ g))
  map_one' := by
    rw [map_one, HTGeometry.symmetricSquareMatrix_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, HTGeometry.symmetricSquareMatrix_mul, Matrix.toLin'_mul]
    rfl

/-- The action obtained by squaring each matrix coefficient. -/
def binaryFrobeniusRepresentation (ρ : G →* Matrix (Fin 2) (Fin 2) k) :
    Representation k G (Fin 2 → k) where
  toFun g := Matrix.toLin' ((ρ g).map (frobenius k 2))
  map_one' := by
    have hone : (1 : Matrix (Fin 2) (Fin 2) k).map (frobenius k 2) = 1 :=
      (frobenius k 2).mapMatrix.map_one
    rw [map_one, hone, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

/-- The one-dimensional determinant character. -/
def binaryDeterminantRepresentation (ρ : G →* Matrix (Fin 2) (Fin 2) k) :
    Representation k G k where
  toFun g := (ρ g).det • LinearMap.id
  map_one' := by
    rw [map_one, Matrix.det_one, one_smul]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro a
    change (ρ (g * h)).det * a = (ρ g).det * ((ρ h).det * a)
    rw [map_mul, Matrix.det_mul, mul_assoc]

/-- The pure-square plane embeds equivariantly in the symmetric square. -/
def binarySquareInclusion (ρ : G →* Matrix (Fin 2) (Fin 2) k) :
    Rep.of (binaryFrobeniusRepresentation ρ) ⟶
      Rep.of (binarySymmetricSquareRepresentation ρ) :=
  Rep.ofHom ⟨binarySquareDiagonal, fun g => by
    apply LinearMap.ext
    intro x
    exact (binarySquareDiagonal_intertwines (ρ g) x).symm⟩

/-- The mixed coefficient is an equivariant map to the determinant character. -/
def binaryMixedQuotient (ρ : G →* Matrix (Fin 2) (Fin 2) k) :
    Rep.of (binarySymmetricSquareRepresentation ρ) ⟶
      Rep.of (binaryDeterminantRepresentation ρ) :=
  Rep.ofHom ⟨binaryMixed, fun g => by
    apply LinearMap.ext
    intro v
    exact binaryMixed_intertwines (ρ g) v⟩

/-- The Frobenius-plane and determinant-quotient sequence of representations. -/
def binarySymmetricSquareComplex (ρ : G →* Matrix (Fin 2) (Fin 2) k) :
    ShortComplex (Rep k G) :=
  ShortComplex.mk (binarySquareInclusion ρ) (binaryMixedQuotient ρ) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl)

/-- The sequence is short exact over every commutative ring of characteristic two. -/
theorem binarySymmetricSquare_shortExact (ρ : G →* Matrix (Fin 2) (Fin 2) k) :
    (binarySymmetricSquareComplex ρ).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (binarySquareDiagonal_exact (R := k)).2.1
  · rw [Rep.mono_iff_injective]
    exact (binarySquareDiagonal_exact (R := k)).1
  · rw [Rep.epi_iff_surjective]
    exact (binarySquareDiagonal_exact (R := k)).2.2

/-- The connecting map from determinant cohomology to Frobenius-twisted cohomology. -/
def binaryFrobeniusConnecting (ρ : G →* Matrix (Fin 2) (Fin 2) k) (n : ℕ) :
    groupCohomology (Rep.of (binaryDeterminantRepresentation ρ)) n ⟶
      groupCohomology (Rep.of (binaryFrobeniusRepresentation ρ)) (n + 1) :=
  groupCohomology.δ (binarySymmetricSquare_shortExact ρ) n (n + 1) rfl

/-- The connecting class is the exact obstruction to lifting through the symmetric square. -/
theorem binaryDeterminantClass_lifts_iff (ρ : G →* Matrix (Fin 2) (Fin 2) k) (n : ℕ)
    (c : groupCohomology (Rep.of (binaryDeterminantRepresentation ρ)) n) :
    (∃ b : groupCohomology (Rep.of (binarySymmetricSquareRepresentation ρ)) n,
      ((groupCohomology.functor k G n).map (binaryMixedQuotient ρ)).hom b = c) ↔
      (binaryFrobeniusConnecting ρ n).hom c = 0 := by
  have hexact := (groupCohomology.mapShortComplex₃_exact
    (binarySymmetricSquare_shortExact ρ) (show n + 1 = n + 1 from rfl)).moduleCat_range_eq_ker
  change LinearMap.range ((groupCohomology.functor k G n).map (binaryMixedQuotient ρ)).hom =
    LinearMap.ker (binaryFrobeniusConnecting ρ n).hom at hexact
  constructor
  · intro hc
    have h : c ∈ LinearMap.range
        ((groupCohomology.functor k G n).map (binaryMixedQuotient ρ)).hom := hc
    rw [hexact] at h
    exact h
  · intro hc
    have h : c ∈ LinearMap.ker (binaryFrobeniusConnecting ρ n).hom := hc
    rw [← hexact] at h
    exact h

end Ring

section Field

variable {k G : Type u} [Field k] [CharP k 2] [Group G]

/-- Trace retracts the scalar inclusion for every binary symmetric-square representation. -/
theorem binarySymmetricSquare_cohomology_trace (ρ : G →* Matrix (Fin 2) (Fin 2) k) (n : ℕ) :
    (groupCohomology.functor k G n).map
        (scalarHom (𝟙 (Rep.of (binarySymmetricSquareRepresentation ρ)))) ≫
        (groupCohomology.functor k G n).map
          (endomorphismTrace (Rep.of (binarySymmetricSquareRepresentation ρ))) =
      𝟙 (groupCohomology (Rep.trivial k G k) n) :=
  oddDimensionalRepresentation_cohomology_trace 1 (binarySymmetricSquareRepresentation ρ) n

/-- Scalar cohomology embeds into endomorphism cohomology of the binary symmetric square. -/
theorem binarySymmetricSquare_scalar_injective (ρ : G →* Matrix (Fin 2) (Fin 2) k) (n : ℕ) :
    Function.Injective ((groupCohomology.functor k G n).map
      (scalarHom (𝟙 (Rep.of (binarySymmetricSquareRepresentation ρ))))).hom :=
  oddDimensionalRepresentation_scalar_injective 1 (binarySymmetricSquareRepresentation ρ) n
end Field

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.binarySymmetricSquare_shortExact
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.binaryDeterminantClass_lifts_iff
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.binarySymmetricSquare_scalar_injective
