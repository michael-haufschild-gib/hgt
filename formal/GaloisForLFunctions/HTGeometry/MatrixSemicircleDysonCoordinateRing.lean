import GaloisForLFunctions.HTGeometry.MatrixSemicircleDysonInfinityChart
import GaloisForLFunctions.HTGeometry.MvPolynomialPointEvaluationIdeal
import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Coordinate ring of the matrix-semicircle Dyson system at infinity

The rescaled square Dyson system is placed over the polynomial base `ℂ[u]`. Its distinguished
point over `u = 0` is maximal and is the only prime in that fiber. Consequently the finite-type
coordinate ring is quasi-finite over `ℂ[u]` at the physical infinity point. This implements the
corrected local algebraic-geometric step in the matrix-semicircle algebraicity argument.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]

/-- Entries of the identity point in the rescaled Dyson fiber. -/
def matrixDysonIdentityEntry (ij : I × I) : ℂ :=
  if ij.1 = ij.2 then 1 else 0

/-- Quadratic Dyson coordinate after separating `u` as the polynomial-base variable. -/
def matrixDysonInfinityBaseQuadratic (A : K → Matrix I I ℂ) (ij : I × I) :
    MvPolynomial (I × I) (Polynomial ℂ) :=
  MvPolynomial.optionEquivRight ℂ (I × I)
    (matrixDysonQuadraticPolynomial A ij.1 ij.2)

/-- Relation `Hᵢⱼ - δᵢⱼ - u (η(H)H)ᵢⱼ` over `ℂ[u]`. -/
def matrixDysonInfinityBaseRelation (A : K → Matrix I I ℂ) (ij : I × I) :
    MvPolynomial (I × I) (Polynomial ℂ) :=
  MvPolynomial.X ij -
    MvPolynomial.C (Polynomial.C (matrixDysonIdentityEntry ij)) -
    MvPolynomial.C Polynomial.X * matrixDysonInfinityBaseQuadratic A ij

def matrixDysonInfinityRelationIdeal (A : K → Matrix I I ℂ) :
    Ideal (MvPolynomial (I × I) (Polynomial ℂ)) :=
  Ideal.span (Set.range (matrixDysonInfinityBaseRelation A))

/-- Affine coordinate ring of the rescaled Dyson variety. -/
abbrev MatrixDysonInfinityCoordinateRing (A : K → Matrix I I ℂ) :=
  MvPolynomial (I × I) (Polynomial ℂ) ⧸ matrixDysonInfinityRelationIdeal A

/-- Ambient evaluation at `u=0`, `H=I`. -/
def matrixDysonInfinityAmbientAugmentation :
    MvPolynomial (I × I) (Polynomial ℂ) →+* ℂ :=
  mvPolynomialBaseZeroPointEval (matrixDysonIdentityEntry (I := I))

@[simp] lemma matrixDysonInfinityAmbientAugmentation_relation
    (A : K → Matrix I I ℂ) (ij : I × I) :
    matrixDysonInfinityAmbientAugmentation
      (matrixDysonInfinityBaseRelation A ij) = 0 := by
  simp [matrixDysonInfinityAmbientAugmentation, matrixDysonInfinityBaseRelation,
    mvPolynomialBaseZeroPointEval]

/-- Augmentation of the coordinate ring at the infinity point. -/
def matrixDysonInfinityAugmentation (A : K → Matrix I I ℂ) :
    MatrixDysonInfinityCoordinateRing A →+* ℂ :=
  Ideal.Quotient.lift (matrixDysonInfinityRelationIdeal A)
    matrixDysonInfinityAmbientAugmentation (by
      intro f hf
      change f ∈ RingHom.ker matrixDysonInfinityAmbientAugmentation
      apply (Ideal.span_le.2 ?_) hf
      rintro _ ⟨ij, rfl⟩
      exact matrixDysonInfinityAmbientAugmentation_relation A ij)

lemma matrixDysonInfinityAugmentation_surjective (A : K → Matrix I I ℂ) :
    Function.Surjective (matrixDysonInfinityAugmentation A) := by
  intro c
  refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C (Polynomial.C c)), ?_⟩
  simp [matrixDysonInfinityAugmentation, matrixDysonInfinityAmbientAugmentation,
    mvPolynomialBaseZeroPointEval]

/-- Prime ideal of the distinguished infinity point. -/
def matrixDysonInfinityPointPrime (A : K → Matrix I I ℂ) :
    Ideal (MatrixDysonInfinityCoordinateRing A) :=
  RingHom.ker (matrixDysonInfinityAugmentation A)

instance matrixDysonInfinityPointPrime_isPrime (A : K → Matrix I I ℂ) :
    (matrixDysonInfinityPointPrime A).IsPrime :=
  RingHom.ker_isPrime _

theorem matrixDysonInfinityPointPrime_isMaximal (A : K → Matrix I I ℂ) :
    (matrixDysonInfinityPointPrime A).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (matrixDysonInfinityAugmentation_surjective A)

/-- Every prime of the coordinate ring over the base point `u=0` is the identity point. -/
theorem matrixDysonInfinity_prime_eq_point
    (A : K → Matrix I I ℂ)
    (q : Ideal (MatrixDysonInfinityCoordinateRing A)) [q.IsPrime]
    (hq : q.under (Polynomial ℂ) =
      (matrixDysonInfinityPointPrime A).under (Polynomial ℂ)) :
    q = matrixDysonInfinityPointPrime A := by
  let Q : Ideal (MvPolynomial (I × I) (Polynomial ℂ)) :=
    q.comap (Ideal.Quotient.mk (matrixDysonInfinityRelationIdeal A))
  have hpX : Polynomial.X ∈
      (matrixDysonInfinityPointPrime A).under (Polynomial ℂ) := by
    change matrixDysonInfinityAugmentation A
      (Ideal.Quotient.mk (matrixDysonInfinityRelationIdeal A)
        (MvPolynomial.C Polynomial.X)) = 0
    unfold matrixDysonInfinityAugmentation
    rw [Ideal.Quotient.lift_mk]
    simp [matrixDysonInfinityAmbientAugmentation, mvPolynomialBaseZeroPointEval]
  have hqX : Polynomial.X ∈ q.under (Polynomial ℂ) := by rw [hq]; exact hpX
  have hu : MvPolynomial.C Polynomial.X ∈ Q := by
    change Ideal.Quotient.mk (matrixDysonInfinityRelationIdeal A)
      (MvPolynomial.C Polynomial.X) ∈ q
    change algebraMap (Polynomial ℂ) (MatrixDysonInfinityCoordinateRing A)
      Polynomial.X ∈ q
    exact hqX
  have hcoord : ∀ ij : I × I,
      MvPolynomial.X ij -
        MvPolynomial.C (Polynomial.C (matrixDysonIdentityEntry ij)) ∈ Q := by
    intro ij
    have hrelIdeal : matrixDysonInfinityBaseRelation A ij ∈
        matrixDysonInfinityRelationIdeal A :=
      Ideal.subset_span (Set.mem_range_self ij)
    have hrel : matrixDysonInfinityBaseRelation A ij ∈ Q := by
      change Ideal.Quotient.mk (matrixDysonInfinityRelationIdeal A)
        (matrixDysonInfinityBaseRelation A ij) ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hrelIdeal]
      exact q.zero_mem
    have hterm := Q.mul_mem_right (matrixDysonInfinityBaseQuadratic A ij) hu
    have hadd := Q.add_mem hrel hterm
    (convert hadd using 1; simp [matrixDysonInfinityBaseRelation])
  refine ((matrixDysonInfinityPointPrime_isMaximal A).eq_of_le
    (Ideal.IsPrime.ne_top' (I := q)) ?_).symm
  intro s hs
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
  change f ∈ Q
  apply mvPolynomial_mem_of_baseZeroPointEval_eq_zero
    (matrixDysonIdentityEntry (I := I)) Q hu hcoord
  simpa [matrixDysonInfinityPointPrime, matrixDysonInfinityAugmentation,
    matrixDysonInfinityAmbientAugmentation] using hs

attribute [-instance] Ideal.Quotient.commSemiring in
set_option maxHeartbeats 800000 in
/-- The rescaled Dyson variety is quasi-finite over its parameter line at the infinity point. -/
theorem matrixDysonInfinity_quasiFiniteAt_point
    (A : K → Matrix I I ℂ) :
    Algebra.QuasiFiniteAt (S := MatrixDysonInfinityCoordinateRing A)
      (Polynomial ℂ) (matrixDysonInfinityPointPrime A) := by
  letI : Algebra (Polynomial ℂ) (MatrixDysonInfinityCoordinateRing A) := inferInstance
  let x : PrimeSpectrum (MatrixDysonInfinityCoordinateRing A) :=
    ⟨matrixDysonInfinityPointPrime A, inferInstance⟩
  change Algebra.QuasiFiniteAt (S := MatrixDysonInfinityCoordinateRing A)
    (Polynomial ℂ) x.asIdeal
  refine Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber
    (R := Polynomial ℂ) (q := x) ?_
  have hset : ({⟨x, by simp⟩} : Set
      (PrimeSpectrum.comap
        (algebraMap (Polynomial ℂ) (MatrixDysonInfinityCoordinateRing A)) ⁻¹' {
          x.comap (algebraMap (Polynomial ℂ) (MatrixDysonInfinityCoordinateRing A))})) =
      Set.univ := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
    apply Subtype.ext
    apply PrimeSpectrum.ext
    apply matrixDysonInfinity_prime_eq_point A y.1.asIdeal
    exact congrArg PrimeSpectrum.asIdeal y.2
  rw [hset]
  exact isOpen_univ

attribute [-instance] Ideal.Quotient.commSemiring in
set_option maxHeartbeats 800000 in
/-- Zariski's Main Theorem supplies one nonvanishing integral multiplier which makes every
coordinate-ring element integral over the spectral parameter ring. -/
theorem matrixDysonInfinity_exists_integral_multiplier
    (A : K → Matrix I I ℂ) :
    ∃ r : MatrixDysonInfinityCoordinateRing A,
      r ∉ matrixDysonInfinityPointPrime A ∧
      ∀ x : MatrixDysonInfinityCoordinateRing A, ∃ m : ℕ,
        IsIntegral (Polynomial ℂ) (r ^ m * x) := by
  letI : Algebra (Polynomial ℂ) (MatrixDysonInfinityCoordinateRing A) := inferInstance
  letI : Algebra.QuasiFiniteAt (S := MatrixDysonInfinityCoordinateRing A)
      (Polynomial ℂ) (matrixDysonInfinityPointPrime A) :=
    matrixDysonInfinity_quasiFiniteAt_point A
  exact Algebra.zariskisMainProperty_iff'.mp
    (Algebra.ZariskisMainProperty.of_finiteType
      (R := Polynomial ℂ) (S := MatrixDysonInfinityCoordinateRing A)
      (matrixDysonInfinityPointPrime A))

end

end GaloisForLFunctions.HTGeometry
