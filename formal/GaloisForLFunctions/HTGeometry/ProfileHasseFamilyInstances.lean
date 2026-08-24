import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.AffinePointCoordinateHasse
import GaloisForLFunctions.HTGeometry.CompactAbelianCharacterHasse
import GaloisForLFunctions.HTGeometry.CompactIntervalMomentHasse
import GaloisForLFunctions.HTGeometry.FiniteTorusFourierHasse
import GaloisForLFunctions.HTGeometry.InfiniteTorusFourierHasse
import GaloisForLFunctions.HTGeometry.FinitePolydiskMomentHasse
import GaloisForLFunctions.HTGeometry.ABHN.PlaceEmbeddingHasse
import GaloisForLFunctions.HTGeometry.ABHN.HasseSeparation
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedBrauerDFinsuppHasse
import GaloisForLFunctions.HilbertMetric.PolynomialEvaluationHasse

/-!
# Reusable Hasse-family registrations

Faithful coordinate, character, moment, completion, scalar-extension, and restricted-Brauer
profiles are registered in the common `HasseFamily` interface. Two point-level principles are added:
finite-support Fourier characters reconstruct product-torus points, and mixed monomials reconstruct
finite-polydisk points.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory
open scoped ComplexConjugate TensorProduct

/-- Dependent-product coordinates form the tautological Hasse family. -/
def piCoordinateHasseFamily {ι : Type*} (A : ι → Type*) :
    HasseFamily ((i : ι) → A i) ι where
  Local := A
  profile := fun x => x
  profile_injective := fun _ _ h => h

/-- Pull a Hasse family back along an injective global parametrization. -/
def HasseFamily.pullbackInjective
    {G X ι : Type*} (H : HasseFamily G ι) (f : X → G)
    (hf : Function.Injective f) : HasseFamily X ι where
  Local := H.Local
  profile := fun x => H.profile (f x)
  profile_injective := fun _ _ h => hf (H.profile_injective h)

/-- Affine coordinate evaluation registered as a reusable Hasse family. -/
def affinePointCoordinateHasseFamily
    (C A : Type*) [CommRing C] [CommRing A] [Algebra C A] :
    HasseFamily (A →ₐ[C] C) A where
  Local := fun _ => C
  profile := affinePointEvaluationProfile C A
  profile_injective := affinePointEvaluationProfile_injective C A

/-- Real multivariate-polynomial evaluation registered as a reusable Hasse family. -/
def realMvPolynomialEvaluationHasseFamily (τ : Type*) :
    HasseFamily (MvPolynomial τ ℝ) (τ → ℝ) where
  Local := fun _ => ℝ
  profile := fun P x => MvPolynomial.eval x P
  profile_injective := by
    intro P Q h
    exact (GaloisForLFunctions.HilbertMetric.mvPolynomial_congr_evaluation_hasse_iff P Q).2
      (fun x => congrFun h x)

/-- Number-field embeddings into all completions form a dependent Hasse family. -/
def numberFieldPlaceEmbeddingHasseFamily
    (K : Type*) [Field K] [NumberField K] :
    HasseFamily K (GaloisForLFunctions.HTGeometry.ABHN.NumberFieldPlace K) where
  Local := fun v => GaloisForLFunctions.HTGeometry.ABHN.completion K v
  profile := GaloisForLFunctions.HTGeometry.ABHN.placeDiagonal K
  profile_injective := GaloisForLFunctions.HTGeometry.ABHN.placeDiagonal_injective K

/-- Rational-function embeddings into all completions form a dependent Hasse family. -/
def rationalFunctionPlaceEmbeddingHasseFamily
    (F : Type*) [Field F] [Finite F] :
    HasseFamily (RatFunc F)
      (GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlace F) where
  Local := GaloisForLFunctions.HTGeometry.ABHN.rationalFunctionCompletion F
  profile := GaloisForLFunctions.HTGeometry.ABHN.rationalFunctionPlaceDiagonal F
  profile_injective :=
    GaloisForLFunctions.HTGeometry.ABHN.rationalFunctionPlaceDiagonal_injective F

/-- Elements of any number-field algebra are detected after all completed scalar extensions. -/
def numberFieldAlgebraScalarExtensionHasseFamily
    (K : Type*) [Field K] [NumberField K]
    (A : Type*) [Ring A] [Algebra K A] :
    HasseFamily A (GaloisForLFunctions.HTGeometry.ABHN.NumberFieldPlace K) where
  Local := fun v => GaloisForLFunctions.HTGeometry.ABHN.completion K v ⊗[K] A
  profile := fun a v =>
    (Algebra.TensorProduct.includeRight : A →ₐ[K]
      GaloisForLFunctions.HTGeometry.ABHN.completion K v ⊗[K] A) a
  profile_injective := by
    intro a b h
    exact (GaloisForLFunctions.HTGeometry.ABHN.numberField_algebra_eq_iff_forall_localScalarExtension
      K A a b).2
      (fun v => congrFun h v)

/-- Elements of any `F(t)`-algebra are detected after all completed scalar extensions. -/
def rationalFunctionAlgebraScalarExtensionHasseFamily
    (F : Type*) [Field F] [Finite F]
    (A : Type*) [Ring A] [Algebra (RatFunc F) A] :
    HasseFamily A
      (GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlace F) where
  Local := fun v =>
    GaloisForLFunctions.HTGeometry.ABHN.rationalFunctionCompletion F v ⊗[RatFunc F] A
  profile := fun a v =>
    (Algebra.TensorProduct.includeRight : A →ₐ[RatFunc F]
      GaloisForLFunctions.HTGeometry.ABHN.rationalFunctionCompletion F v ⊗[RatFunc F] A) a
  profile_injective := by
    intro a b h
    exact (GaloisForLFunctions.HTGeometry.ABHN.rationalFunction_algebra_eq_iff_forall_localScalarExtension
      F A a b).2
      (fun v => congrFun h v)

/-- Restricted number-field local Brauer families are detected place by place. -/
def numberFieldRestrictedLocalBrauerHasseFamily
    (K : Type*) [Field K] [NumberField K] :
    HasseFamily
      (GaloisForLFunctions.HTGeometry.ABHN.RestrictedLocalBrauerClasses K)
      (GaloisForLFunctions.HTGeometry.ABHN.NumberFieldPlace K) where
  Local := fun v => BrauerGroup (GaloisForLFunctions.HTGeometry.ABHN.completion K v)
  profile := fun x v => x.toLocalBrauerClasses v
  profile_injective := by
    intro x y h
    exact (GaloisForLFunctions.HTGeometry.ABHN.numberFieldRestrictedLocalBrauer_congr_hasse_iff
      K x y).2
      (fun v => congrFun h v)

/-- Restricted `F(t)` local Brauer families are detected at finite places and infinity. -/
def rationalFunctionRestrictedLocalBrauerHasseFamily
    (F : Type*) [Field F] [Finite F] :
    HasseFamily
      (GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionRestrictedLocalBrauerClasses F)
      (GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlace F) where
  Local := fun v => BrauerGroup
    (GaloisForLFunctions.HTGeometry.ABHN.rationalFunctionCompletion F v)
  profile := fun x v => x.toLocalBrauerClasses v
  profile_injective := by
    intro x y h
    exact (GaloisForLFunctions.HTGeometry.ABHN.rationalFunctionRestrictedLocalBrauer_congr_hasse_iff
      F x y).2
      (fun v => congrFun h v)

/-- Compact-abelian unitary characters registered as a reusable Hasse family. -/
def compactAbelianCharacterHasseFamily
    (G : Type*) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] :
    HasseFamily G (GaloisForLFunctions.CompactAbelian.UnitaryContinuousCharacter G) where
  Local := fun _ => ℂ
  profile := GaloisForLFunctions.CompactAbelian.unitaryCharacterProfile G
  profile_injective := GaloisForLFunctions.CompactAbelian.unitaryCharacterProfile_injective

/-- Compact-interval probability moments registered as a reusable Hasse family. -/
def CompactIntervalDatum.probabilityMomentHasseFamily (I : CompactIntervalDatum) :
    HasseFamily (ProbabilityMeasure (Set.Icc I.lower I.upper)) ℕ where
  Local := fun _ => ℝ
  profile := I.probabilityMomentProfile
  profile_injective := I.probabilityMomentProfile_injective

/-- Finite-torus probability Fourier coefficients registered as a reusable Hasse family. -/
def finiteTorusProbabilityFourierHasseFamily
    (d : Type*) [Fintype d] :
    HasseFamily (ProbabilityMeasure (UnitAddTorus d)) (d → ℤ) where
  Local := fun _ => ℂ
  profile := finiteTorusProbabilityFourierProfile d
  profile_injective := finiteTorusProbabilityFourierProfile_injective d

/-- Product-torus probability Fourier coefficients registered as a reusable Hasse family. -/
def infiniteTorusProbabilityFourierHasseFamily
    (I : Type*) [Countable I] :
    HasseFamily (ProbabilityMeasure (I → UnitAddCircle)) (I →₀ ℤ) where
  Local := fun _ => ℂ
  profile := infiniteTorusProbabilityFourierProfile I
  profile_injective := infiniteTorusProbabilityFourierProfile_injective I

/-- Finite-polydisk probability mixed moments registered as a reusable Hasse family. -/
def finitePolydiskProbabilityMomentHasseFamily
    (d : Type*) [Fintype d] :
    HasseFamily (ProbabilityMeasure (d → ClosedComplexUnitDisk))
      ((d → ℕ) × (d → ℕ)) where
  Local := fun _ => ℂ
  profile := finitePolydiskProbabilityMomentProfile d
  profile_injective := finitePolydiskProbabilityMomentProfile_injective d

/-- Complete finite-support Fourier profile of a product-torus point. -/
def infiniteTorusPointFourierProfile (I : Type*) :
    (I → UnitAddCircle) → ((I →₀ ℤ) → ℂ) :=
  fun x n => infiniteTorusFourier n x

/-- Finite-support Fourier characters faithfully encode every product-torus point. -/
theorem infiniteTorusPointFourierProfile_injective (I : Type*) :
    Function.Injective (infiniteTorusPointFourierProfile I) := by
  intro x y h
  funext i
  have hi := congrFun h (Finsupp.single i 1)
  change infiniteTorusFourier (Finsupp.single i 1) x =
    infiniteTorusFourier (Finsupp.single i 1) y at hi
  rw [infiniteTorusFourier_single, infiniteTorusFourier_single,
    fourier_one, fourier_one, Subtype.coe_inj] at hi
  exact AddCircle.injective_toCircle one_ne_zero hi

/-- Product-torus point reconstruction as a Hasse family. -/
def infiniteTorusPointFourierHasseFamily (I : Type*) :
    HasseFamily (I → UnitAddCircle) (I →₀ ℤ) where
  Local := fun _ => ℂ
  profile := infiniteTorusPointFourierProfile I
  profile_injective := infiniteTorusPointFourierProfile_injective I

/-- Distinct product-torus points differ at one finite-support character. -/
theorem infiniteTorusPoint_ne_iff_exists_fourier_ne
    {I : Type*} (x y : I → UnitAddCircle) :
    x ≠ y ↔ ∃ n : I →₀ ℤ, infiniteTorusFourier n x ≠ infiniteTorusFourier n y :=
  (infiniteTorusPointFourierHasseFamily I).ne_iff_exists_local_ne x y

/-- Complete mixed-monomial profile of one finite-polydisk point. -/
def finitePolydiskPointMomentProfile (d : Type*) [Fintype d] :
    (d → ClosedComplexUnitDisk) → (((d → ℕ) × (d → ℕ)) → ℂ) :=
  fun x pq => finitePolydiskMoment pq.1 pq.2 x

/-- Mixed monomials faithfully encode each finite-polydisk point. -/
theorem finitePolydiskPointMomentProfile_injective
    (d : Type*) [Fintype d] :
    Function.Injective (finitePolydiskPointMomentProfile d) := by
  classical
  intro x y h
  funext i
  let p : d → ℕ := Pi.single i 1
  let q : d → ℕ := fun _ => 0
  have hmoment (z : d → ClosedComplexUnitDisk) :
      finitePolydiskMoment p q z = (z i : ℂ) := by
    change (∏ j, (z j : ℂ) ^ p j * conj (z j : ℂ) ^ q j) = (z i : ℂ)
    calc
      _ = (z i : ℂ) ^ p i * conj (z i : ℂ) ^ q i := by
        apply Finset.prod_eq_single i
        · intro j _ hji
          simp [p, q, hji]
        · simp
      _ = (z i : ℂ) := by simp [p, q]
  have hi := congrFun h (p, q)
  change finitePolydiskMoment p q x = finitePolydiskMoment p q y at hi
  rw [hmoment x, hmoment y] at hi
  exact Subtype.coe_injective hi

/-- Finite-polydisk point reconstruction as a Hasse family. -/
def finitePolydiskPointMomentHasseFamily
    (d : Type*) [Fintype d] :
    HasseFamily (d → ClosedComplexUnitDisk) ((d → ℕ) × (d → ℕ)) where
  Local := fun _ => ℂ
  profile := finitePolydiskPointMomentProfile d
  profile_injective := finitePolydiskPointMomentProfile_injective d

/-- Distinct finite-polydisk points differ at one mixed moment. -/
theorem finitePolydiskPoint_ne_iff_exists_moment_ne
    {d : Type*} [Fintype d] (x y : d → ClosedComplexUnitDisk) :
    x ≠ y ↔ ∃ pq : (d → ℕ) × (d → ℕ),
      finitePolydiskMoment pq.1 pq.2 x ≠ finitePolydiskMoment pq.1 pq.2 y :=
  (finitePolydiskPointMomentHasseFamily d).ne_iff_exists_local_ne x y

end

end GaloisForLFunctions.HTGeometry
