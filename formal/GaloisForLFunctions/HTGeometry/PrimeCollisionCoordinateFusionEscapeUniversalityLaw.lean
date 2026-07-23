import GaloisForLFunctions.HTGeometry.PrimeCollisionConvolution
import GaloisForLFunctions.HTGeometry.PrimeValuationCoordinateFusionCompletion

/-!
# Prime-collision coordinate-fusion escape universality

Prime-valuation fusion is the same-prime collision projection of native Dirichlet convolution.
Substituting this coefficient identity into the coordinate-relative completion theorem shows that
two carriers already present in a finite depth field have a native convolution collision component
equal to the next carrier, which is differentially transcendental over that field.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Module
open scoped Differential

noncomputable section

universe u

local instance nativeCollisionUpperEndAnalyticDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance nativeCollisionUpperEndMeroComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance nativeCollisionUpperEndMeroDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance nativeCollisionComplexDifferential : Differential ℂ where
  deriv := 0

local instance nativeCollisionUpperEndComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ upperEndMeroField :=
  ⟨fun c => by
    rw [upperEndMero_deriv_complexConstant c]
    change (0 : upperEndMeroField) = algebraMap ℂ upperEndMeroField 0
    rw [map_zero]⟩

local instance nativeCollisionCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  GaloisForLFunctions.derivationClosedDifferential
    upperEndRationalCoordinateField upperEndRationalCoordinateField_derivationClosed

local instance nativeCollisionCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

/-- Native Dirichlet convolution followed by same-prime layer projection is pointwise residue
multiplication on the next valuation layer. -/
theorem primePowerLayerProjection_mul_primeResidueValuationObservableColumns
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)]
    (y : Nat.Primes → ∀ i, A i) (e r : ℕ)
    (f g : FullValueSubtype (∀ i, A i) → ℂ) :
    primePowerLayerProjection (e + r + 1)
        (primeResidueValuationObservableColumn A y e f *
          primeResidueValuationObservableColumn A y r g) =
      primeResidueValuationObservableColumn A y (e + r + 1) (f * g) := by
  calc
    primePowerLayerProjection (e + r + 1)
        (primeResidueValuationObservableColumn A y e f *
          primeResidueValuationObservableColumn A y r g) =
        primeValuationFusion e r
          (primeResidueValuationObservableColumn A y e f)
          (primeResidueValuationObservableColumn A y r g) := by
      simpa [primeResidueValuationObservableColumn] using
        (primePowerLayerProjection_mul_columns e r
          (fun p => f ⟨y p, Set.mem_univ _⟩)
          (fun p => g ⟨y p, Set.mem_univ _⟩))
    _ = primeResidueValuationObservableColumn A y (e + r + 1) (f * g) :=
      primeResidueValuationObservableColumn_fusion A y e r f g

/-- **Native collision escape law.**  Every finite coordinate-relative valuation prefix contains
the depth-`n` carrier and neutral depth-zero carrier, but the same-prime component of their native
Dirichlet convolution is exactly the next carrier and lies outside the prefix field. -/
theorem cofiniteTailDenseOn_primeResidueValuation_nativeCollision_escapes_coordinatePrefix
    (n : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    GaloisForLFunctions.DifferentialIndependent
        (primeResidueValuationUpperEndCoordinateDepthPrefixField n A y)
        (primeResidueValuationUpperEndNextLayerCarrier (n := n) A y) ∧
      Nat.card (PrimeResidueValuationNextLayerIndex n A) =
        ∏ i, Fintype.card (A i) ∧
      primeResidueValuationUpperEndCoordinateDepthPrefixField n A y <
        primeResidueValuationUpperEndCoordinateDepthPrefixField (n + 1) A y ∧
      ∀ z : ∀ i, A i,
        primeResidueValuationUpperEndCarrier A y n z ∈
            primeResidueValuationUpperEndCoordinateDepthPrefixField n A y ∧
          primeResidueValuationUpperEndCarrier A y 0 (fun _ => 1) ∈
            primeResidueValuationUpperEndCoordinateDepthPrefixField n A y ∧
          primePowerLayerProjection (n + 1)
              (primeResidueValuationObservableColumn A y n
                  (anchoredRestrictedProductBasis A z) *
                primeResidueValuationObservableColumn A y 0
                  (anchoredRestrictedProductBasis A (fun _ => 1))) =
            primeResidueValuationObservableColumn A y (n + 1)
              (anchoredRestrictedProductBasis A z) ∧
          primeResidueValuationUpperEndCarrier A y (n + 1) z ∉
            primeResidueValuationUpperEndCoordinateDepthPrefixField n A y := by
  obtain ⟨hnext, hrank, hstrict, hcreation⟩ :=
    cofiniteTailDenseOn_primeResidueValuationUpperEndCoordinateVacuumCreationLaw
      n A y hy
  refine ⟨hnext, hrank, hstrict, ?_⟩
  intro z
  obtain ⟨hn, hzero, hfusion, hout⟩ := hcreation z
  refine ⟨hn, hzero, ?_, hout⟩
  calc
    primePowerLayerProjection (n + 1)
        (primeResidueValuationObservableColumn A y n
            (anchoredRestrictedProductBasis A z) *
          primeResidueValuationObservableColumn A y 0
            (anchoredRestrictedProductBasis A (fun _ => 1))) =
        primeValuationFusion n 0
          (primeResidueValuationObservableColumn A y n
            (anchoredRestrictedProductBasis A z))
          (primeResidueValuationObservableColumn A y 0
            (anchoredRestrictedProductBasis A (fun _ => 1))) := by
      simpa [primeResidueValuationObservableColumn] using
        (primePowerLayerProjection_mul_columns n 0
          (fun p => anchoredRestrictedProductBasis A z
            ⟨y p, Set.mem_univ _⟩)
          (fun p => anchoredRestrictedProductBasis A (fun _ => 1)
            ⟨y p, Set.mem_univ _⟩))
    _ = primeResidueValuationObservableColumn A y (n + 1)
          (anchoredRestrictedProductBasis A z) := hfusion

end

end GaloisForLFunctions.HTGeometry
