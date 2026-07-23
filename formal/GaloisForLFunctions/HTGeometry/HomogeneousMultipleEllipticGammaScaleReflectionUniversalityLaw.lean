import GaloisForLFunctions.HTGeometry.HomogeneousMultipleEllipticGamma
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaHypertranscendence
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaInversion

/-!
# Homogeneous multiple elliptic-Gamma scale/reflection universality

The normalized rank-three-minor hypertranscendence and parity reflection theorems become a
common-scale covariant law after restoring the implicit base period. Reflection through the
physical period sum commutes with every nonzero simultaneous rescaling, while both scale orbits
carry the radial Ward derivative zero.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

local instance homogeneousMultipleEllipticGammaScaleReflectionUnivDomain :
    IsDomain (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTUnivDomain

local instance homogeneousMultipleEllipticGammaScaleReflectionComplexAlgebraAnalytic :
    Algebra ℂ (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraAnalytic

local instance homogeneousMultipleEllipticGammaScaleReflectionComplexAlgebraMero :
    Algebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraMero

local instance homogeneousMultipleEllipticGammaScaleReflectionMeroDifferential :
    Differential (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroDifferential

local instance homogeneousMultipleEllipticGammaScaleReflectionComplexDifferential :
    Differential ℂ :=
  multipleEllipticGammaHTComplexDifferential

local instance homogeneousMultipleEllipticGammaScaleReflectionMeroCharZero :
    CharZero (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroCharZero

local instance homogeneousMultipleEllipticGammaScaleReflectionComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexDifferentialAlgebra

local instance homogeneousMultipleEllipticGammaScaleReflectionCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  multipleEllipticGammaHTCoordinateDifferential

local instance homogeneousMultipleEllipticGammaScaleReflectionCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTCoordinateDifferentialAlgebra

/-- Reflection of the normalized multiple elliptic Gamma lifts exactly to the homogeneous chart,
with center equal to the sum of the unnormalized displayed periods. -/
theorem homogeneousMultipleEllipticGammaProduct_reflection
    {ι : Type} [Fintype ι]
    (ω₀ : ℂ) (ω : ι → ℂ) (z : ℂ) :
    homogeneousMultipleEllipticGammaProduct ω₀ ω ((∑ i, ω i) - z) =
      if Even (Fintype.card ι) then
        (homogeneousMultipleEllipticGammaProduct ω₀ ω z)⁻¹
      else homogeneousMultipleEllipticGammaProduct ω₀ ω z := by
  have hcenter : ((∑ i, ω i) - z) / ω₀ =
      (∑ i, ω i / ω₀) - z / ω₀ := by
    rw [sub_div, Finset.sum_div]
  rw [homogeneousMultipleEllipticGammaProduct,
    homogeneousMultipleEllipticGammaProduct, hcenter,
    multipleEllipticGammaProduct_reflection]

/-- Common nonzero rescaling commutes with homogeneous parity reflection. -/
theorem homogeneousMultipleEllipticGammaProduct_scaled_reflection
    {ι : Type} [Fintype ι]
    (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ) (ω : ι → ℂ) (z : ℂ) :
    homogeneousMultipleEllipticGammaProduct
        (c * ω₀) (fun i => c * ω i) (c * ((∑ i, ω i) - z)) =
      if Even (Fintype.card ι) then
        (homogeneousMultipleEllipticGammaProduct
          (c * ω₀) (fun i => c * ω i) (c * z))⁻¹
      else
        homogeneousMultipleEllipticGammaProduct
          (c * ω₀) (fun i => c * ω i) (c * z) := by
  rw [homogeneousMultipleEllipticGammaProduct_scale c hc,
    homogeneousMultipleEllipticGammaProduct_scale c hc]
  exact homogeneousMultipleEllipticGammaProduct_reflection ω₀ ω z

/-- **Homogeneous multiple elliptic-Gamma scale/reflection universality law.** A rank-three minor
in the normalized period ratios forces hypertranscendence of both meromorphic carriers. In the
restored homogeneous chart, every nonzero common rescaling commutes with parity reflection through
the physical period sum, and both reflected and unreflected scale orbits have zero radial Ward
derivative. -/
theorem homogeneousMultipleEllipticGamma_scaleReflectionHypertranscendenceUniversality
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (ω₀ : ℂ) (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i / ω₀).im)
    (hminor : MultipleEllipticGammaHasRankThreeMinor (fun i => ω i / ω₀)) :
    HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaMero (fun i => ω i / ω₀) hω) ∧
      HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaLogDerivMero (fun i => ω i / ω₀) hω) ∧
      (∀ (c : ℂ), c ≠ 0 → ∀ z : ℂ,
        homogeneousMultipleEllipticGammaProduct
            (c * ω₀) (fun i => c * ω i) (c * ((∑ i, ω i) - z)) =
          if Even (Fintype.card ι) then
            (homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i) (c * z))⁻¹
          else
            homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i) (c * z)) ∧
      (∀ z : ℂ,
        HasDerivAt
            (fun c : ℂ => homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i) (c * z))
            0 1 ∧
          HasDerivAt
            (fun c : ℂ => homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i) (c * ((∑ i, ω i) - z)))
            0 1) := by
  refine ⟨
    hypertranscendentalOver_multipleEllipticGammaMero_of_rankThreeMinor
      (fun i => ω i / ω₀) hω hminor,
    hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_rankThreeMinor
      (fun i => ω i / ω₀) hω hminor,
    ?_, ?_⟩
  · intro c hc z
    exact homogeneousMultipleEllipticGammaProduct_scaled_reflection c hc ω₀ ω z
  · intro z
    exact ⟨
      hasDerivAt_homogeneousMultipleEllipticGammaProduct_scaleOrbit ω₀ ω z,
      hasDerivAt_homogeneousMultipleEllipticGammaProduct_scaleOrbit
        ω₀ ω ((∑ i, ω i) - z)⟩

end

end GaloisForLFunctions
