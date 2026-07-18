import GaloisForLFunctions.HTGeometry.BaseGaugeDifferentialIndependence
import GaloisForLFunctions.HTGeometry.UpperEndRationalCoordinateDifferentialAdjoin

/-!
# Affine coordinate gauges in the upper-end meromorphic field

Transforms attached to a measure are rarely presented in the exact normalization that a freeness
theorem is stated in.  Typically one has

```text
observed = a * canonical + b
```

with `a` and `b` rational in the coordinate and `a` nowhere zero.  This module discharges that
bookkeeping once and for all at the upper end: the embedded rational coordinate field is
derivation closed, hence carries the restricted derivation, and the abstract affine base gauge
therefore applies verbatim.

The consequence is that presenting a carrier through any invertible rational gauge neither creates
nor destroys differential independence over `ℂ(z)`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance upperEndAffineGaugeDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance upperEndAffineGaugeComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance upperEndAffineGaugeDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- The embedded rational coordinate field carries the restricted upper-end derivation. -/
local instance upperEndCoordinateFieldDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

/-- The restriction is compatible with the ambient derivation, so the coordinate field is a
differential subalgebra of the meromorphic field. -/
local instance upperEndCoordinateFieldDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    upperEndRationalCoordinateField
    upperEndRationalCoordinateField_derivationClosed x⟩

/-- **Upper-end rational gauge invariance.**  Presenting a family of upper-end carriers through an
invertible affine gauge with rational-coordinate coefficients does not change differential
independence over the embedded `ℂ(z)`. -/
theorem differentialIndependent_upperEnd_affineGauge_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → upperEndMeroField)
    (a b : ι → upperEndRationalCoordinateField) (ha : ∀ i, a i ≠ 0) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun i ↦ (a i : upperEndMeroField) * x i + (b i : upperEndMeroField)) ↔
      DifferentialIndependent upperEndRationalCoordinateField x :=
  differentialIndependent_affineBase_iff x a b ha

/-- Rank-one form: hypertranscendence over the embedded coordinate field is invariant under an
invertible affine rational gauge. -/
theorem hypertranscendentalOver_upperEnd_affineGauge_iff
    (x : upperEndMeroField)
    (a b : upperEndRationalCoordinateField) (ha : a ≠ 0) :
    HypertranscendentalOver upperEndRationalCoordinateField
        ((a : upperEndMeroField) * x + (b : upperEndMeroField)) ↔
      HypertranscendentalOver upperEndRationalCoordinateField x := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton,
    hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact differentialIndependent_upperEnd_affineGauge_iff
    (fun _ : Unit ↦ x) (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ ha)

end

end GaloisForLFunctions.HTGeometry
