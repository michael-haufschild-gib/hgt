import GaloisForLFunctions.HTGeometry.HerglotzUpperEndCarrier
import GaloisForLFunctions.HTGeometry.UpperEndAffineGauge

/-!
# Transferring hypertranscendence across the Herglotz normalization gauge

The regularized Herglotz transform of a measure satisfying the Nevanlinna growth condition is,
after normalizing its weighted measure, the value

```text
c * (z + (1 + z ^ (2 : ℕ)) * C_P z)
```

of an invertible affine rational gauge applied to the Cauchy transform of a probability measure.
This module records that the gauge coefficients really are invertible rational coordinates, so
hypertranscendence over the embedded `ℂ(z)` may be read off from either presentation.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory Polynomial

noncomputable section

local instance herglotzGaugeDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance herglotzGaugeComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance herglotzGaugeDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- The upper-end coordinate, viewed inside the embedded rational coordinate field. -/
def upperEndCoordinateGen : upperEndRationalCoordinateField :=
  ⟨upperEndCoordinateMero, IntermediateField.subset_adjoin ℂ _ rfl⟩

@[simp]
theorem upperEndCoordinateGen_coe :
    (upperEndCoordinateGen : upperEndMeroField) = upperEndCoordinateMero :=
  rfl

/-- The quadratic gauge factor `1 + z ^ (2 : ℕ)` is the image of a nonzero coordinate polynomial. -/
theorem one_add_coordinate_sq_eq_poly :
    (1 : upperEndMeroField) + upperEndCoordinateMero ^ (2 : ℕ) =
      upperEndPolyToMero (1 + Polynomial.X ^ (2 : ℕ)) := by
  rw [map_add, map_one, map_pow]
  rfl

/-- The quadratic gauge factor never vanishes in the meromorphic field. -/
theorem one_add_coordinate_sq_ne_zero :
    (1 : upperEndMeroField) + upperEndCoordinateMero ^ (2 : ℕ) ≠ 0 := by
  rw [one_add_coordinate_sq_eq_poly]
  intro hzero
  have hpoly : (1 + Polynomial.X ^ (2 : ℕ) : Polynomial ℂ) = 0 := by
    apply upperEndPolyToMero_injective
    rw [hzero, map_zero]
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 0) hpoly
  simp at hcoeff

/-- The multiplicative part of the Herglotz normalization gauge. -/
def herglotzGaugeMultiplier (c : ℂ) : upperEndRationalCoordinateField :=
  algebraMap ℂ upperEndRationalCoordinateField c * (1 + upperEndCoordinateGen ^ (2 : ℕ))

/-- The additive part of the Herglotz normalization gauge. -/
def herglotzGaugeShift (c : ℂ) : upperEndRationalCoordinateField :=
  algebraMap ℂ upperEndRationalCoordinateField c * upperEndCoordinateGen

@[simp]
theorem herglotzGaugeMultiplier_coe (c : ℂ) :
    (herglotzGaugeMultiplier c : upperEndMeroField) =
      algebraMap ℂ upperEndMeroField c *
        (1 + upperEndCoordinateMero ^ (2 : ℕ)) := by
  rw [herglotzGaugeMultiplier]
  push_cast
  rfl

@[simp]
theorem herglotzGaugeShift_coe (c : ℂ) :
    (herglotzGaugeShift c : upperEndMeroField) =
      algebraMap ℂ upperEndMeroField c * upperEndCoordinateMero := by
  rw [herglotzGaugeShift]
  push_cast
  rfl

/-- The gauge multiplier is invertible exactly when the normalizing mass is nonzero. -/
theorem herglotzGaugeMultiplier_ne_zero {c : ℂ} (hc : c ≠ 0) :
    herglotzGaugeMultiplier c ≠ 0 := by
  intro hzero
  have hcoe : (herglotzGaugeMultiplier c : upperEndMeroField) = 0 := by
    rw [hzero]
    rfl
  rw [herglotzGaugeMultiplier_coe] at hcoe
  rcases mul_eq_zero.mp hcoe with hc0 | hq0
  · exact hc ((injective_iff_map_eq_zero _).mp
      upperEndComplexToMero.injective c hc0)
  · exact one_add_coordinate_sq_ne_zero hq0

/-- **Herglotz gauge transfer.**  The normalized Herglotz presentation
`c * (z + (1 + z ^ (2 : ℕ)) * C)` is hypertranscendental over the embedded rational coordinate field
exactly when the underlying Cauchy carrier `C` is.  No analytic hypothesis is used beyond the
carrier lying in the meromorphic field. -/
theorem hypertranscendentalOver_herglotzGauge_iff
    (C : upperEndMeroField) {c : ℂ} (hc : c ≠ 0) :
    HypertranscendentalOver upperEndRationalCoordinateField
        (algebraMap ℂ upperEndMeroField c *
          (upperEndCoordinateMero +
            (1 + upperEndCoordinateMero ^ (2 : ℕ)) * C)) ↔
      HypertranscendentalOver upperEndRationalCoordinateField C := by
  have hrewrite :
      algebraMap ℂ upperEndMeroField c *
          (upperEndCoordinateMero + (1 + upperEndCoordinateMero ^ (2 : ℕ)) * C) =
        (herglotzGaugeMultiplier c : upperEndMeroField) * C +
          (herglotzGaugeShift c : upperEndMeroField) := by
    rw [herglotzGaugeMultiplier_coe, herglotzGaugeShift_coe]
    ring
  rw [hrewrite]
  exact hypertranscendentalOver_upperEnd_affineGauge_iff C
    (herglotzGaugeMultiplier c) (herglotzGaugeShift c)
    (herglotzGaugeMultiplier_ne_zero hc)

/-- Specialization to the actual Cauchy carrier of a finite measure. -/
theorem hypertranscendentalOver_herglotzGauge_cauchyTransform_iff
    (ν : Measure ℝ) [IsFiniteMeasure ν] {c : ℂ} (hc : c ≠ 0) :
    HypertranscendentalOver upperEndRationalCoordinateField
        (algebraMap ℂ upperEndMeroField c *
          (upperEndCoordinateMero +
            (1 + upperEndCoordinateMero ^ (2 : ℕ)) * cauchyTransformUpperEndMero ν)) ↔
      HypertranscendentalOver upperEndRationalCoordinateField
        (cauchyTransformUpperEndMero ν) :=
  hypertranscendentalOver_herglotzGauge_iff (cauchyTransformUpperEndMero ν) hc

end

end GaloisForLFunctions.HTGeometry
