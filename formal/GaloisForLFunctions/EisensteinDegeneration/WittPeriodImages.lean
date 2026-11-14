import GaloisForLFunctions.EisensteinDegeneration.PeriodImage
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittEuler

/-!
# Period changes of integral Euler products

The literal big-Witt series, finite Euler products and their coefficientwise
limit all have constant term one. Consequently their period images have
exactly the imposed boundary order. No cancellation among Euler coordinates
can change that order or hide a Laurent pole.
-/

namespace GaloisForLFunctions.EisensteinDegeneration

open PowerSeries RHTower

noncomputable section

variable {R : Type*} [CommRing R]

/-- The unit represented by the complete integral Euler product. -/
def eulerPeriodUnit (x : ℕ → R) : (PowerSeries R)ˣ where
  val := deningerBigWittEulerSeries x
  inv := PowerSeries.invOfUnit (deningerBigWittEulerSeries x) 1
  val_inv := PowerSeries.mul_invOfUnit _ 1 (deningerBigWittEulerSeries_constantCoeff x)
  inv_val := PowerSeries.invOfUnit_mul _ 1 (deningerBigWittEulerSeries_constantCoeff x)

/-- The unit represented by an arbitrary finite cutoff of the same Euler product. -/
def partialEulerPeriodUnit (x : ℕ → R) (N : ℕ) : (PowerSeries R)ˣ where
  val := deningerBigWittEulerPartial x N
  inv := PowerSeries.invOfUnit (deningerBigWittEulerPartial x N) 1
  val_inv := PowerSeries.mul_invOfUnit _ 1 (deningerBigWittEulerPartial_constantCoeff x N)
  inv_val := PowerSeries.invOfUnit_mul _ 1 (deningerBigWittEulerPartial_constantCoeff x N)

/-- The boundary coefficient is independent of every Euler coordinate. -/
theorem eulerPeriod_boundary (m : ℕ) (x : ℕ → R) (f : PowerSeries R) :
    coeff m (periodImage m (eulerPeriodUnit x) f) = constantCoeff f := by
  rw [periodImage_coeff_boundary]
  change constantCoeff (deningerBigWittEulerSeries x) * constantCoeff f = _
  rw [deningerBigWittEulerSeries_constantCoeff, one_mul]

/-- Every finite cutoff gives the same first surviving coefficient as the complete product. -/
theorem partialEulerPeriod_boundary (m N : ℕ) (x : ℕ → R) (f : PowerSeries R) :
    coeff m (periodImage m (partialEulerPeriodUnit x N) f) =
      coeff m (periodImage m (eulerPeriodUnit x) f) := by
  rw [eulerPeriod_boundary, periodImage_coeff_boundary]
  change constantCoeff (deningerBigWittEulerPartial x N) * constantCoeff f = _
  rw [deningerBigWittEulerPartial_constantCoeff, one_mul]

/-- The whole Euler product detects regularity, without hypotheses on its coordinates. -/
theorem eulerProduct_detects_regular (x : ℕ → R) (f : LaurentSeries R) :
    Regular (f * (deningerBigWittEulerSeries x : LaurentSeries R)) ↔ Regular f :=
  regular_mul_unit_iff f (eulerPeriodUnit x)

/-- Pole detection also holds at every finite Euler cutoff. -/
theorem partialEulerProduct_detects_regular (x : ℕ → R) (N : ℕ) (f : LaurentSeries R) :
    Regular (f * (deningerBigWittEulerPartial x N : LaurentSeries R)) ↔ Regular f :=
  regular_mul_unit_iff f (partialEulerPeriodUnit x N)

/-- The literal Witt carrier supplies the same regularity detector before choosing Euler
coordinates. -/
theorem wittSeries_detects_regular (w : DeningerBigWittAdditive R) (f : LaurentSeries R) :
    Regular (f * (deningerBigWittSeries w : LaurentSeries R)) ↔ Regular f :=
  regular_mul_unit_iff f w.1

section Domain

variable [IsDomain R]

/-- A complete Euler product shifts the order only by the actual period-map exponent. -/
theorem eulerPeriod_order (m : ℕ) (x : ℕ → R) (f : PowerSeries R) :
    (periodImage m (eulerPeriodUnit x) f).order = m + f.order :=
  periodImage_order m (eulerPeriodUnit x) f

/-- Finite truncation and the complete Euler product have identical period-image orders. -/
theorem partialEulerPeriod_order (m N : ℕ) (x : ℕ → R) (f : PowerSeries R) :
    (periodImage m (partialEulerPeriodUnit x N) f).order =
      (periodImage m (eulerPeriodUnit x) f).order := by
  rw [periodImage_order, periodImage_order]

end Domain

/-- Euler coordinates do not change the dimension of the boundary quotient. -/
theorem eulerPeriod_cokernel_finrank {K : Type*} [Field K] (m : ℕ) (x : ℕ → K) :
    Module.finrank K (PowerSeries K ⧸ (periodMap m (eulerPeriodUnit x)).range) = m :=
  periodCokernel_finrank m (eulerPeriodUnit x)

end

end GaloisForLFunctions.EisensteinDegeneration
