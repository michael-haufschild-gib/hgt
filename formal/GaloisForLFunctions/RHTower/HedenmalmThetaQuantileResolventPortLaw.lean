import GaloisForLFunctions.RHTower.HedenmalmThetaQuantileBoundaryNull

/-!
# Two-port Green law for the phase-sensitive theta resolvent

The exact metric commutator measures the difference of boundary-port intensities.  Route T's
logarithmic-jet row is instead the symmetric port sum.  Here the inverse-pencil equation is welded
to the Green commutator without norms or determinant weights.  The resulting identity is exact,
but retains a source--response metric cross term: it does not eliminate the hidden antisymmetric
port.
-/

open Complex MeasureTheory

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmHilbertSchmidt

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Fixed-source polarized symplectic metric current. -/
def thetaQuantileMetricSymplecticCurrent (g : ThetaH) : ℂ :=
  (inner ℂ
      (thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate)) g : ℂ) -
    inner ℂ (thetaMetricOperator thetaQuantileCoordinate)
      (thetaKernelOperator g)

/-- Exact inverse-pencil equation, exposed for the all-complex theta resolvent. -/
theorem thetaComplexResolvent_add_parameter_kernel {z : ℂ}
    (hz : IsUnit (thetaSourcePencil z)) (f : ThetaH) :
    thetaComplexResolvent z f +
        z • thetaKernelOperator (thetaComplexResolvent z f) = f := by
  have hpencil : thetaSourcePencil z * thetaComplexResolvent z = 1 :=
    Ring.mul_inverse_cancel _ hz
  have h := congrArg (fun T : ThetaH →L[ℂ] ThetaH => T f) hpencil
  simpa only [thetaSourcePencil, thetaComplexResolvent,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply] using h

/-- Polarized metric commutator: boundary current is the symplectic metric pairing of source and
response. -/
theorem inner_pinnedBoundaryCLM_eq_thetaMetric_commutator_pair (f g : ThetaH) :
    (inner ℂ (pinnedBoundaryCLM f) g : ℂ) =
      Complex.I *
        ((inner ℂ (thetaMetricOperator (thetaKernelOperator f)) g : ℂ) -
          inner ℂ (thetaMetricOperator f) (thetaKernelOperator g)) := by
  have hgreen := congrArg (fun T : ThetaH →L[ℂ] ThetaH =>
      (inner ℂ (T f) g : ℂ)) thetaMetric_commutator_thetaKernelOperator
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply, inner_sub_left,
    ContinuousLinearMap.smul_apply, inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left] at hgreen
  have hconjI : (starRingEnd ℂ) Complex.I = -Complex.I := by
    simpa using Complex.conj_I
  rw [hconjI] at hgreen
  calc
    (inner ℂ (pinnedBoundaryCLM f) g : ℂ) =
        Complex.I * (-Complex.I *
          (inner ℂ (pinnedBoundaryCLM f) g : ℂ)) := by
      have hI : Complex.I * (-Complex.I) = (1 : ℂ) := by
        rw [mul_neg, Complex.I_mul_I]
        norm_num
      rw [← mul_assoc, hI, one_mul]
    _ = Complex.I *
        ((inner ℂ (thetaMetricOperator (thetaKernelOperator f)) g : ℂ) -
          inner ℂ (thetaMetricOperator f) (thetaKernelOperator g)) := by
      rw [hgreen]

/-- Quadratic form of the metric commutator is the exact rank-two boundary flux. -/
theorem inner_pinnedBoundaryCLM_eq_thetaMetric_commutator (g : ThetaH) :
    (inner ℂ (pinnedBoundaryCLM g) g : ℂ) =
      Complex.I *
        ((inner ℂ (thetaMetricOperator (thetaKernelOperator g)) g : ℂ) -
          inner ℂ (thetaMetricOperator g) (thetaKernelOperator g)) := by
  exact inner_pinnedBoundaryCLM_eq_thetaMetric_commutator_pair g g

/-- The desired monopole row is a fixed-source polarized symplectic Green current. -/
theorem thetaQuantileBoundaryDipole_mul_pinnedMean_eq_metricSymplectic (g : ThetaH) :
    pinnedFirstMoment thetaQuantileCoordinate * pinnedMean g =
      -Complex.I *
        ((inner ℂ
            (thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate)) g : ℂ) -
          inner ℂ (thetaMetricOperator thetaQuantileCoordinate)
            (thetaKernelOperator g)) := by
  have h := inner_pinnedBoundaryCLM_eq_thetaMetric_commutator_pair
    thetaQuantileCoordinate g
  rw [inner_pinnedBoundaryCLM_thetaQuantileCoordinate] at h
  linear_combination -h

/-- **Polarized Green representation of the Xi logarithmic derivative.**  Unlike quadratic energy,
this identity is phase-linear and retains divisor orientation. -/
theorem thetaQuantileMetricSymplectic_eq_logDeriv {z : ℂ}
    (hz : IsUnit (thetaSourcePencil z)) :
    pinnedFirstMoment thetaQuantileCoordinate * logDeriv XiC z =
      (inner ℂ
          (thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate))
          (thetaComplexResolvent z thetaQuantileCoordinate) : ℂ) -
        inner ℂ (thetaMetricOperator thetaQuantileCoordinate)
          (thetaKernelOperator
            (thetaComplexResolvent z thetaQuantileCoordinate)) := by
  have hphase := thetaQuantileBoundaryDipole_mul_pinnedMean_eq_metricSymplectic
    (thetaComplexResolvent z thetaQuantileCoordinate)
  rw [pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_logDeriv hz] at hphase
  apply mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero)
  calc
    (-Complex.I) *
        (pinnedFirstMoment thetaQuantileCoordinate * logDeriv XiC z) =
        pinnedFirstMoment thetaQuantileCoordinate *
          (-Complex.I * logDeriv XiC z) := by ring
    _ = (-Complex.I) *
        ((inner ℂ
            (thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate))
            (thetaComplexResolvent z thetaQuantileCoordinate) : ℂ) -
          inner ℂ (thetaMetricOperator thetaQuantileCoordinate)
            (thetaKernelOperator
              (thetaComplexResolvent z thetaQuantileCoordinate))) := hphase

/-- The phase-sensitive resolvent row is the normalized polarized metric current. -/
theorem pinnedMean_thetaQuantileResolvent_eq_metricSymplectic {z : ℂ}
    (hz : IsUnit (thetaSourcePencil z)) :
    pinnedMean (thetaComplexResolvent z thetaQuantileCoordinate) =
      (-Complex.I / pinnedFirstMoment thetaQuantileCoordinate) *
        ((inner ℂ
            (thetaMetricOperator (thetaKernelOperator thetaQuantileCoordinate))
            (thetaComplexResolvent z thetaQuantileCoordinate) : ℂ) -
          inner ℂ (thetaMetricOperator thetaQuantileCoordinate)
            (thetaKernelOperator
              (thetaComplexResolvent z thetaQuantileCoordinate))) := by
  rw [pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_logDeriv hz]
  rw [← thetaQuantileMetricSymplectic_eq_logDeriv hz]
  field_simp [pinnedFirstMoment_thetaQuantileCoordinate_ne_zero]

/-- Compact named form of the polarized logarithmic-derivative law. -/
theorem thetaQuantileMetricSymplecticCurrent_resolvent_eq_logDeriv {z : ℂ}
    (hz : IsUnit (thetaSourcePencil z)) :
    thetaQuantileMetricSymplecticCurrent
        (thetaComplexResolvent z thetaQuantileCoordinate) =
      pinnedFirstMoment thetaQuantileCoordinate * logDeriv XiC z := by
  exact (thetaQuantileMetricSymplectic_eq_logDeriv hz).symm

/-- Compact named form of the phase-sensitive polarized resolvent row. -/
theorem pinnedMean_thetaQuantileResolvent_eq_metricSymplecticCurrent {z : ℂ}
    (hz : IsUnit (thetaSourcePencil z)) :
    pinnedMean (thetaComplexResolvent z thetaQuantileCoordinate) =
      (-Complex.I / pinnedFirstMoment thetaQuantileCoordinate) *
        thetaQuantileMetricSymplecticCurrent
          (thetaComplexResolvent z thetaQuantileCoordinate) := by
  exact pinnedMean_thetaQuantileResolvent_eq_metricSymplectic hz

/-- Polarized current is `i` times dipole charge times the observed monopole row. -/
theorem thetaQuantileMetricSymplecticCurrent_resolvent_eq_I_mul_pinnedMean {z : ℂ}
    (hz : IsUnit (thetaSourcePencil z)) :
    thetaQuantileMetricSymplecticCurrent
        (thetaComplexResolvent z thetaQuantileCoordinate) =
      Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
        pinnedMean (thetaComplexResolvent z thetaQuantileCoordinate) := by
  rw [thetaQuantileMetricSymplecticCurrent_resolvent_eq_logDeriv hz,
    pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_logDeriv hz]
  have hI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    norm_num
  calc
    pinnedFirstMoment thetaQuantileCoordinate * logDeriv XiC z =
        (Complex.I * (-Complex.I)) *
          pinnedFirstMoment thetaQuantileCoordinate * logDeriv XiC z := by
      rw [hI]
      ring
    _ = Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
        (-Complex.I * logDeriv XiC z) := by ring

/-- **Scaled two-port resolvent Green law.**  It is polynomial in the pencil parameter, hence has
no artificial division at the origin.  The left side is boundary flux; the right side is the
oriented metric cross work between source and response. -/
theorem thetaComplexResolvent_scaled_boundaryFlux {z : ℂ}
    (hz : IsUnit (thetaSourcePencil z)) (f : ThetaH) :
    let g := thetaComplexResolvent z f
    (starRingEnd ℂ z * z) * (inner ℂ (pinnedBoundaryCLM g) g : ℂ) =
      Complex.I *
        (z * inner ℂ (thetaMetricOperator (f - g)) g -
          (starRingEnd ℂ z) * inner ℂ (thetaMetricOperator g) (f - g)) := by
  let g := thetaComplexResolvent z f
  have heq : g + z • thetaKernelOperator g = f :=
    thetaComplexResolvent_add_parameter_kernel hz f
  have hdiff : f - g = z • thetaKernelOperator g := by
    rw [← heq]
    module
  have hleft :
      (starRingEnd ℂ z) *
          (inner ℂ (thetaMetricOperator (thetaKernelOperator g)) g : ℂ) =
        inner ℂ (thetaMetricOperator (f - g)) g := by
    rw [hdiff, map_smul, inner_smul_left]
  have hright :
      z * (inner ℂ (thetaMetricOperator g) (thetaKernelOperator g) : ℂ) =
        inner ℂ (thetaMetricOperator g) (f - g) := by
    rw [hdiff, inner_smul_right]
  change
    (starRingEnd ℂ z * z) * (inner ℂ (pinnedBoundaryCLM g) g : ℂ) =
      Complex.I *
        (z * inner ℂ (thetaMetricOperator (f - g)) g -
          (starRingEnd ℂ z) * inner ℂ (thetaMetricOperator g) (f - g))
  rw [inner_pinnedBoundaryCLM_eq_thetaMetric_commutator]
  linear_combination
    Complex.I * z * hleft -
      Complex.I * (starRingEnd ℂ z) * hright

/-- Route T's quantile log-jet obeys the same exact two-port work law on every invertible pencil. -/
theorem thetaQuantileResolvent_scaled_boundaryFlux {z : ℂ}
    (hz : IsUnit (thetaSourcePencil z)) :
    let g := thetaComplexResolvent z thetaQuantileCoordinate
    (starRingEnd ℂ z * z) * (inner ℂ (pinnedBoundaryCLM g) g : ℂ) =
      Complex.I *
        (z * inner ℂ
            (thetaMetricOperator (thetaQuantileCoordinate - g)) g -
          (starRingEnd ℂ z) * inner ℂ
            (thetaMetricOperator g) (thetaQuantileCoordinate - g)) :=
  thetaComplexResolvent_scaled_boundaryFlux hz thetaQuantileCoordinate

end

end RHTower.HedenmalmThetaSource
