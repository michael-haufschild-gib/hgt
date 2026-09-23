import GaloisForLFunctions.HTGeometry.RydbergClockDephasing
import GaloisForLFunctions.HTGeometry.PositiveObserverGNSDecompositionLaw
import GaloisForLFunctions.RHTower.CCMArchimedeanQuantizedCalculus
import GaloisForLFunctions.RHTower.SoninEvenCarrier
import GaloisForLFunctions.RHTower.SuperPoincareProjectionFamily
import GaloisForLFunctions.RHTower.LpIndicatorProjectionGap

/-!
# Projector-dephasing applications to existing corpus clocks

Two pre-existing involutions—the Connes--Consani Hardy involution and Sonin
parity reflection—have invariant-sector projectors already developed elsewhere
in the corpus.  The Rydberg projector-dephasing law turns both into exact
double-commutator generators with classified kernels.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

theorem ccmHardyGaugeAverage_eq_projection :
    HTGeometry.finiteCyclicGaugeAverage ccmHardyInvolution 2 =
      ccmHardyProjection := by
  apply ContinuousLinearMap.ext
  intro x
  rw [HTGeometry.finiteInvolutiveGaugeAverage_apply,
    ccmHardyInvolution_apply]
  module

/-- Hardy-sector projective dephasing is exactly the quantized-calculus
double commutator, with normalization `-1/8`. -/
theorem ccmHardy_projectorDephasing_eq_doubleCommutator
    (X : SoninL2 →L[ℂ] SoninL2) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) ccmHardyProjection X =
      -(8 : ℂ)⁻¹ •
        (ccmHardyInvolution * (ccmHardyInvolution * X - X * ccmHardyInvolution) -
          (ccmHardyInvolution * X - X * ccmHardyInvolution) * ccmHardyInvolution) := by
  rw [← ccmHardyGaugeAverage_eq_projection]
  exact HTGeometry.projectorDephasingGenerator_finiteInvolutiveGaugeAverage_eq
    ccmHardyInvolution X ccmHardyInvolution_sq_eq_one

/-- Exact immunity criterion: Hardy dephasing vanishes precisely on observables
commuting with the Hardy involution. -/
theorem ccmHardy_projectorDephasing_eq_zero_iff
    (X : SoninL2 →L[ℂ] SoninL2) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) ccmHardyProjection X = 0 ↔
      ccmHardyInvolution * X = X * ccmHardyInvolution := by
  rw [← ccmHardyGaugeAverage_eq_projection]
  exact HTGeometry.projectorDephasingGenerator_finiteInvolutiveGaugeAverage_eq_zero_iff
    ccmHardyInvolution X ccmHardyInvolution_sq_eq_one

/-- Re-pinching an observable at the Hardy split is dephasing-immune. -/
theorem ccmHardy_pinched_projectorDephasing_eq_zero
    (X : SoninL2 →L[ℂ] SoninL2) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) ccmHardyProjection
      (HTGeometry.twoOutcomePinching ccmHardyProjection X) = 0 := by
  exact HTGeometry.projectorDephasingGenerator_pinching_eq_zero (k := ℂ)
    ccmHardyProjection X ccmHardyProjection_idempotent

theorem l2Reflection_sq_eq_one : l2Reflection ^ (2 : ℕ) = 1 := by
  change l2Reflection * l2Reflection = 1
  apply ContinuousLinearMap.ext
  intro f
  change l2Reflection (l2Reflection f) = f
  exact l2Reflection_involutive f

theorem l2ReflectionGaugeAverage_eq_evenProjection :
    HTGeometry.finiteCyclicGaugeAverage l2Reflection 2 = evenProjection := by
  apply ContinuousLinearMap.ext
  intro f
  rw [HTGeometry.finiteInvolutiveGaugeAverage_apply, evenProjection_apply]

/-- Sonin parity dephasing is the double commutator with spatial reflection. -/
theorem soninEven_projectorDephasing_eq_doubleCommutator
    (X : SoninL2 →L[ℂ] SoninL2) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) evenProjection X =
      -(8 : ℂ)⁻¹ •
        (l2Reflection * (l2Reflection * X - X * l2Reflection) -
          (l2Reflection * X - X * l2Reflection) * l2Reflection) := by
  rw [← l2ReflectionGaugeAverage_eq_evenProjection]
  exact HTGeometry.projectorDephasingGenerator_finiteInvolutiveGaugeAverage_eq
    l2Reflection X l2Reflection_sq_eq_one

/-- Sonin parity dephasing vanishes exactly for reflection-preserving observables. -/
theorem soninEven_projectorDephasing_eq_zero_iff
    (X : SoninL2 →L[ℂ] SoninL2) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) evenProjection X = 0 ↔
      l2Reflection * X = X * l2Reflection := by
  rw [← l2ReflectionGaugeAverage_eq_evenProjection]
  exact HTGeometry.projectorDephasingGenerator_finiteInvolutiveGaugeAverage_eq_zero_iff
    l2Reflection X l2Reflection_sq_eq_one

/-- Re-pinching at the even/odd Sonin split is dephasing-immune. -/
theorem soninEven_pinched_projectorDephasing_eq_zero
    (X : SoninL2 →L[ℂ] SoninL2) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) evenProjection
      (HTGeometry.twoOutcomePinching evenProjection X) = 0 := by
  exact HTGeometry.projectorDephasingGenerator_pinching_eq_zero (k := ℂ)
    evenProjection X evenProjection_idempotent

/-! ## Projection-phase families -/

/-- Every member of the existing oblique shear family obeys the algebraic
half-pinching dephasing identity. -/
theorem projectionPhaseShear_projectorDephasing_eq_halfPinching
    (t : ℝ) (X : ProjectionPhaseEnd) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (projectionPhaseShearFamily t) X =
      (2 : ℂ)⁻¹ •
        (HTGeometry.twoOutcomePinching (projectionPhaseShearFamily t) X - X) := by
  exact HTGeometry.projectorDephasingGenerator_eq_half_pinching_sub (k := ℂ)
    (projectionPhaseShearFamily t) X (projectionPhaseShearFamily_idempotent t)

theorem projectionPhaseShear_projectorDephasing_eq_zero_iff
    (t : ℝ) (X : ProjectionPhaseEnd) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (projectionPhaseShearFamily t) X = 0 ↔
      projectionPhaseShearFamily t * X = X * projectionPhaseShearFamily t := by
  exact HTGeometry.projectorDephasingGenerator_eq_zero_iff_commute (k := ℂ)
    (projectionPhaseShearFamily t) X (projectionPhaseShearFamily_idempotent t)

theorem projectionPhaseShear_pinched_projectorDephasing_eq_zero
    (t : ℝ) (X : ProjectionPhaseEnd) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) (projectionPhaseShearFamily t)
      (HTGeometry.twoOutcomePinching (projectionPhaseShearFamily t) X) = 0 := by
  exact HTGeometry.projectorDephasingGenerator_pinching_eq_zero (k := ℂ)
    (projectionPhaseShearFamily t) X (projectionPhaseShearFamily_idempotent t)

/-- Orthogonal projection-phase family gives the physical self-adjoint specialization. -/
theorem projectionPhaseOrthogonal_projectorDephasing_eq_halfPinching
    (t : ℝ) (X : ProjectionPhaseEnd) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (projectionPhaseOrthogonalFamily t) X =
      (2 : ℂ)⁻¹ •
        (HTGeometry.twoOutcomePinching (projectionPhaseOrthogonalFamily t) X - X) := by
  exact HTGeometry.projectorDephasingGenerator_eq_half_pinching_sub (k := ℂ)
    (projectionPhaseOrthogonalFamily t) X
    (projectionPhaseOrthogonalFamily_idempotent t)

theorem projectionPhaseOrthogonal_projectorDephasing_eq_zero_iff
    (t : ℝ) (X : ProjectionPhaseEnd) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (projectionPhaseOrthogonalFamily t) X = 0 ↔
      projectionPhaseOrthogonalFamily t * X =
        X * projectionPhaseOrthogonalFamily t := by
  exact HTGeometry.projectorDephasingGenerator_eq_zero_iff_commute (k := ℂ)
    (projectionPhaseOrthogonalFamily t) X
    (projectionPhaseOrthogonalFamily_idempotent t)

theorem projectionPhaseOrthogonal_pinched_projectorDephasing_eq_zero
    (t : ℝ) (X : ProjectionPhaseEnd) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) (projectionPhaseOrthogonalFamily t)
      (HTGeometry.twoOutcomePinching (projectionPhaseOrthogonalFamily t) X) = 0 := by
  exact HTGeometry.projectorDephasingGenerator_pinching_eq_zero (k := ℂ)
    (projectionPhaseOrthogonalFamily t) X
    (projectionPhaseOrthogonalFamily_idempotent t)

/-! ## Measurable support cutoffs -/

/-- Measurable support sector packaged so exported applications need no proof premise. -/
structure RydbergMeasurableCutoff (X : Type*) [MeasurableSpace X] where
  carrier : Set X
  measurableCarrier : MeasurableSet carrier

namespace RydbergMeasurableCutoff

def projection
    {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (C : RydbergMeasurableCutoff X) :
    MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ :=
  lpIndicatorProjection μ C.carrier C.measurableCarrier

theorem projection_idempotent
    {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (C : RydbergMeasurableCutoff X) : IsIdempotentElem (C.projection μ) := by
  exact lpIndicatorProjection_idempotent μ C.carrier C.measurableCarrier

/-- Support-sector dephasing is half the hard-cutoff pinching disturbance. -/
theorem projectorDephasing_eq_halfPinching
    {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (C : RydbergMeasurableCutoff X)
    (A : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ) :
    HTGeometry.projectorDephasingGenerator (k := ℝ) (C.projection μ) A =
      (2 : ℝ)⁻¹ • (HTGeometry.twoOutcomePinching (C.projection μ) A - A) := by
  exact HTGeometry.projectorDephasingGenerator_eq_half_pinching_sub (k := ℝ)
    (C.projection μ) A (C.projection_idempotent μ)

/-- Kernel consists exactly of support-preserving observables. -/
theorem projectorDephasing_eq_zero_iff
    {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (C : RydbergMeasurableCutoff X)
    (A : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ) :
    HTGeometry.projectorDephasingGenerator (k := ℝ) (C.projection μ) A = 0 ↔
      C.projection μ * A = A * C.projection μ := by
  exact HTGeometry.projectorDephasingGenerator_eq_zero_iff_commute (k := ℝ)
    (C.projection μ) A (C.projection_idempotent μ)

theorem pinched_projectorDephasing_eq_zero
    {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (C : RydbergMeasurableCutoff X)
    (A : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ) :
    HTGeometry.projectorDephasingGenerator (k := ℝ) (C.projection μ)
      (HTGeometry.twoOutcomePinching (C.projection μ) A) = 0 := by
  exact HTGeometry.projectorDephasingGenerator_pinching_eq_zero (k := ℝ)
    (C.projection μ) A (C.projection_idempotent μ)

end RydbergMeasurableCutoff

/-! ## Conditional-expectation projections -/

/-- The completed GNS conditional expectation carries its projection law as data. -/
theorem completedConditionalProjection_idempotent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : GaloisForLFunctions.HTGeometry.CompletedConditionalProjection H) :
    IsIdempotentElem P.projector := by
  apply ContinuousLinearMap.ext
  exact P.idempotent

/-- Conditional-expectation dephasing is half the observed/hidden pinching disturbance. -/
theorem completedConditionalProjection_projectorDephasing_eq_halfPinching
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : GaloisForLFunctions.HTGeometry.CompletedConditionalProjection H)
    (A : H →L[ℂ] H) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) P.projector A =
      (2 : ℂ)⁻¹ • (HTGeometry.twoOutcomePinching P.projector A - A) := by
  exact HTGeometry.projectorDephasingGenerator_eq_half_pinching_sub (k := ℂ)
    P.projector A (completedConditionalProjection_idempotent P)

/-- Zero dephasing is exactly preservation of the observed/hidden GNS split. -/
theorem completedConditionalProjection_projectorDephasing_eq_zero_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : GaloisForLFunctions.HTGeometry.CompletedConditionalProjection H)
    (A : H →L[ℂ] H) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) P.projector A = 0 ↔
      P.projector * A = A * P.projector := by
  exact HTGeometry.projectorDephasingGenerator_eq_zero_iff_commute (k := ℂ)
    P.projector A (completedConditionalProjection_idempotent P)

theorem completedConditionalProjection_pinched_projectorDephasing_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : GaloisForLFunctions.HTGeometry.CompletedConditionalProjection H)
    (A : H →L[ℂ] H) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) P.projector
      (HTGeometry.twoOutcomePinching P.projector A) = 0 := by
  exact HTGeometry.projectorDephasingGenerator_pinching_eq_zero (k := ℂ)
    P.projector A (completedConditionalProjection_idempotent P)

/-- Boundary moment-fiber conditional expectation is an algebraic projector. -/
theorem boundaryConditionalProjection_idempotent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : GaloisForLFunctions.HTGeometry.BoundaryConditionalProjection H) :
    IsIdempotentElem P.projector := by
  apply LinearMap.ext
  exact P.idempotent

/-- Moment-fiber boundary dephasing is half the horizontal/vertical pinching disturbance. -/
theorem boundaryConditionalProjection_projectorDephasing_eq_halfPinching
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : GaloisForLFunctions.HTGeometry.BoundaryConditionalProjection H)
    (A : H →ₗ[ℂ] H) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) P.projector A =
      (2 : ℂ)⁻¹ • (HTGeometry.twoOutcomePinching P.projector A - A) := by
  exact HTGeometry.projectorDephasingGenerator_eq_half_pinching_sub (k := ℂ)
    P.projector A (boundaryConditionalProjection_idempotent P)

/-- Zero boundary dephasing is exactly preservation of horizontal/vertical moment sectors. -/
theorem boundaryConditionalProjection_projectorDephasing_eq_zero_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : GaloisForLFunctions.HTGeometry.BoundaryConditionalProjection H)
    (A : H →ₗ[ℂ] H) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) P.projector A = 0 ↔
      P.projector * A = A * P.projector := by
  exact HTGeometry.projectorDephasingGenerator_eq_zero_iff_commute (k := ℂ)
    P.projector A (boundaryConditionalProjection_idempotent P)

theorem boundaryConditionalProjection_pinched_projectorDephasing_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : GaloisForLFunctions.HTGeometry.BoundaryConditionalProjection H)
    (A : H →ₗ[ℂ] H) :
    HTGeometry.projectorDephasingGenerator (k := ℂ) P.projector
      (HTGeometry.twoOutcomePinching P.projector A) = 0 := by
  exact HTGeometry.projectorDephasingGenerator_pinching_eq_zero (k := ℂ)
    P.projector A (boundaryConditionalProjection_idempotent P)

end RHTower
