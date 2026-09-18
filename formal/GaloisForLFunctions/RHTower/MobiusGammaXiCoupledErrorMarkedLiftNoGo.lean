import GaloisForLFunctions.RHTower.MobiusGammaXiCoupledErrorDebtCancellationDichotomy

/-!
# G-CE marked linear-lift cancellation dichotomy

The scalar G-CE debt is the literal charge
`mobiusGammaXiCoupledErrorCriticalCoefficient`.  This module tests the only direct
higher-dimensional extension of the scalar-controller proposal: inject that charge into a marked
complex normed space, then apply a fixed complex-linear scalar readout.

The result is exhaustive.  If the visible scalar residual cancels, then either the actual charge
is zero (equivalently RH), or the composite scalar readout is `-I` on *every* scalar input.  Thus
adding hidden marked coordinates does not make a fixed linear scalar cancellation source-faithful:
the visible readout still erases the complete scalar source channel.  A viable pre-scalar G-CE
producer must therefore use a non-linear/pair interaction or a non-fixed readout before its final
source identification.
-/

open Complex

noncomputable section

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Visible G-CE charge after a marked linear lift and a fixed scalar readout. -/
def mobiusGammaXiMarkedLiftResidual
    (inject : ℂ →L[ℂ] E) (readout : E →L[ℂ] ℂ) : ℂ :=
  mobiusGammaXiCoupledErrorCriticalCoefficient +
    readout (inject mobiusGammaXiCoupledErrorCriticalCoefficient)

/-- A marked lift erases the scalar source at its fixed readout exactly when the coherent visible
sum vanishes for every possible scalar charge. -/
def mobiusGammaXiMarkedLiftErasesScalarReadout
    (inject : ℂ →L[ℂ] E) (readout : E →L[ℂ] ℂ) : Prop :=
  ∀ z : ℂ, z + readout (inject z) = 0

/-- The unique opposite scalar controller. -/
def mobiusGammaXiMarkedLiftOppositeScalarController : ℂ →L[ℂ] ℂ :=
  -(ContinuousLinearMap.id ℂ ℂ)

/-- Exact classification of universal scalar erasure through an arbitrary marked linear lift. -/
theorem mobiusGammaXiMarkedLift_erasesScalarReadout_iff_readoutComp_eq_opposite
    (inject : ℂ →L[ℂ] E) (readout : E →L[ℂ] ℂ) :
    mobiusGammaXiMarkedLiftErasesScalarReadout inject readout ↔
      readout.comp inject = mobiusGammaXiMarkedLiftOppositeScalarController := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro z
    have hz := h z
    simp only [mobiusGammaXiMarkedLiftOppositeScalarController,
      ContinuousLinearMap.comp_apply, _root_.neg_apply, ContinuousLinearMap.id_apply]
    linear_combination hz
  · rintro h z
    change z + (readout.comp inject) z = 0
    rw [h]
    simp [mobiusGammaXiMarkedLiftOppositeScalarController]

/-- **Marked linear-lift dichotomy.**  Cancelling the actual G-CE scalar charge after any
complex-linear marked lift either proves RH or erases every scalar source at the fixed readout. -/
theorem mobiusGammaXiMarkedLift_residual_eq_zero_iff_rh_or_erasesScalarReadout
    (inject : ℂ →L[ℂ] E) (readout : E →L[ℂ] ℂ) :
    mobiusGammaXiMarkedLiftResidual inject readout = 0 ↔
      RiemannHypothesis ∨ mobiusGammaXiMarkedLiftErasesScalarReadout inject readout := by
  let d := mobiusGammaXiCoupledErrorCriticalCoefficient
  constructor
  · intro hcancel
    by_cases hd : d = 0
    · left
      exact continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mp
        (by simpa [d, mobiusGammaXiCoupledErrorCriticalCoefficient] using hd)
    · right
      intro z
      have hTd : readout (inject d) = -d := by
        dsimp only [mobiusGammaXiMarkedLiftResidual, d] at hcancel
        linear_combination hcancel
      have hzd : ((z / d) : ℂ) • d = z := by
        simp [smul_eq_mul, hd]
      rw [← hzd, map_smul, map_smul, hTd]
      simp
  · rintro (hRH | herase)
    · have hd : mobiusGammaXiCoupledErrorCriticalCoefficient = 0 := by
        exact continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mpr hRH
      simp [mobiusGammaXiMarkedLiftResidual, hd]
    · exact herase mobiusGammaXiCoupledErrorCriticalCoefficient

/-- Equivalent operator form: a marked linear lift that visibly cancels without RH has composite
scalar readout exactly `-I`. -/
theorem mobiusGammaXiMarkedLift_residual_eq_zero_iff_rh_or_readoutComp_eq_opposite
    (inject : ℂ →L[ℂ] E) (readout : E →L[ℂ] ℂ) :
    mobiusGammaXiMarkedLiftResidual inject readout = 0 ↔
      RiemannHypothesis ∨
        readout.comp inject = mobiusGammaXiMarkedLiftOppositeScalarController := by
  rw [mobiusGammaXiMarkedLift_residual_eq_zero_iff_rh_or_erasesScalarReadout,
    mobiusGammaXiMarkedLift_erasesScalarReadout_iff_readoutComp_eq_opposite]

/-- Removing universal scalar erasure leaves precisely the RH branch. -/
theorem mobiusGammaXiMarkedLift_nonerasingCancellation_iff
    (inject : ℂ →L[ℂ] E) (readout : E →L[ℂ] ℂ) :
    (readout.comp inject ≠ mobiusGammaXiMarkedLiftOppositeScalarController ∧
        mobiusGammaXiMarkedLiftResidual inject readout = 0) ↔
      (readout.comp inject ≠ mobiusGammaXiMarkedLiftOppositeScalarController ∧
        RiemannHypothesis) := by
  rw [mobiusGammaXiMarkedLift_residual_eq_zero_iff_rh_or_readoutComp_eq_opposite]
  tauto

/-- The marked-lift formulation specializes definitionally to the existing physical scalar G-CE
controller. -/
theorem mobiusGammaXiMarkedLift_residual_scalar_specialization
    (T : ℂ →L[ℂ] ℂ) :
    mobiusGammaXiMarkedLiftResidual (ContinuousLinearMap.id ℂ ℂ) T =
      mobiusGammaXiControlledCriticalResidual T := by
  rfl

end RHTower
