import GaloisForLFunctions.HTGeometry.CoherentHistoryMechanics
import GaloisForLFunctions.HTGeometry.MarkedVariationDynamics

/-!
# Calibration-spectrum mechanics

A positive envelope and a coherent complex output define a nonnegative response against every
unit calibrator.  Four calibrators reconstruct the envelope and coherent output; positive
observers transport the full response linearly, while optimizing the calibrator after observation
creates exactly the marked-variation observer loss.  The same response has a nonnegative marked
source ancestry and an exact serial conservation law.

All results are finite, unconditional, and independent of RH.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- A unit complex calibrator. Unit modulus is structural data, not a theorem premise. -/
structure UnitCalibrator where
  val : ℂ
  norm_eq_one : ‖val‖ = 1

namespace UnitCalibrator

/-- Positive real calibrator. -/
def one : UnitCalibrator :=
  ⟨1, norm_one⟩

/-- Negative real calibrator. -/
def negOne : UnitCalibrator :=
  ⟨-1, by simp⟩

/-- Positive imaginary calibrator. -/
def I : UnitCalibrator :=
  ⟨Complex.I, Complex.norm_I⟩

/-- Negative imaginary calibrator. -/
def negI : UnitCalibrator :=
  ⟨-Complex.I, by simp⟩

end UnitCalibrator

/-- The total coherent phase always has unit modulus, including at zero. -/
theorem norm_coherentUnitPhase (z : ℂ) : ‖coherentUnitPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [coherentUnitPhase, hz]
  · rw [coherentUnitPhase, if_neg hz, norm_mul, norm_inv]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    field_simp

/-- The coherent phase calibrates a complex number to its positive modulus. -/
theorem star_coherentUnitPhase_mul (z : ℂ) :
    (starRingEnd ℂ) (coherentUnitPhase z) * z = (‖z‖ : ℂ) := by
  calc
    (starRingEnd ℂ) (coherentUnitPhase z) * z =
        (starRingEnd ℂ) (coherentUnitPhase z) *
          ((‖z‖ : ℂ) * coherentUnitPhase z) := by
            rw [norm_mul_coherentUnitPhase]
    _ = (‖z‖ : ℂ) *
          ((starRingEnd ℂ) (coherentUnitPhase z) * coherentUnitPhase z) := by ring
    _ = (‖z‖ : ℂ) := by
      rw [RCLike.conj_mul, norm_coherentUnitPhase]
      simp

/-- Canonical calibrator selected by a coherent output. -/
def coherentCalibrator (z : ℂ) : UnitCalibrator :=
  ⟨coherentUnitPhase z, norm_coherentUnitPhase z⟩

/-- Challenge response of a positive envelope and coherent output. -/
def calibrationResponse (envelope : ℝ) (coherent : ℂ) (u : UnitCalibrator) : ℝ :=
  envelope - ((starRingEnd ℂ) u.val * coherent).re

/-- Residual of one marked coherent contribution against a calibrator. -/
def phaseResidual (u : UnitCalibrator) (z : ℂ) : ℝ :=
  calibrationResponse ‖z‖ z u

/-- Every phase residual is nonnegative. -/
theorem phaseResidual_nonneg (u : UnitCalibrator) (z : ℂ) :
    0 ≤ phaseResidual u z := by
  have hre := Complex.re_le_norm ((starRingEnd ℂ) u.val * z)
  rw [norm_mul, Complex.norm_conj, u.norm_eq_one, one_mul] at hre
  exact sub_nonneg.mpr hre

/-- The coherent calibrator attains the modulus ground response. -/
theorem calibrationResponse_coherentCalibrator (envelope : ℝ) (z : ℂ) :
    calibrationResponse envelope z (coherentCalibrator z) = envelope - ‖z‖ := by
  simp only [calibrationResponse, coherentCalibrator]
  rw [star_coherentUnitPhase_mul, Complex.ofReal_re]

/-- Every unit calibrator lies above the modulus ground response. -/
theorem calibrationResponse_ground_le (envelope : ℝ) (z : ℂ) (u : UnitCalibrator) :
    envelope - ‖z‖ ≤ calibrationResponse envelope z u := by
  have hre := Complex.re_le_norm ((starRingEnd ℂ) u.val * z)
  rw [norm_mul, Complex.norm_conj, u.norm_eq_one, one_mul] at hre
  exact sub_le_sub_left hre envelope

/-- Four calibration values reconstruct the positive envelope. -/
theorem calibrationResponse_four_reconstruct_envelope (envelope : ℝ) (z : ℂ) :
    (calibrationResponse envelope z UnitCalibrator.one +
        calibrationResponse envelope z UnitCalibrator.negOne) / 2 = envelope := by
  simp [calibrationResponse, UnitCalibrator.one, UnitCalibrator.negOne]

/-- Four calibration values reconstruct the real coherent coordinate. -/
theorem calibrationResponse_four_reconstruct_re (envelope : ℝ) (z : ℂ) :
    (calibrationResponse envelope z UnitCalibrator.negOne -
        calibrationResponse envelope z UnitCalibrator.one) / 2 = z.re := by
  simp [calibrationResponse, UnitCalibrator.one, UnitCalibrator.negOne]

/-- Four calibration values reconstruct the imaginary coherent coordinate. -/
theorem calibrationResponse_four_reconstruct_im (envelope : ℝ) (z : ℂ) :
    (calibrationResponse envelope z UnitCalibrator.negI -
        calibrationResponse envelope z UnitCalibrator.I) / 2 = z.im := by
  simp [calibrationResponse, UnitCalibrator.I, UnitCalibrator.negI, Complex.mul_re]

/-- Positive mixing transports a calibration response exactly. -/
theorem applyReal_calibrationResponse {X Y : Type*} [Fintype X]
    (T : FinitePositiveKernel X Y) (envelope : X → ℝ) (coherent : X → ℂ)
    (u : UnitCalibrator) :
    T.applyReal (fun x => calibrationResponse (envelope x) (coherent x) u) =
      fun y => calibrationResponse (T.applyReal envelope y) (T.applyComplex coherent y) u := by
  funext y
  change (∑ x, T.weight y x *
      (envelope x - ((starRingEnd ℂ) u.val * coherent x).re)) =
    (∑ x, T.weight y x * envelope x) -
      ((starRingEnd ℂ) u.val *
        ∑ x, (T.weight y x : ℂ) * coherent x).re
  rw [show (∑ x, T.weight y x *
      (envelope x - ((starRingEnd ℂ) u.val * coherent x).re)) =
      ∑ x, (T.weight y x * envelope x -
        T.weight y x * ((starRingEnd ℂ) u.val * coherent x).re) by
          apply Finset.sum_congr rfl
          intro x hx
          ring]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  change (∑ x, T.weight y x * ((starRingEnd ℂ) u.val * coherent x).re) =
    Complex.reAddGroupHom
      (∑ x, (starRingEnd ℂ) u.val * ((T.weight y x : ℂ) * coherent x))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp [Complex.mul_re]
  ring

section MarkedCalibration

variable {X Y Z I J : Type*}

/-- Calibration spectrum of a marked packet after a positive observer. -/
def markedCalibrationSpectrum [Fintype X] [Fintype I]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) (y : Y)
    (u : UnitCalibrator) : ℝ :=
  calibrationResponse (markedEnvelopeOutput T a y) (markedCoherentOutput T a y) u

/-- The marked calibration spectrum is pointwise nonnegative. -/
theorem markedCalibrationSpectrum_nonneg [Fintype X] [Fintype I]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) (y : Y)
    (u : UnitCalibrator) :
    0 ≤ markedCalibrationSpectrum T a y u := by
  have hdefect := markedVariationDefect_nonneg T a y
  have hground := calibrationResponse_ground_le
    (markedEnvelopeOutput T a y) (markedCoherentOutput T a y) u
  dsimp [markedVariationDefect, markedCalibrationSpectrum] at hdefect ⊢
  linarith

/-- Every calibrator lies above marked variation. -/
theorem markedVariationDefect_le_spectrum [Fintype X] [Fintype I]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) (y : Y)
    (u : UnitCalibrator) :
    markedVariationDefect T a y ≤ markedCalibrationSpectrum T a y u := by
  exact calibrationResponse_ground_le
    (markedEnvelopeOutput T a y) (markedCoherentOutput T a y) u

/-- The coherent calibrator attains marked variation exactly. -/
theorem markedCalibrationSpectrum_ground [Fintype X] [Fintype I]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) (y : Y) :
    markedCalibrationSpectrum T a y
      (coherentCalibrator (markedCoherentOutput T a y)) = markedVariationDefect T a y := by
  exact calibrationResponse_coherentCalibrator
    (markedEnvelopeOutput T a y) (markedCoherentOutput T a y)

/-- Serial positive observation transports the full marked calibration spectrum linearly. -/
theorem markedCalibrationSpectrum_observerTransport [Fintype X] [Fintype Y] [Fintype I]
    (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y)
    (a : I → X → ℂ) (z : Z) (u : UnitCalibrator) :
    markedCalibrationSpectrum (S.comp T) a z u =
      S.applyReal (fun y => markedCalibrationSpectrum T a y u) z := by
  have hresponse := applyReal_calibrationResponse S
    (markedEnvelopeOutput T a) (markedCoherentOutput T a) u
  change calibrationResponse
      (markedEnvelopeOutput (S.comp T) a z)
      (markedCoherentOutput (S.comp T) a z) u = _
  rw [show markedEnvelopeOutput (S.comp T) a =
      S.applyReal (markedEnvelopeOutput T a) by
        exact S.applyReal_comp T (markedEnvelope a)]
  rw [show markedCoherentOutput (S.comp T) a =
      S.applyComplex (markedCoherentOutput T a) by
        exact S.applyComplex_comp T (markedCoherent a)]
  exact (congrFun hresponse z).symm

/-- Optimizing after observation differs from optimizing before observation by exactly the
positive observer loss. -/
theorem markedCalibration_ground_exchange [Fintype X] [Fintype Y] [Fintype I]
    (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y)
    (a : I → X → ℂ) (z : Z) :
    markedVariationDefect (S.comp T) a z -
        S.applyReal (markedVariationDefect T a) z =
      positiveObserverLoss S (markedCoherentOutput T a) z := by
  have hchain := congrFun (markedVariationDefect_observerChain S T a) z
  linarith

/-- Summing residuals of the marked entries gives the aggregate calibration response. -/
theorem sum_phaseResidual_eq_calibrationResponse [Fintype I]
    (a : I → X → ℂ) (x : X) (u : UnitCalibrator) :
    (∑ i, phaseResidual u (a i x)) =
      calibrationResponse (markedEnvelope a x) (markedCoherent a x) u := by
  simp only [phaseResidual, calibrationResponse, markedEnvelope, markedCoherent,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  change (∑ i, ((starRingEnd ℂ) u.val * a i x).re) =
    Complex.reAddGroupHom (∑ i, (starRingEnd ℂ) u.val * a i x)
  rw [map_sum]
  rfl

/-- Exact one-stage disintegration of variation into nonnegative source-marked residuals. -/
theorem markedVariationDefect_sourceAncestry [Fintype X] [Fintype I]
    (T : FinitePositiveKernel X Y) (a : I → X → ℂ) (y : Y) :
    markedVariationDefect T a y =
      T.applyReal
        (fun x => ∑ i, phaseResidual
          (coherentCalibrator (markedCoherentOutput T a y)) (a i x)) y := by
  let u := coherentCalibrator (markedCoherentOutput T a y)
  have hsum :
      (fun x => ∑ i, phaseResidual u (a i x)) =
        fun x => calibrationResponse (markedEnvelope a x) (markedCoherent a x) u := by
    funext x
    exact sum_phaseResidual_eq_calibrationResponse a x u
  rw [hsum]
  rw [congrFun (applyReal_calibrationResponse T (markedEnvelope a) (markedCoherent a) u) y]
  exact (markedCalibrationSpectrum_ground T a y).symm

/-- Observer loss is the exact residual ancestry of intermediate coherent outputs against the
final calibrator. -/
theorem positiveObserverLoss_ancestry [Fintype Y]
    (S : FinitePositiveKernel Y Z) (c : Y → ℂ) (z : Z) :
    positiveObserverLoss S c z =
      S.applyReal
        (fun y => phaseResidual (coherentCalibrator (S.applyComplex c z)) (c y)) z := by
  change S.applyReal (fun y => ‖c y‖) z - ‖S.applyComplex c z‖ = _
  rw [show S.applyReal (fun y => ‖c y‖) z - ‖S.applyComplex c z‖ =
      calibrationResponse (S.applyReal (fun y => ‖c y‖) z) (S.applyComplex c z)
        (coherentCalibrator (S.applyComplex c z)) by
      exact (calibrationResponse_coherentCalibrator
        (S.applyReal (fun y => ‖c y‖) z) (S.applyComplex c z)).symm]
  rw [← congrFun (applyReal_calibrationResponse S (fun y => ‖c y‖) c
    (coherentCalibrator (S.applyComplex c z))) z]
  rfl

/-- Serial ancestry conservation: total defect is inherited source residual plus observer-created
phase frustration, both nonnegative. -/
theorem markedVariationDefect_serialAncestry [Fintype X] [Fintype Y] [Fintype I]
    (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y)
    (a : I → X → ℂ) (z : Z) :
    markedVariationDefect (S.comp T) a z =
      S.applyReal (markedVariationDefect T a) z +
        S.applyReal
          (fun y => phaseResidual
            (coherentCalibrator (markedCoherentOutput (S.comp T) a z))
            (markedCoherentOutput T a y)) z := by
  have hchain := congrFun (markedVariationDefect_observerChain S T a) z
  rw [hchain]
  congr 1
  rw [show markedCoherentOutput (S.comp T) a =
      S.applyComplex (markedCoherentOutput T a) by
        exact S.applyComplex_comp T (markedCoherent a)]
  exact positiveObserverLoss_ancestry S (markedCoherentOutput T a) z

/-- Conservative generation translates the entire calibration spectrum vertically by the
positive refinement excess. -/
theorem markedCalibrationSpectrum_refinement [Fintype X] [Fintype I] [Fintype J]
    (T : FinitePositiveKernel X Y) (R : MarkedRefinement (I := I) (J := J) X)
    (y : Y) (u : UnitCalibrator) :
    markedCalibrationSpectrum T R.fine y u =
      markedCalibrationSpectrum T R.coarse y u + T.applyReal (refinementExcess R) y := by
  have hcoherent :
      markedCoherentOutput T R.fine = markedCoherentOutput T R.coarse := by
    unfold markedCoherentOutput
    rw [R.coherent_eq]
  have hexcess :
      T.applyReal (refinementExcess R) =
        fun y => markedEnvelopeOutput T R.fine y - markedEnvelopeOutput T R.coarse y := by
    rw [show refinementExcess R =
      fun x => markedEnvelope R.fine x - markedEnvelope R.coarse x from rfl]
    rw [T.applyReal_sub]
    rfl
  unfold markedCalibrationSpectrum calibrationResponse
  rw [hcoherent, congrFun hexcess y]
  ring

end MarkedCalibration

/-- Cosine normal form of a one-phase calibration response. -/
def phaseCosineResponse (envelope stiffness phase theta : ℝ) : ℝ :=
  envelope - stiffness * Real.cos (theta - phase)

/-- Velocity field of the cosine calibration response. -/
def phaseCosineVelocity (stiffness phase theta : ℝ) : ℝ :=
  stiffness * Real.sin (theta - phase)

/-- The calibration response is stationary at its selected phase. -/
theorem phaseCosineResponse_hasDerivAt_min
    (envelope stiffness phase : ℝ) :
    HasDerivAt (phaseCosineResponse envelope stiffness phase) 0 phase := by
  have hsub : HasDerivAt (fun theta : ℝ => theta - phase) 1 phase :=
    (hasDerivAt_id phase).sub_const phase
  have hcos := hsub.cos
  have hscaled := hcos.const_mul stiffness
  have hresponse := hscaled.const_sub envelope
  change HasDerivAt
    (fun theta : ℝ => envelope - stiffness * Real.cos (theta - phase)) 0 phase
  simpa using hresponse

/-- The derivative of response velocity at the selected phase is exactly the coherent stiffness. -/
theorem phaseCosineVelocity_hasDerivAt_min (stiffness phase : ℝ) :
    HasDerivAt (phaseCosineVelocity stiffness phase) stiffness phase := by
  have hsub : HasDerivAt (fun theta : ℝ => theta - phase) 1 phase :=
    (hasDerivAt_id phase).sub_const phase
  have hsin := hsub.sin
  have hscaled := hsin.const_mul stiffness
  change HasDerivAt
    (fun theta : ℝ => stiffness * Real.sin (theta - phase)) stiffness phase
  simpa using hscaled

/-- Observer frustration is exactly local coherent stiffness minus observed coherent stiffness. -/
theorem responseStiffness_conservation {Y Z : Type*} [Fintype Y]
    (S : FinitePositiveKernel Y Z) (c : Y → ℂ) (z : Z) :
    S.applyReal (fun y => ‖c y‖) z =
      ‖S.applyComplex c z‖ + positiveObserverLoss S c z := by
  simp [positiveObserverLoss]

/-- Calibration-spectrum capstone: reconstruction, ground attainment, observer exchange, source
ancestry, serial conservation, and stiffness conservation hold in one closed theorem package. -/
theorem calibrationSpectrumMechanics_capstone {X Y Z I : Type*}
    [Fintype X] [Fintype Y] [Fintype I]
    (S : FinitePositiveKernel Y Z) (T : FinitePositiveKernel X Y)
    (a : I → X → ℂ) (z : Z) :
    markedCalibrationSpectrum (S.comp T) a z
        (coherentCalibrator (markedCoherentOutput (S.comp T) a z)) =
        markedVariationDefect (S.comp T) a z ∧
      markedVariationDefect (S.comp T) a z =
        S.applyReal (markedVariationDefect T a) z +
          S.applyReal
            (fun y => phaseResidual
              (coherentCalibrator (markedCoherentOutput (S.comp T) a z))
              (markedCoherentOutput T a y)) z ∧
      S.applyReal (fun y => ‖markedCoherentOutput T a y‖) z =
        ‖S.applyComplex (markedCoherentOutput T a) z‖ +
          positiveObserverLoss S (markedCoherentOutput T a) z := by
  exact ⟨markedCalibrationSpectrum_ground (S.comp T) a z,
    markedVariationDefect_serialAncestry S T a z,
    responseStiffness_conservation S (markedCoherentOutput T a) z⟩

end

end GaloisForLFunctions.HTGeometry
