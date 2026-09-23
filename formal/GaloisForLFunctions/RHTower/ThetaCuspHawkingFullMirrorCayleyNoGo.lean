import GaloisForLFunctions.RHTower.ThetaCuspHawkingTimelikeMirrorRealizationEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingKMSCayleyScatteringMixingEndpoint

/-!
# Full theta-mirror second jet obstructs the Cayley completion

For the physical timelike ray

`p_lambda(v) = v + lambda * thetaCuspFullSource(v)`,

the exact Davies--Fulling pair numerator contains the nonlinear phase

`exp(-i * lambda * omega_out * thetaCuspFullSource(v))`.

After subtracting the inertial distribution, its coupling derivative at zero is the established
Xi-valued Born kernel.  Its second derivative is instead

`2 * omega_in * omega_out^(2 : ℕ) * Fourier(thetaCuspFullSource^(2 : ℕ))(omega_in + omega_out)`.

The theta source is everywhere positive, so the square transform is nonzero on a nonempty open
interval of positive physical frequencies.  The canonical Cayley transition is odd in the
coupling and has zero second derivative.  Hence the exact moving-mirror S-matrix cannot equal the
sectorwise Cayley completion, even locally in coupling.

This is a source-specific obstruction, not a generic complaint about unitarization.  It also
identifies the correct nonlinear replacement: the full mirror carries a hierarchy of Fourier
transforms of powers of the theta source and mixes frequencies through an integral kernel.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-! ## Exact renormalized Davies--Fulling numerator -/

/-- Inertial-subtracted integrand of the exact Davies--Fulling pair numerator.  The subtraction
removes the nonintegrable inertial plane wave; at positive pair frequency its distributional
contribution is zero. -/
def thetaCuspMovingMirrorFullRenormalizedIntegrand
    (lambda outgoingFrequency incomingFrequency v : ℝ) : ℂ :=
  let g := thetaCuspFullSource v
  let g' := deriv thetaCuspFullSource v
  let totalFrequency := incomingFrequency + outgoingFrequency
  let phaseRate := ((-outgoingFrequency * g : ℝ) : ℂ) * Complex.I
  let slope := ((outgoingFrequency * g' : ℝ) : ℂ)
  Complex.exp (((-totalFrequency * v : ℝ) : ℂ) * Complex.I) *
    (Complex.exp ((lambda : ℂ) * phaseRate) *
        (((outgoingFrequency - incomingFrequency : ℝ) : ℂ) + (lambda : ℂ) * slope) -
      ((outgoingFrequency - incomingFrequency : ℝ) : ℂ))

/-- Exact inertial-subtracted Davies--Fulling pair numerator for the theta mirror family. -/
def thetaCuspMovingMirrorFullRenormalizedRaw
    (lambda outgoingFrequency incomingFrequency : ℝ) : ℂ :=
  ∫ v : ℝ, thetaCuspMovingMirrorFullRenormalizedIntegrand
    lambda outgoingFrequency incomingFrequency v

/-- Pointwise first coupling derivative of the full mirror integrand. -/
def thetaCuspMovingMirrorFullFirstJetIntegrand
    (lambda outgoingFrequency incomingFrequency v : ℝ) : ℂ :=
  let g := thetaCuspFullSource v
  let g' := deriv thetaCuspFullSource v
  let totalFrequency := incomingFrequency + outgoingFrequency
  let phaseRate := ((-outgoingFrequency * g : ℝ) : ℂ) * Complex.I
  let phase := Complex.exp ((lambda : ℂ) * phaseRate)
  let slope := ((outgoingFrequency * g' : ℝ) : ℂ)
  Complex.exp (((-totalFrequency * v : ℝ) : ℂ) * Complex.I) *
    (phaseRate * phase *
        (((outgoingFrequency - incomingFrequency : ℝ) : ℂ) +
          (lambda : ℂ) * slope) + phase * slope)

/-- Pointwise second coupling derivative of the full mirror integrand. -/
def thetaCuspMovingMirrorFullSecondJetIntegrand
    (lambda outgoingFrequency incomingFrequency v : ℝ) : ℂ :=
  let g := thetaCuspFullSource v
  let g' := deriv thetaCuspFullSource v
  let totalFrequency := incomingFrequency + outgoingFrequency
  let phaseRate := ((-outgoingFrequency * g : ℝ) : ℂ) * Complex.I
  let phase := Complex.exp ((lambda : ℂ) * phaseRate)
  let slope := ((outgoingFrequency * g' : ℝ) : ℂ)
  Complex.exp (((-totalFrequency * v : ℝ) : ℂ) * Complex.I) *
    (phaseRate ^ (2 : ℕ) * phase *
        (((outgoingFrequency - incomingFrequency : ℝ) : ℂ) +
          (lambda : ℂ) * slope) +
      2 * phaseRate * phase * slope)

/-- The displayed first jet is the actual pointwise coupling derivative of the exact integrand. -/
theorem hasDerivAt_thetaCuspMovingMirrorFullRenormalizedIntegrand
    (lambda outgoingFrequency incomingFrequency v : ℝ) :
    HasDerivAt
      (fun coupling : ℝ => thetaCuspMovingMirrorFullRenormalizedIntegrand
        coupling outgoingFrequency incomingFrequency v)
      (thetaCuspMovingMirrorFullFirstJetIntegrand
        lambda outgoingFrequency incomingFrequency v)
      lambda := by
  unfold thetaCuspMovingMirrorFullRenormalizedIntegrand
    thetaCuspMovingMirrorFullFirstJetIntegrand
  dsimp only
  let base := Complex.exp
    (((-(incomingFrequency + outgoingFrequency) * v : ℝ) : ℂ) * Complex.I)
  let rate := ((-outgoingFrequency * thetaCuspFullSource v : ℝ) : ℂ) * Complex.I
  let slope := ((outgoingFrequency * deriv thetaCuspFullSource v : ℝ) : ℂ)
  let offset := ((outgoingFrequency - incomingFrequency : ℝ) : ℂ)
  let phase : ℝ → ℂ := fun coupling => Complex.exp ((coupling : ℂ) * rate)
  let affine : ℝ → ℂ := fun coupling => offset + (coupling : ℂ) * slope
  change HasDerivAt
    (fun coupling => base * (phase coupling * affine coupling - offset))
    (base * (rate * phase lambda * affine lambda + phase lambda * slope)) lambda
  have hlambda : HasDerivAt (fun coupling : ℝ => (coupling : ℂ)) 1 lambda :=
    (hasDerivAt_id lambda).ofReal_comp
  have hphase : HasDerivAt phase (phase lambda * rate) lambda := by
    simpa [phase] using (hlambda.mul_const rate).cexp
  have haffine : HasDerivAt affine slope lambda := by
    simpa [affine] using (hlambda.mul_const slope).const_add offset
  have hmain := ((hphase.mul haffine).sub_const offset).const_mul base
  have hmain' : HasDerivAt
      (fun coupling => base * (phase coupling * affine coupling - offset))
      (base * (phase lambda * rate * affine lambda + phase lambda * slope)) lambda := by
    simpa only [Pi.mul_apply] using hmain
  rw [show base * (rate * phase lambda * affine lambda + phase lambda * slope) =
      base * (phase lambda * rate * affine lambda + phase lambda * slope) by ring]
  exact hmain'

/-- The displayed second jet is the actual derivative of the first coupling jet. -/
theorem hasDerivAt_thetaCuspMovingMirrorFullFirstJetIntegrand
    (lambda outgoingFrequency incomingFrequency v : ℝ) :
    HasDerivAt
      (fun coupling : ℝ => thetaCuspMovingMirrorFullFirstJetIntegrand
        coupling outgoingFrequency incomingFrequency v)
      (thetaCuspMovingMirrorFullSecondJetIntegrand
        lambda outgoingFrequency incomingFrequency v)
      lambda := by
  unfold thetaCuspMovingMirrorFullFirstJetIntegrand
    thetaCuspMovingMirrorFullSecondJetIntegrand
  dsimp only
  let base := Complex.exp
    (((-(incomingFrequency + outgoingFrequency) * v : ℝ) : ℂ) * Complex.I)
  let rate := ((-outgoingFrequency * thetaCuspFullSource v : ℝ) : ℂ) * Complex.I
  let slope := ((outgoingFrequency * deriv thetaCuspFullSource v : ℝ) : ℂ)
  let offset := ((outgoingFrequency - incomingFrequency : ℝ) : ℂ)
  let phase : ℝ → ℂ := fun coupling => Complex.exp ((coupling : ℂ) * rate)
  let affine : ℝ → ℂ := fun coupling => offset + (coupling : ℂ) * slope
  change HasDerivAt
    (fun coupling => base *
      (rate * phase coupling * affine coupling + phase coupling * slope))
    (base * (rate ^ (2 : ℕ) * phase lambda * affine lambda +
      2 * rate * phase lambda * slope)) lambda
  have hlambda : HasDerivAt (fun coupling : ℝ => (coupling : ℂ)) 1 lambda :=
    (hasDerivAt_id lambda).ofReal_comp
  have hphase : HasDerivAt phase (phase lambda * rate) lambda := by
    simpa [phase] using (hlambda.mul_const rate).cexp
  have haffine : HasDerivAt affine slope lambda := by
    simpa [affine] using (hlambda.mul_const slope).const_add offset
  have hfirst : HasDerivAt
      (fun coupling => rate * phase coupling * affine coupling + phase coupling * slope)
      (rate * (phase lambda * rate) * affine lambda + rate * phase lambda * slope +
        (phase lambda * rate) * slope) lambda := by
    exact ((hphase.const_mul rate).mul haffine).add (hphase.mul_const slope)
  have hmain := hfirst.const_mul base
  have hmain' : HasDerivAt
      (fun coupling => base *
        (rate * phase coupling * affine coupling + phase coupling * slope))
      (base * (rate * (phase lambda * rate) * affine lambda +
        rate * phase lambda * slope + (phase lambda * rate) * slope)) lambda := by
    simpa only [Pi.add_apply, Pi.mul_apply] using hmain
  rw [show base * (rate ^ (2 : ℕ) * phase lambda * affine lambda +
      2 * rate * phase lambda * slope) =
      base * (rate * (phase lambda * rate) * affine lambda +
        rate * phase lambda * slope + (phase lambda * rate) * slope) by ring]
  exact hmain'

/-! ## Dominated coupling differentiation of the full mirror integral -/

private theorem norm_thetaCuspMovingMirrorFullFirstJetIntegrand_le
    (lambda frequency v B : ℝ) (hlambda : |lambda| ≤ B) (hB : 0 ≤ B) :
    ‖thetaCuspMovingMirrorFullFirstJetIntegrand lambda frequency frequency v‖ ≤
      ((|frequency| * thetaCuspDerivativeExpConstant 0 * B + 1) *
        (|frequency| * thetaCuspDerivativeExpConstant 1)) * Real.exp (-|v|) := by
  let C0 := thetaCuspDerivativeExpConstant 0
  let C1 := thetaCuspDerivativeExpConstant 1
  have hC0 : 0 ≤ C0 := thetaCuspDerivativeExpConstant_nonneg 0
  have hC1 : 0 ≤ C1 := thetaCuspDerivativeExpConstant_nonneg 1
  let rate : ℂ := ((-frequency * thetaCuspFullSource v : ℝ) : ℂ) * Complex.I
  let phase : ℂ := Complex.exp ((lambda : ℂ) * rate)
  let slope : ℂ := ((frequency * deriv thetaCuspFullSource v : ℝ) : ℂ)
  have hphase : ‖phase‖ = 1 := by
    dsimp [phase, rate]
    rw [Complex.norm_exp]
    norm_num
  have hrate : ‖rate‖ ≤ |frequency| * C0 := by
    dsimp [rate]
    rw [norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (by
        have hg := abs_thetaCuspFullSource_le v
        have he : Real.exp (-|v|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg v))
        exact hg.trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left he hC0))
      (abs_nonneg frequency)
  have hslope : ‖slope‖ ≤ |frequency| * C1 * Real.exp (-|v|) := by
    dsimp [slope]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hg' := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 1 v
    rw [iteratedDeriv_one] at hg'
    simpa [C1, mul_assoc] using mul_le_mul_of_nonneg_left hg' (abs_nonneg frequency)
  have hlambdaNorm : ‖(lambda : ℂ)‖ ≤ B := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hlambda
  have hbase :
      ‖Complex.exp (((-(frequency + frequency) * v : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num
  unfold thetaCuspMovingMirrorFullFirstJetIntegrand
  dsimp only
  simp only [sub_self, ofReal_zero, zero_add]
  rw [norm_mul, hbase, one_mul]
  change ‖rate * phase * ((lambda : ℂ) * slope) + phase * slope‖ ≤
    ((|frequency| * C0 * B + 1) * (|frequency| * C1)) * Real.exp (-|v|)
  calc
    ‖rate * phase * ((lambda : ℂ) * slope) + phase * slope‖ ≤
        ‖rate * phase * ((lambda : ℂ) * slope)‖ + ‖phase * slope‖ := norm_add_le _ _
    _ = ‖rate‖ * ‖phase‖ * (‖(lambda : ℂ)‖ * ‖slope‖) +
        ‖phase‖ * ‖slope‖ := by simp only [norm_mul]
    _ ≤ (|frequency| * C0) * 1 *
          (B * (|frequency| * C1 * Real.exp (-|v|))) +
        1 * (|frequency| * C1 * Real.exp (-|v|)) := by
      rw [hphase]
      gcongr
    _ = ((|frequency| * C0 * B + 1) * (|frequency| * C1)) *
        Real.exp (-|v|) := by ring

private theorem norm_thetaCuspMovingMirrorFullSecondJetIntegrand_le
    (lambda frequency v B : ℝ) (hlambda : |lambda| ≤ B) (hB : 0 ≤ B) :
    ‖thetaCuspMovingMirrorFullSecondJetIntegrand lambda frequency frequency v‖ ≤
      (((|frequency| * thetaCuspDerivativeExpConstant 0) ^ (2 : ℕ) * B +
          2 * (|frequency| * thetaCuspDerivativeExpConstant 0)) *
        (|frequency| * thetaCuspDerivativeExpConstant 1)) * Real.exp (-|v|) := by
  let C0 := thetaCuspDerivativeExpConstant 0
  let C1 := thetaCuspDerivativeExpConstant 1
  have hC0 : 0 ≤ C0 := thetaCuspDerivativeExpConstant_nonneg 0
  have hC1 : 0 ≤ C1 := thetaCuspDerivativeExpConstant_nonneg 1
  let rate : ℂ := ((-frequency * thetaCuspFullSource v : ℝ) : ℂ) * Complex.I
  let phase : ℂ := Complex.exp ((lambda : ℂ) * rate)
  let slope : ℂ := ((frequency * deriv thetaCuspFullSource v : ℝ) : ℂ)
  have hphase : ‖phase‖ = 1 := by
    dsimp [phase, rate]
    rw [Complex.norm_exp]
    norm_num
  have hrate : ‖rate‖ ≤ |frequency| * C0 := by
    dsimp [rate]
    rw [norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (by
        have hg := abs_thetaCuspFullSource_le v
        have he : Real.exp (-|v|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg v))
        exact hg.trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left he hC0))
      (abs_nonneg frequency)
  have hslope : ‖slope‖ ≤ |frequency| * C1 * Real.exp (-|v|) := by
    dsimp [slope]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hg' := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 1 v
    rw [iteratedDeriv_one] at hg'
    simpa [C1, mul_assoc] using mul_le_mul_of_nonneg_left hg' (abs_nonneg frequency)
  have hlambdaNorm : ‖(lambda : ℂ)‖ ≤ B := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hlambda
  have hbase :
      ‖Complex.exp (((-(frequency + frequency) * v : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num
  unfold thetaCuspMovingMirrorFullSecondJetIntegrand
  dsimp only
  simp only [sub_self, ofReal_zero, zero_add]
  rw [norm_mul, hbase, one_mul]
  change ‖rate ^ (2 : ℕ) * phase * ((lambda : ℂ) * slope) + 2 * rate * phase * slope‖ ≤
    (((|frequency| * C0) ^ (2 : ℕ) * B + 2 * (|frequency| * C0)) *
      (|frequency| * C1)) * Real.exp (-|v|)
  calc
    ‖rate ^ (2 : ℕ) * phase * ((lambda : ℂ) * slope) + 2 * rate * phase * slope‖ ≤
        ‖rate ^ (2 : ℕ) * phase * ((lambda : ℂ) * slope)‖ +
          ‖(2 : ℂ) * rate * phase * slope‖ := norm_add_le _ _
    _ = ‖rate‖ ^ (2 : ℕ) * ‖phase‖ * (‖(lambda : ℂ)‖ * ‖slope‖) +
          2 * ‖rate‖ * ‖phase‖ * ‖slope‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
    _ ≤ (|frequency| * C0) ^ (2 : ℕ) * 1 *
          (B * (|frequency| * C1 * Real.exp (-|v|))) +
        2 * (|frequency| * C0) * 1 *
          (|frequency| * C1 * Real.exp (-|v|)) := by
      rw [hphase]
      gcongr
    _ = (((|frequency| * C0) ^ (2 : ℕ) * B + 2 * (|frequency| * C0)) *
          (|frequency| * C1)) * Real.exp (-|v|) := by ring

private theorem measurable_thetaCuspMovingMirrorFullRenormalizedIntegrand
    (lambda frequency : ℝ) :
    AEStronglyMeasurable (fun v : ℝ =>
      thetaCuspMovingMirrorFullRenormalizedIntegrand lambda frequency frequency v) := by
  apply Continuous.aestronglyMeasurable
  have hg : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
  have hg' : Continuous (deriv thetaCuspFullSource) :=
    contDiff_thetaCuspFullSource.continuous_deriv (by simp)
  unfold thetaCuspMovingMirrorFullRenormalizedIntegrand
  fun_prop (disch := assumption)

private theorem measurable_thetaCuspMovingMirrorFullFirstJetIntegrand
    (lambda frequency : ℝ) :
    AEStronglyMeasurable (fun v : ℝ =>
      thetaCuspMovingMirrorFullFirstJetIntegrand lambda frequency frequency v) := by
  apply Continuous.aestronglyMeasurable
  have hg : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
  have hg' : Continuous (deriv thetaCuspFullSource) :=
    contDiff_thetaCuspFullSource.continuous_deriv (by simp)
  unfold thetaCuspMovingMirrorFullFirstJetIntegrand
  fun_prop (disch := assumption)

private theorem measurable_thetaCuspMovingMirrorFullSecondJetIntegrand
    (lambda frequency : ℝ) :
    AEStronglyMeasurable (fun v : ℝ =>
      thetaCuspMovingMirrorFullSecondJetIntegrand lambda frequency frequency v) := by
  apply Continuous.aestronglyMeasurable
  have hg : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
  have hg' : Continuous (deriv thetaCuspFullSource) :=
    contDiff_thetaCuspFullSource.continuous_deriv (by simp)
  unfold thetaCuspMovingMirrorFullSecondJetIntegrand
  fun_prop (disch := assumption)

private theorem norm_thetaCuspMovingMirrorFullRenormalizedIntegrand_le
    (lambda frequency v B : ℝ) (hlambda : |lambda| ≤ B) (hB : 0 ≤ B) :
    ‖thetaCuspMovingMirrorFullRenormalizedIntegrand lambda frequency frequency v‖ ≤
      (B * (|frequency| * thetaCuspDerivativeExpConstant 1)) * Real.exp (-|v|) := by
  let C1 := thetaCuspDerivativeExpConstant 1
  have hC1 : 0 ≤ C1 := thetaCuspDerivativeExpConstant_nonneg 1
  let rate : ℂ := ((-frequency * thetaCuspFullSource v : ℝ) : ℂ) * Complex.I
  let phase : ℂ := Complex.exp ((lambda : ℂ) * rate)
  let slope : ℂ := ((frequency * deriv thetaCuspFullSource v : ℝ) : ℂ)
  have hphase : ‖phase‖ = 1 := by
    dsimp [phase, rate]
    rw [Complex.norm_exp]
    norm_num
  have hslope : ‖slope‖ ≤ |frequency| * C1 * Real.exp (-|v|) := by
    dsimp [slope]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hg' := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 1 v
    rw [iteratedDeriv_one] at hg'
    simpa [C1, mul_assoc] using mul_le_mul_of_nonneg_left hg' (abs_nonneg frequency)
  have hlambdaNorm : ‖(lambda : ℂ)‖ ≤ B := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hlambda
  have hbase :
      ‖Complex.exp (((-(frequency + frequency) * v : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num
  unfold thetaCuspMovingMirrorFullRenormalizedIntegrand
  dsimp only
  simp only [sub_self, ofReal_zero, zero_add, sub_zero]
  rw [norm_mul, hbase, one_mul, norm_mul, hphase, one_mul, norm_mul]
  change ‖(lambda : ℂ)‖ * ‖slope‖ ≤ B * (|frequency| * C1) * Real.exp (-|v|)
  calc
    ‖(lambda : ℂ)‖ * ‖slope‖ ≤ B *
        (|frequency| * C1 * Real.exp (-|v|)) := by gcongr
    _ = B * (|frequency| * C1) * Real.exp (-|v|) := by ring

/-- First coupling derivative commutes with the exact balanced full-mirror integral. -/
theorem hasDerivAt_thetaCuspMovingMirrorFullRenormalizedRaw_balanced
    (lambda frequency : ℝ) :
    HasDerivAt
      (fun coupling : ℝ => thetaCuspMovingMirrorFullRenormalizedRaw
        coupling frequency frequency)
      (∫ v : ℝ, thetaCuspMovingMirrorFullFirstJetIntegrand
        lambda frequency frequency v) lambda := by
  let B : ℝ := |lambda| + 1
  let firstMajorCoefficient : ℝ :=
    (|frequency| * thetaCuspDerivativeExpConstant 0 * B + 1) *
      (|frequency| * thetaCuspDerivativeExpConstant 1)
  let firstMajor : ℝ → ℝ := fun v => firstMajorCoefficient * Real.exp (-|v|)
  let fullMajorCoefficient : ℝ := B *
    (|frequency| * thetaCuspDerivativeExpConstant 1)
  let fullMajor : ℝ → ℝ := fun v => fullMajorCoefficient * Real.exp (-|v|)
  have hB : 0 ≤ B := by dsimp [B]; linarith [abs_nonneg lambda]
  have hcenterB : |lambda| ≤ B := by dsimp [B]; linarith
  have hfirstMajor : Integrable firstMajor :=
    integrable_exp_neg_abs.const_mul firstMajorCoefficient
  have hfullMajor : Integrable fullMajor :=
    integrable_exp_neg_abs.const_mul fullMajorCoefficient
  have hfullInt : Integrable (fun v : ℝ =>
      thetaCuspMovingMirrorFullRenormalizedIntegrand lambda frequency frequency v) := by
    apply hfullMajor.mono
      (measurable_thetaCuspMovingMirrorFullRenormalizedIntegrand lambda frequency)
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg
        (mul_nonneg hB
          (mul_nonneg (abs_nonneg frequency)
            (thetaCuspDerivativeExpConstant_nonneg 1)))
        (Real.exp_pos _).le)]
    exact norm_thetaCuspMovingMirrorFullRenormalizedIntegrand_le
      lambda frequency v B hcenterB hB
  have hdom : ∀ᵐ v : ℝ, ∀ coupling ∈ Metric.ball lambda 1,
      ‖thetaCuspMovingMirrorFullFirstJetIntegrand coupling frequency frequency v‖ ≤
        firstMajor v := by
    filter_upwards with v
    intro coupling hcoupling
    have hdist : |coupling - lambda| < 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hcoupling
    have hcouplingB : |coupling| ≤ B := by
      calc
        |coupling| = |lambda + (coupling - lambda)| := by ring_nf
        _ ≤ |lambda| + |coupling - lambda| := abs_add_le _ _
        _ ≤ B := by dsimp [B]; linarith
    exact norm_thetaCuspMovingMirrorFullFirstJetIntegrand_le
      coupling frequency v B hcouplingB hB
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun coupling v => thetaCuspMovingMirrorFullRenormalizedIntegrand
      coupling frequency frequency v)
    (F' := fun coupling v => thetaCuspMovingMirrorFullFirstJetIntegrand
      coupling frequency frequency v)
    (x₀ := lambda) (s := Metric.ball lambda 1) (bound := firstMajor)
    (Metric.ball_mem_nhds lambda (by norm_num))
    (Filter.Eventually.of_forall fun coupling =>
      measurable_thetaCuspMovingMirrorFullRenormalizedIntegrand coupling frequency)
    hfullInt (measurable_thetaCuspMovingMirrorFullFirstJetIntegrand lambda frequency)
    hdom hfirstMajor
    (by
      filter_upwards with v
      intro coupling _
      exact hasDerivAt_thetaCuspMovingMirrorFullRenormalizedIntegrand
        coupling frequency frequency v)
  exact hresult.2

/-- Integrated pointwise first coupling jet in a balanced physical sector. -/
def thetaCuspMovingMirrorFullFirstJetRaw (lambda frequency : ℝ) : ℂ :=
  ∫ v : ℝ, thetaCuspMovingMirrorFullFirstJetIntegrand lambda frequency frequency v

/-- Second coupling derivative commutes with the balanced full-mirror integral at zero. -/
theorem hasDerivAt_thetaCuspMovingMirrorFullFirstJetRaw_zero (frequency : ℝ) :
    HasDerivAt
      (fun coupling : ℝ => thetaCuspMovingMirrorFullFirstJetRaw coupling frequency)
      (∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
        0 frequency frequency v) 0 := by
  let C0 := thetaCuspDerivativeExpConstant 0
  let C1 := thetaCuspDerivativeExpConstant 1
  let firstMajorCoefficient : ℝ :=
    (|frequency| * C0 + 1) * (|frequency| * C1)
  let firstMajor : ℝ → ℝ := fun v => firstMajorCoefficient * Real.exp (-|v|)
  let secondMajorCoefficient : ℝ :=
    ((|frequency| * C0) ^ (2 : ℕ) + 2 * (|frequency| * C0)) *
      (|frequency| * C1)
  let secondMajor : ℝ → ℝ := fun v => secondMajorCoefficient * Real.exp (-|v|)
  have hC0 : 0 ≤ C0 := thetaCuspDerivativeExpConstant_nonneg 0
  have hC1 : 0 ≤ C1 := thetaCuspDerivativeExpConstant_nonneg 1
  have hfirstCoefficient : 0 ≤ firstMajorCoefficient := by
    dsimp [firstMajorCoefficient]
    positivity
  have hsecondCoefficient : 0 ≤ secondMajorCoefficient := by
    dsimp [secondMajorCoefficient]
    positivity
  have hfirstMajor : Integrable firstMajor :=
    integrable_exp_neg_abs.const_mul firstMajorCoefficient
  have hsecondMajor : Integrable secondMajor :=
    integrable_exp_neg_abs.const_mul secondMajorCoefficient
  have hfirstInt : Integrable (fun v : ℝ =>
      thetaCuspMovingMirrorFullFirstJetIntegrand 0 frequency frequency v) := by
    apply hfirstMajor.mono
      (measurable_thetaCuspMovingMirrorFullFirstJetIntegrand 0 frequency)
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hfirstCoefficient (Real.exp_pos _).le)]
    simpa [firstMajorCoefficient, C0, C1] using
      norm_thetaCuspMovingMirrorFullFirstJetIntegrand_le
        0 frequency v 1 (by simp) (by norm_num)
  have hdom : ∀ᵐ v : ℝ, ∀ coupling ∈ Metric.ball (0 : ℝ) 1,
      ‖thetaCuspMovingMirrorFullSecondJetIntegrand coupling frequency frequency v‖ ≤
        secondMajor v := by
    filter_upwards with v
    intro coupling hcoupling
    have hcouplingOne : |coupling| ≤ 1 := by
      have hdist : |coupling| < 1 := by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hcoupling
      exact hdist.le
    simpa [secondMajor, secondMajorCoefficient, C0, C1] using
      norm_thetaCuspMovingMirrorFullSecondJetIntegrand_le
        coupling frequency v 1 hcouplingOne (by norm_num)
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun coupling v => thetaCuspMovingMirrorFullFirstJetIntegrand
      coupling frequency frequency v)
    (F' := fun coupling v => thetaCuspMovingMirrorFullSecondJetIntegrand
      coupling frequency frequency v)
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1) (bound := secondMajor)
    (Metric.ball_mem_nhds 0 (by norm_num))
    (Filter.Eventually.of_forall fun coupling =>
      measurable_thetaCuspMovingMirrorFullFirstJetIntegrand coupling frequency)
    hfirstInt (measurable_thetaCuspMovingMirrorFullSecondJetIntegrand 0 frequency)
    hdom hsecondMajor
    (by
      filter_upwards with v
      intro coupling _
      exact hasDerivAt_thetaCuspMovingMirrorFullFirstJetIntegrand
        coupling frequency frequency v)
  simpa only [thetaCuspMovingMirrorFullFirstJetRaw] using hresult.2

/-- Exact balanced full-mirror raw amplitude has the integrated second jet as second derivative. -/
theorem secondDeriv_thetaCuspMovingMirrorFullRenormalizedRaw_balanced_zero
    (frequency : ℝ) :
    deriv (deriv (fun coupling : ℝ =>
      thetaCuspMovingMirrorFullRenormalizedRaw coupling frequency frequency)) 0 =
      ∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
        0 frequency frequency v := by
  have hfirstDerivative :
      (fun coupling : ℝ => deriv (fun q : ℝ =>
        thetaCuspMovingMirrorFullRenormalizedRaw q frequency frequency) coupling) =
      fun coupling : ℝ => thetaCuspMovingMirrorFullFirstJetRaw coupling frequency := by
    funext coupling
    exact (hasDerivAt_thetaCuspMovingMirrorFullRenormalizedRaw_balanced
      coupling frequency).deriv
  change deriv (fun coupling : ℝ => deriv (fun q : ℝ =>
    thetaCuspMovingMirrorFullRenormalizedRaw q frequency frequency) coupling) 0 = _
  rw [hfirstDerivative]
  exact (hasDerivAt_thetaCuspMovingMirrorFullFirstJetRaw_zero frequency).deriv

/-! ## Source-square transform and nonzero physical second jet -/

/-- Fourier transform of the squared theta source in physical angular-frequency normalization. -/
def thetaCuspSourceSquareFourier (totalFrequency : ℝ) : ℂ :=
  FourierTransform.fourier
    (fun v : ℝ => ((thetaCuspFullSource v : ℂ) ^ (2 : ℕ)))
    (totalFrequency / (2 * Real.pi))

theorem integrable_thetaCuspFullSource_sq_complex :
    Integrable (fun v : ℝ => ((thetaCuspFullSource v : ℂ) ^ (2 : ℕ))) := by
  let C := thetaCuspDerivativeExpConstant 0
  have hC : 0 ≤ C := thetaCuspDerivativeExpConstant_nonneg 0
  have hmajor : Integrable (fun v : ℝ => C ^ (2 : ℕ) * Real.exp (-|v|)) :=
    integrable_exp_neg_abs.const_mul _
  apply hmajor.mono
  · exact ((Complex.continuous_ofReal.comp
      contDiff_thetaCuspFullSource.continuous).pow 2).aestronglyMeasurable
  · filter_upwards with v
    have hg := abs_thetaCuspFullSource_le v
    have hexp : Real.exp (-|v|) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg v))
    have hgC : |thetaCuspFullSource v| ≤ C :=
      hg.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hC)
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (sq_nonneg C) (Real.exp_pos _).le)]
    calc
      |thetaCuspFullSource v| ^ (2 : ℕ) ≤
          (C * Real.exp (-|v|)) ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hg 2
      _ = C ^ (2 : ℕ) * Real.exp (-2 * |v|) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring_nf
      _ ≤ C ^ (2 : ℕ) * Real.exp (-|v|) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith [abs_nonneg v])) (sq_nonneg C)

theorem continuous_thetaCuspSourceSquareFourier :
    Continuous thetaCuspSourceSquareFourier := by
  unfold thetaCuspSourceSquareFourier
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner integrable_thetaCuspFullSource_sq_complex).comp
      (continuous_id.div_const (2 * Real.pi))

theorem thetaCuspSourceSquareFourier_zero_re_pos :
    0 < (thetaCuspSourceSquareFourier 0).re := by
  rw [thetaCuspSourceSquareFourier, zero_div, Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  change 0 < RCLike.re (∫ v : ℝ, ((thetaCuspFullSource v : ℂ) ^ (2 : ℕ)))
  rw [← integral_re integrable_thetaCuspFullSource_sq_complex]
  have hrealEq : (fun v : ℝ => RCLike.re ((thetaCuspFullSource v : ℂ) ^ (2 : ℕ))) =
      fun v : ℝ => thetaCuspFullSource v ^ (2 : ℕ) := by
    funext v
    change ((thetaCuspFullSource v : ℂ) ^ (2 : ℕ)).re = thetaCuspFullSource v ^ (2 : ℕ)
    rw [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hrealEq]
  have hsqReal : Integrable (fun v : ℝ => thetaCuspFullSource v ^ (2 : ℕ)) := by
    rw [← hrealEq]
    exact integrable_thetaCuspFullSource_sq_complex.re
  rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    hsqReal]
  have hsupp : Function.support (fun v : ℝ => thetaCuspFullSource v ^ (2 : ℕ)) = Set.univ := by
    ext v
    simp only [Function.mem_support, ne_eq, mem_univ, iff_true]
    exact pow_ne_zero 2 (thetaCuspFullSource_pos v).ne'
  rw [hsupp]
  simp

theorem exists_pos_thetaCuspSourceSquareFourier_ne_zero :
    ∃ totalFrequency : ℝ, 0 < totalFrequency ∧
      thetaCuspSourceSquareFourier totalFrequency ≠ 0 := by
  have hcont : Continuous fun s : ℝ => (thetaCuspSourceSquareFourier s).re :=
    Complex.continuous_re.comp continuous_thetaCuspSourceSquareFourier
  have hzero := thetaCuspSourceSquareFourier_zero_re_pos
  have hnhds : {s : ℝ | 0 < (thetaCuspSourceSquareFourier s).re} ∈ 𝓝 0 :=
    hcont.isOpen_preimage _ isOpen_Ioi |>.mem_nhds hzero
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨epsilon, hepsilon, hball⟩
  let s := epsilon / 2
  have hspos : 0 < s := half_pos hepsilon
  have hsball : s ∈ Metric.ball (0 : ℝ) epsilon := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hspos]
    exact half_lt_self hepsilon
  have hsre : 0 < (thetaCuspSourceSquareFourier s).re := hball hsball
  exact ⟨s, hspos, fun hzero' => by rw [hzero'] at hsre; simp at hsre⟩

/-- Complex square of the theta source and its ordinary derivative. -/
private def thetaCuspSourceSquare (v : ℝ) : ℂ :=
  (thetaCuspFullSource v : ℂ) ^ (2 : ℕ)

private theorem differentiable_thetaCuspSourceSquare :
    Differentiable ℝ thetaCuspSourceSquare := by
  intro v
  have hreal : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource v) v :=
    (contDiff_thetaCuspFullSource.differentiable (by simp) v).hasDerivAt
  have hcomplex : HasDerivAt (fun x : ℝ => (thetaCuspFullSource x : ℂ))
      ((deriv thetaCuspFullSource v : ℝ) : ℂ) v := hreal.ofReal_comp
  exact (hcomplex.pow 2).differentiableAt

private theorem deriv_thetaCuspSourceSquare (v : ℝ) :
    deriv thetaCuspSourceSquare v =
      2 * (thetaCuspFullSource v : ℂ) *
        ((deriv thetaCuspFullSource v : ℝ) : ℂ) := by
  unfold thetaCuspSourceSquare
  let d : ℝ := deriv thetaCuspFullSource v
  have hreal : HasDerivAt thetaCuspFullSource d v :=
    (contDiff_thetaCuspFullSource.differentiable (by simp) v).hasDerivAt
  have hcomplex : HasDerivAt (fun x : ℝ => (thetaCuspFullSource x : ℂ))
      (d : ℂ) v := hreal.ofReal_comp
  have heq : (fun x : ℝ => (thetaCuspFullSource x : ℂ) ^ (2 : ℕ)) =
      (fun x : ℝ => (thetaCuspFullSource x : ℂ)) *
        (fun x : ℝ => (thetaCuspFullSource x : ℂ)) := by
    funext x
    simp only [Pi.mul_apply, pow_two]
  rw [heq]
  simpa [pow_two, d] using (hcomplex.pow 2).deriv

private theorem integrable_deriv_thetaCuspSourceSquare :
    Integrable (deriv thetaCuspSourceSquare) := by
  let C0 := thetaCuspDerivativeExpConstant 0
  let C1 := thetaCuspDerivativeExpConstant 1
  have hC0 : 0 ≤ C0 := thetaCuspDerivativeExpConstant_nonneg 0
  have hC1 : 0 ≤ C1 := thetaCuspDerivativeExpConstant_nonneg 1
  have hmajor : Integrable
      (fun v : ℝ => 2 * C0 * C1 * Real.exp (-|v|)) :=
    integrable_exp_neg_abs.const_mul _
  apply hmajor.mono'
  · rw [show deriv thetaCuspSourceSquare = fun v : ℝ =>
        2 * (thetaCuspFullSource v : ℂ) *
          ((deriv thetaCuspFullSource v : ℝ) : ℂ) by
      funext v
      exact deriv_thetaCuspSourceSquare v]
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp
      contDiff_thetaCuspFullSource.continuous)).mul
        (Complex.continuous_ofReal.comp
          (contDiff_thetaCuspFullSource.continuous_deriv (by simp)))).aestronglyMeasurable
  · filter_upwards with v
    rw [deriv_thetaCuspSourceSquare, norm_mul, norm_mul,
      Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hg := abs_thetaCuspFullSource_le v
    have hg' := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 1 v
    rw [iteratedDeriv_one] at hg'
    calc
      2 * |thetaCuspFullSource v| * |deriv thetaCuspFullSource v| ≤
          2 * (C0 * Real.exp (-|v|)) * (C1 * Real.exp (-|v|)) := by gcongr
      _ = 2 * C0 * C1 * Real.exp (-2 * |v|) := by
        ring_nf
        rw [← Real.exp_nat_mul]
        ring_nf
      _ ≤ 2 * C0 * C1 * Real.exp (-|v|) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith [abs_nonneg v]))
          (mul_nonneg (mul_nonneg (by norm_num) hC0) hC1)

/-- Exact source-square normal form of the balanced physical full-mirror second coupling jet. -/
theorem integral_thetaCuspMovingMirrorFullSecondJetIntegrand_zero_balanced
    (frequency : ℝ) :
    (∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
      0 frequency frequency v) =
      (2 * frequency ^ (3 : ℕ) : ℝ) * thetaCuspSourceSquareFourier (2 * frequency) := by
  have hFourierDeriv := congrFun
    (Real.fourier_deriv
      (f := thetaCuspSourceSquare)
      (by
        change Integrable (fun v : ℝ => ((thetaCuspFullSource v : ℂ) ^ (2 : ℕ)))
        exact integrable_thetaCuspFullSource_sq_complex)
      differentiable_thetaCuspSourceSquare
      integrable_deriv_thetaCuspSourceSquare)
    (frequency / Real.pi)
  have hscale : 2 * frequency / (2 * Real.pi) = frequency / Real.pi := by
    field_simp [Real.pi_ne_zero]
  have hphaseDeriv :
      (∫ v : ℝ,
        Complex.exp (((-2 * frequency * v : ℝ) : ℂ) * Complex.I) *
          deriv thetaCuspSourceSquare v) =
        FourierTransform.fourier (deriv thetaCuspSourceSquare)
          (frequency / Real.pi) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with v
    simp only [smul_eq_mul]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [thetaCuspSourceSquareFourier, hscale]
  calc
    (∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
        0 frequency frequency v) =
        (-Complex.I * (frequency : ℂ) ^ (2 : ℕ)) *
          ∫ v : ℝ,
            Complex.exp (((-2 * frequency * v : ℝ) : ℂ) * Complex.I) *
              deriv thetaCuspSourceSquare v := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with v
        rw [deriv_thetaCuspSourceSquare]
        unfold thetaCuspMovingMirrorFullSecondJetIntegrand
        dsimp only
        simp only [zero_mul, ofReal_zero, Complex.exp_zero]
        push_cast
        ring
    _ = (-Complex.I * (frequency : ℂ) ^ (2 : ℕ)) *
          FourierTransform.fourier (deriv thetaCuspSourceSquare)
            (frequency / Real.pi) := by rw [hphaseDeriv]
    _ = (-Complex.I * (frequency : ℂ) ^ (2 : ℕ)) *
          ((2 * (Real.pi : ℂ) * Complex.I * (frequency / Real.pi : ℝ)) •
            FourierTransform.fourier thetaCuspSourceSquare
              (frequency / Real.pi)) := by rw [hFourierDeriv]
    _ = (2 * frequency ^ (3 : ℕ) : ℝ) *
          FourierTransform.fourier thetaCuspSourceSquare
            (frequency / Real.pi) := by
        simp only [smul_eq_mul]
        push_cast
        field_simp [Real.pi_ne_zero]
        rw [Complex.I_sq]
        ring

/-- Some balanced positive physical mirror sector has a nonzero second coupling jet. -/
theorem exists_balanced_pos_fullMirror_secondJet_ne_zero :
    ∃ frequency : ℝ, 0 < frequency ∧
      (∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
        0 frequency frequency v) ≠ 0 := by
  rcases exists_pos_thetaCuspSourceSquareFourier_ne_zero with ⟨s, hs, hsq⟩
  let frequency := s / 2
  have hfrequency : 0 < frequency := half_pos hs
  refine ⟨frequency, hfrequency, ?_⟩
  rw [integral_thetaCuspMovingMirrorFullSecondJetIntegrand_zero_balanced]
  have hsum : 2 * frequency = s := by dsimp only [frequency]; ring
  rw [hsum]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hfrequency.ne'))
  · exact hsq

/-- Some positive balanced sector has a genuinely nonzero second derivative of the exact raw
Davies--Fulling amplitude, after both dominated differentiation steps have been discharged. -/
theorem exists_balanced_pos_fullMirror_secondDeriv_ne_zero :
    ∃ frequency : ℝ, 0 < frequency ∧
      deriv (deriv (fun coupling : ℝ =>
        thetaCuspMovingMirrorFullRenormalizedRaw coupling frequency frequency)) 0 ≠ 0 := by
  rcases exists_balanced_pos_fullMirror_secondJet_ne_zero with ⟨frequency, hfrequency, hne⟩
  refine ⟨frequency, hfrequency, ?_⟩
  rw [secondDeriv_thetaCuspMovingMirrorFullRenormalizedRaw_balanced_zero]
  exact hne

/-! ## Cayley mismatch -/

/-- Every canonical Cayley transition is odd in the coupling, hence has no even coupling jet. -/
theorem thetaCuspHawkingCayleyTransition_neg
    (lambda a omega : ℝ) :
    thetaCuspHawkingCayleyTransition (-lambda) a omega =
      -thetaCuspHawkingCayleyTransition lambda a omega := by
  unfold thetaCuspHawkingCayleyTransition thetaCuspHawkingCayleyLoad
  push_cast
  rw [neg_sq]
  ring

/-- Every finite central second difference of a canonical Cayley transition vanishes exactly. -/
theorem thetaCuspHawkingCayleyTransition_centralSecondDifference_zero
    (lambda a omega : ℝ) :
    thetaCuspHawkingCayleyTransition lambda a omega +
        thetaCuspHawkingCayleyTransition (-lambda) a omega -
      2 * thetaCuspHawkingCayleyTransition 0 a omega = 0 := by
  rw [thetaCuspHawkingCayleyTransition_neg]
  simp [thetaCuspHawkingCayleyTransition]

/-- **[FALSIFIED] Canonical Cayley/full-mirror identification.**  Exact theta-mirror dynamics
has a nonzero even coupling jet in a positive balanced sector, while every Cayley block has zero
second jet.  Therefore the Cayley completion cannot be the full nonperturbative theta-mirror
S-matrix. -/
theorem no_fullThetaMirror_eq_canonicalCayley_at_all_balanced_frequencies :
    ¬ (∀ frequency : ℝ, 0 < frequency →
      deriv (deriv (fun coupling : ℝ =>
        thetaCuspMovingMirrorFullRenormalizedRaw coupling frequency frequency)) 0 = 0) := by
  rintro hall
  rcases exists_balanced_pos_fullMirror_secondDeriv_ne_zero with
    ⟨frequency, hfrequency, hne⟩
  exact hne (hall frequency hfrequency)

end RHTower
