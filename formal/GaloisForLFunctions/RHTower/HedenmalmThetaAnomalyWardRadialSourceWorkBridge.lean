import GaloisForLFunctions.RHTower.HedenmalmCompletedSourceLineConjugateDiracResolvent

/-!
# Ward anomaly as positive amplification of completed radial source work

The invariant and anti-invariant completed line-pair responses satisfy an exact Pythagorean law.
Thus radial source work is centered spectral width squared times the norm square of the original
completed first-divided Xi vector.  The same quantity is centered displacement times compact-theta
Green boundary flux.

The P-G124 Ward anomaly and Euclidean Krein defect are not independent currents: each is exactly
P-G126 radial source work multiplied by an explicit strictly positive source/frame gain.  This
localizes the remaining Route P producer to an independent boundary/passivity law capable of
neutralizing radial work; Ward realification itself only amplifies it.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-! ## Completed line-pair response energy -/

/-- Critical-line conjugation preserves the norm of the completed divided vector on support
fibres, before choosing an analytic-multiplicity copy. -/
theorem norm_completedXiFirstDividedL2_lineConj_support
    (rho : XiDivisorSupport) :
    ‖completedXiFirstDividedL2 (xiZeroLineConjEquiv rho)‖ =
      ‖completedXiFirstDividedL2 rho‖ := by
  rw [completedXiFirstDividedL2_lineConj]
  simp only [MeasureTheory.Lp.norm_def]
  congr 1
  exact MeasureTheory.AEEqFun.eLpNorm_star

/-- **Line-pair Pythagorean law.**  Invariant and anti-invariant real responses split the full
completed first-divided Xi norm without loss. -/
theorem norm_sq_completedXiLinePairEven_add_odd
    (rho : XiDivisorSupport) :
    ‖completedXiLinePairEven rho‖ ^ 2 + ‖completedXiLinePairOdd rho‖ ^ 2 =
      ‖completedXiFirstDividedL2 rho‖ ^ 2 := by
  have hpara := parallelogram_law_with_norm ℂ
    (completedXiFirstDividedL2 rho)
    (completedXiFirstDividedL2 (xiZeroLineConjEquiv rho))
  have hpartner := norm_completedXiFirstDividedL2_lineConj_support rho
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    norm_num [norm_div]
  have hIhalf : ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [norm_div, norm_neg, Complex.norm_I]
    norm_num
  rw [hpartner] at hpara
  rw [completedXiLinePairEven_eq, completedXiLinePairOdd_eq,
    norm_smul, norm_smul, hhalf, hIhalf]
  nlinarith [hpara]

/-- Completed radial source work is spectral width squared times the full divided-vector energy. -/
theorem burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq
    (rho : XiDivisorSupport) :
    burnolCompletedRadialSourceWork rho =
      (xiSpectralPointSupport rho).im ^ 2 *
        ‖completedXiFirstDividedL2 rho‖ ^ 2 := by
  rw [burnolCompletedRadialSourceWork_eq,
    norm_sq_completedXiLinePairEven_add_odd]

/-- Source-explicit radial work formula through same-fibre theta root energy. -/
theorem burnolCompletedRadialSourceWork_eq_thetaRootEnergy
    (rho : XiDivisorSupport) :
    burnolCompletedRadialSourceWork rho =
      (xiSpectralPointSupport rho).im ^ 2 *
        (2 * Real.pi * thetaSource.mass ^ 2 *
          thetaRootEnergy (xiSpectralPointSupport rho)) := by
  rw [burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq,
    norm_sq_completedXiFirstDividedL2_eq_sameFiberThetaRootEnergy]

/-- **Green-current work law.**  Completed radial work is centered displacement paired with the
actual compact-theta boundary flux, including exact source normalization. -/
theorem burnolCompletedRadialSourceWork_eq_im_mul_thetaBoundaryFlux
    (q : XiZeroCopy) :
    burnolCompletedRadialSourceWork q.1 =
      (xiSpectralPoint q).im *
        (Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q) := by
  rw [burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq,
    thetaXiRankTwoBoundaryFlux_completedXi_sameFiber]
  simp only [xiSpectralPoint_eq_support]
  ring

/-- Dissipative radial work is reflection-even although both its spectral force and signed Green
current reverse under critical-line conjugation. -/
theorem burnolCompletedRadialSourceWork_lineConj
    (rho : XiDivisorSupport) :
    burnolCompletedRadialSourceWork (xiZeroLineConjEquiv rho) =
      burnolCompletedRadialSourceWork rho := by
  rw [burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq,
    burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq,
    xiSpectralPointSupport_lineConj,
    norm_completedXiFirstDividedL2_lineConj_support]
  simp only [Complex.conj_im]
  ring

/-- Pairing critical-line conjugates doubles radial source work; it cannot cancel it as a signed
Green current does. -/
theorem burnolCompletedRadialSourceWork_add_lineConj
    (rho : XiDivisorSupport) :
    burnolCompletedRadialSourceWork rho +
        burnolCompletedRadialSourceWork (xiZeroLineConjEquiv rho) =
      2 * burnolCompletedRadialSourceWork rho := by
  rw [burnolCompletedRadialSourceWork_lineConj]
  ring

/-! ## Ward/Krein positive-gain bridge -/

/-- Strictly positive observer gain converting radial source work into Ward anomaly energy. -/
def thetaXiWardRadialGain (q : XiZeroCopy) : ℝ :=
  burnolTwoPrimeFrameEnergy (xiSpectralPoint q) ^ 2 *
    ‖completedXiFirstDividedL2 q.1‖ ^ 2

theorem thetaXiWardRadialGain_pos (q : XiZeroCopy) :
    0 < thetaXiWardRadialGain q := by
  rw [thetaXiWardRadialGain]
  exact mul_pos
    (sq_pos_of_pos (burnolTwoPrimeFrameEnergy_pos (xiSpectralPoint q)))
    (sq_pos_of_pos (norm_pos_iff.mpr (completedXiFirstDividedL2_ne_zero q.1)))

/-- The positive gain is itself a source-explicit frame/root-energy product. -/
theorem thetaXiWardRadialGain_eq_thetaRootEnergy (q : XiZeroCopy) :
    thetaXiWardRadialGain q =
      burnolTwoPrimeFrameEnergy (xiSpectralPoint q) ^ 2 *
        (2 * Real.pi * thetaSource.mass ^ 2 *
          thetaRootEnergy (xiSpectralPointSupport q.1)) := by
  rw [thetaXiWardRadialGain,
    norm_sq_completedXiFirstDividedL2_eq_sameFiberThetaRootEnergy]

/-- **Ward/source-work bridge.**  Ward anomaly energy is exactly positive gain times radial work. -/
theorem thetaXiWard_anomaly_normSq_eq_gain_mul_radialSourceWork
    (q : XiZeroCopy) :
    Complex.normSq (thetaXiWardRealificationAnomaly q) =
      thetaXiWardRadialGain q * burnolCompletedRadialSourceWork q.1 := by
  rw [thetaXiWard_anomaly_normSq_eq_thetaChannel_sq,
    thetaXiWardThetaChannel_eq, thetaXiWardRealificationMass,
    thetaXiWardRadialGain,
    burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq,
    xiSpectralPoint_eq_support]
  ring

/-- Euclidean energy hidden by Krein-null Ward cancellation is twice the same amplified radial
source work. -/
theorem thetaXiWardEuclideanEnergy_eq_two_mul_gain_mul_radialSourceWork
    (q : XiZeroCopy) :
    thetaXiWardEuclideanEnergy q =
      2 * thetaXiWardRadialGain q * burnolCompletedRadialSourceWork q.1 := by
  rw [thetaXiWardEuclideanEnergy_eq_two_mul_anomaly_normSq,
    thetaXiWard_anomaly_normSq_eq_gain_mul_radialSourceWork]
  ring

/-- Ward Euclidean flatness and radial-work neutrality are pointwise identical conditions because
the conversion gain is strictly positive. -/
theorem thetaXiWardEuclideanEnergy_eq_zero_iff_radialSourceWork_eq_zero
    (q : XiZeroCopy) :
    thetaXiWardEuclideanEnergy q = 0 ↔
      burnolCompletedRadialSourceWork q.1 = 0 := by
  rw [thetaXiWardEuclideanEnergy_eq_two_mul_gain_mul_radialSourceWork]
  have hgain : 2 * thetaXiWardRadialGain q ≠ 0 :=
    ne_of_gt (mul_pos two_pos (thetaXiWardRadialGain_pos q))
  constructor
  · intro hzero
    exact (mul_eq_zero.mp hzero).resolve_left hgain
  · intro hzero
    rw [hzero, mul_zero]

end RHTower
