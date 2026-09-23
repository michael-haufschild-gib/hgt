import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTotalCokernelClockDefectTransduction

/-!
# Exact intensity readout of the source-FE physical-clock defect

Compare the actual source-packet operations `J U_t` and `U_t J`. Their cross
amplitude is positive real on every Xi copy, whereas their intensities differ
by the exponential of the horizontal tilt. Thus phase-only interference drops
the defect that the fixed Hawking clock must extinguish. The surviving intensity
ratio identifies the complete reduced cokernel as negative logarithmic-gain
energy, at the already source-predeclared unit clock step.

This is a source-level readout identity, motivated by arXiv:2608.27650. It does
not construct a photonic realization, identify the full original physical action,
or prove extinction. No field, boundary term, or clock frequency is modified.
-/

open Complex
namespace RHTower.D4BMSourceClockFringe
noncomputable section

def leftArm (n : ℕ) (t : ℝ) (q : XiZeroCopy) : ℂ :=
  hbXiPeierlsUnitSourceFEPacketTransport
    (hbXiPeierlsCenteredQNMPhysicalClockStep n t (Finsupp.single q 1))
      (xiZeroCopyReflectEquiv q)

def rightArm (n : ℕ) (t : ℝ) (q : XiZeroCopy) : ℂ :=
  hbXiPeierlsCenteredQNMPhysicalClockStep n t
    (hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q 1))
      (xiZeroCopyReflectEquiv q)

theorem leftArm_eq (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    leftArm n t q = hbXiPeierlsUnitSourceFECocycle q *
      Complex.exp (Complex.I * (t : ℂ) *
        (starRingEnd ℂ) (hbXiPeierlsCenteredQNMFrequency n q)) := by
  rw [leftArm, hbXiPeierlsUnitSourceFEPhysicalClockStep_left_single]
  exact Finsupp.single_eq_same

theorem rightArm_eq (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    rightArm n t q = hbXiPeierlsUnitSourceFECocycle q *
      Complex.exp (Complex.I * (t : ℂ) * hbXiPeierlsCenteredQNMFrequency n q) := by
  rw [rightArm, hbXiPeierlsUnitSourceFEPhysicalClockStep_right_single]
  exact Finsupp.single_eq_same

/-- Cross-arm phase is identically zero: the cross amplitude is positive real. -/
theorem crossAmplitude_eq (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    leftArm n t q * (starRingEnd ℂ) (rightArm n t q) =
      (Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) : ℂ) := by
  rw [leftArm_eq, rightArm_eq, map_mul, ← Complex.exp_conj]
  have hc : (starRingEnd ℂ)
      (Complex.I * (t : ℂ) * hbXiPeierlsCenteredQNMFrequency n q) =
      -(Complex.I * (t : ℂ) *
        (starRingEnd ℂ) (hbXiPeierlsCenteredQNMFrequency n q)) := by simp
  rw [hc]
  calc
    _ = (hbXiPeierlsUnitSourceFECocycle q *
        (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q)) *
        (Complex.exp (Complex.I * (t : ℂ) *
          (starRingEnd ℂ) (hbXiPeierlsCenteredQNMFrequency n q)) *
         Complex.exp (-(Complex.I * (t : ℂ) *
          (starRingEnd ℂ) (hbXiPeierlsCenteredQNMFrequency n q)))) := by ring
    _ = _ := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one,
        Complex.normSq_eq_conj_mul_self]
      ring

theorem leftIntensity_eq (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    Complex.normSq (leftArm n t q) =
      Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) *
        Real.exp (-t * ((q.1 : ℂ).re - 1 / 2)) := by
  rw [leftArm_eq, Complex.normSq_mul]
  congr 1
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, pow_two, ← Real.exp_add]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  rw [hbXiPeierlsCenteredQNMFrequency_im_eq]
  ring

theorem rightIntensity_eq (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    Complex.normSq (rightArm n t q) =
      Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) *
        Real.exp (t * ((q.1 : ℂ).re - 1 / 2)) := by
  rw [rightArm_eq, Complex.normSq_mul]
  congr 1
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, pow_two, ← Real.exp_add]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  rw [hbXiPeierlsCenteredQNMFrequency_im_eq]
  ring

/-- The fixed-clock mismatch survives as intensity, despite zero differential phase. -/
theorem darkIntensity_eq (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    Complex.normSq (leftArm n t q - rightArm n t q) =
      2 * Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) *
        (Real.cosh (t * ((q.1 : ℂ).re - 1 / 2)) - 1) := by
  rw [Complex.normSq_sub, leftIntensity_eq, rightIntensity_eq,
    crossAmplitude_eq, Complex.ofReal_re, Real.cosh_eq]
  rw [neg_mul]
  ring

/-- Relative intensities give an exact finite-time logarithmic gain. -/
theorem logIntensityRatio_eq (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    Real.log (Complex.normSq (leftArm n t q) /
      Complex.normSq (rightArm n t q)) =
      -2 * t * ((q.1 : ℂ).re - 1 / 2) := by
  rw [leftIntensity_eq, rightIntensity_eq, mul_div_mul_left _ _
    (Complex.normSq_pos.mpr (hbXiPeierlsUnitSourceFECocycle_ne_zero q)).ne']
  rw [← Real.exp_sub, Real.log_exp]
  ring

/-- The complete reduced cokernel is the negative energy of the unit-clock gain readout. -/
theorem fullCokernel_eq_logIntensityEnergy (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q =
      -((hbXiPeierlsClockDefectToFullCokernelSusceptibility n q *
        Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) *
        (Real.log (Complex.normSq (leftArm 0 1 q) /
          Complex.normSq (rightArm 0 1 q)) / 2) ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_clockDefectEnergy,
    normSq_hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq,
    logIntensityRatio_eq]
  congr 2
  ring

end
end RHTower.D4BMSourceClockFringe
