import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWCompletedCTPOriginalCapLiftBridge
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWOpticalCTPParity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWWeakSourceMassPositivity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsSameRateNoGo

/-!
PW-B amplitude-uniform incidence obstruction. The actual completed CTP source
has degree four in source amplitude, while the source-faithful weak crossed
optical flux has degree eight. A fixed nonzero calibration holding at amplitudes
one and two therefore forces the critical line; the surviving producer must
use a source-derived amplitude-dependent normalization or a fixed amplitude.
-/

open Complex ComplexConjugate
open scoped InnerProductSpace
open RHTower RHTower.D4BMModularCore
open RHTower.D4BMGlobalAngularResponse
open RHTower.D4BMFullAngularSourceReflection
open RHTower.D4BMPWOpticalCTPParity

namespace RHTower.D4BMPWAmplitudeIncidence
noncomputable section
set_option autoImplicit false

def amplitudeWeakSolution (q : XiZeroCopy) (b : Bool) (a : ℂ)
    (h : energyDomain) : Prop :=
  ∀ v : energyDomain,
    inner ℂ v h - (1-parameter q b)*inner ℂ (embedding v) (embedding h) =
      -inner ℂ (embedding v) (a ^ (2 : ℕ) • forcingVector q b)

theorem amplitudeWeakResponse_spec (q : XiZeroCopy) (b : Bool) (a : ℂ) :
    amplitudeWeakSolution q b a (a ^ (2 : ℕ) • weakResponse q b) := by
  intro v
  have h := weakResponse_spec q b v
  simp only [Submodule.coe_inner,Submodule.coe_smul,
    inner_smul_right,map_smul] at h ⊢
  linear_combination (a ^ (2 : ℕ)) * h

/-- The actual quadratic source amplitude transported through the linear weak response. -/
def amplitudeMass (q : XiZeroCopy) (b : Bool) (a : ℂ) : ℝ :=
  ‖a ^ (2 : ℕ) • embedding (weakResponse q b)‖ ^ (2 : ℕ)

def amplitudeFlux (q : XiZeroCopy) (b : Bool) (a : ℂ) : ℝ :=
  (inner ℂ (a ^ (2 : ℕ) • embedding (weakResponse q b))
    (a ^ (2 : ℕ) • forcingVector q b)).im

def amplitudeCrossedFlux (q : XiZeroCopy) (a : ℂ) : ℝ :=
  amplitudeFlux q true a * amplitudeMass q false a +
    amplitudeFlux q false a * amplitudeMass q true a

theorem amplitudeMass_eq (q : XiZeroCopy) (b : Bool) (a : ℂ) :
    amplitudeMass q b a = ‖a‖ ^ (4 : ℕ) * weakSourceMass q b := by
  simp only [amplitudeMass,weakSourceMass,norm_smul,norm_pow]
  ring

theorem amplitudeFlux_eq (q : XiZeroCopy) (b : Bool) (a : ℂ) :
    amplitudeFlux q b a = ‖a‖ ^ (4 : ℕ) * weakSourceFlux q b := by
  have hcoeff : a ^ (2 : ℕ) * (starRingEnd ℂ) (a ^ (2 : ℕ)) =
      ((‖a‖ ^ (4 : ℕ) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,norm_pow]
    push_cast
    ring
  simp only [amplitudeFlux,weakSourceFlux,inner_smul_left,inner_smul_right]
  rw [← mul_assoc,hcoeff]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero]

theorem amplitudeCrossedFlux_eq (q : XiZeroCopy) (a : ℂ) :
    amplitudeCrossedFlux q a = ‖a‖ ^ (8 : ℕ) * crossedOpticalFlux q := by
  rw [amplitudeCrossedFlux,amplitudeFlux_eq,amplitudeFlux_eq,
    amplitudeMass_eq,amplitudeMass_eq]
  unfold crossedOpticalFlux
  ring

private theorem mass_one (q : XiZeroCopy) (b : Bool) :
    amplitudeMass q b 1 = weakSourceMass q b := by
  simp [amplitudeMass,weakSourceMass]

private theorem flux_one (q : XiZeroCopy) (b : Bool) :
    amplitudeFlux q b 1 = weakSourceFlux q b := by
  simp [amplitudeFlux,weakSourceFlux]

private theorem mass_two (q : XiZeroCopy) (b : Bool) :
    amplitudeMass q b 2 = 16 * weakSourceMass q b := by
  simp only [amplitudeMass,weakSourceMass]
  norm_num [norm_smul]
  ring

private theorem flux_two (q : XiZeroCopy) (b : Bool) :
    amplitudeFlux q b 2 = 16 * weakSourceFlux q b := by
  simp only [amplitudeFlux,weakSourceFlux]
  norm_num [inner_smul_left,inner_smul_right]
  ring

private theorem crossed_one (q : XiZeroCopy) :
    amplitudeCrossedFlux q 1 = crossedOpticalFlux q := by
  simp [amplitudeCrossedFlux,crossedOpticalFlux,mass_one,flux_one]

private theorem crossed_two (q : XiZeroCopy) :
    amplitudeCrossedFlux q 2 = 256 * crossedOpticalFlux q := by
  simp only [amplitudeCrossedFlux,crossedOpticalFlux,mass_two,flux_two]
  ring

theorem completedCTP_amplitude_four (q : XiZeroCopy) (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchSymmetricCausalPair q a X k =
      a ^ (4 : ℕ) * fullCircleCrossBranchSymmetricCausalPair q 1 X k := by
  unfold fullCircleCrossBranchSymmetricCausalPair
  simp only [pwb_fullCircleCrossBranch_eq_fullCausalSourcePair]
  rw [D4BMLiteralCyclicPeierlsSameRateNoGo.fullCausalSourcePair_amplitude_biquadratic
        q true true false a a,
      D4BMLiteralCyclicPeierlsSameRateNoGo.fullCausalSourcePair_amplitude_biquadratic
        q false true false a a]
  ring

def amplitudeOrientedIncidence (q : XiZeroCopy) (a : ℂ) (X k : ℝ) : Prop :=
  (q.1 : ℂ).im * (fullCircleCrossBranchSymmetricCausalPair q a X k).re =
    amplitudeCrossedFlux q a

theorem two_amplitude_incidence_forces_critical (q : XiZeroCopy) (X k : ℝ)
    (h1 : amplitudeOrientedIncidence q 1 X k)
    (h2 : amplitudeOrientedIncidence q 2 X k) :
    (q.1 : ℂ).re = 1/2 := by
  have hc2 := completedCTP_amplitude_four q 2 X k
  have hF : crossedOpticalFlux q = 0 := by
    dsimp [amplitudeOrientedIncidence] at h1 h2
    rw [crossed_one] at h1
    rw [crossed_two,hc2] at h2
    norm_num at h2
    nlinarith [h1,h2]
  have hmassT : weakSourceMass q true ≠ 0 := ne_of_gt (pwb_weakSourceMass_pos q true)
  have hmassF : weakSourceMass q false ≠ 0 := ne_of_gt (pwb_weakSourceMass_pos q false)
  have him : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hcoef : (-16 : ℝ) * (q.1 : ℂ).im *
      (weakSourceMass q true * weakSourceMass q false) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) him) (mul_ne_zero hmassT hmassF)
  have hfactor : crossedOpticalFlux q =
      ((q.1 : ℂ).re - 1/2) *
        ((-16 : ℝ) * (q.1 : ℂ).im *
          (weakSourceMass q true * weakSourceMass q false)) := by
    rw [crossedOpticalFlux_eq]
    ring
  rw [hfactor] at hF
  have hδ : (q.1 : ℂ).re - 1/2 = 0 :=
    (mul_eq_zero.mp hF).resolve_right hcoef
  linarith

theorem two_amplitude_incidence_iff_critical (q : XiZeroCopy) (X k : ℝ) :
    (amplitudeOrientedIncidence q 1 X k ∧
      amplitudeOrientedIncidence q 2 X k) ↔
    (q.1 : ℂ).re = 1/2 := by
  constructor
  · rintro ⟨h1,h2⟩
    exact two_amplitude_incidence_forces_critical q X k h1 h2
  · intro hline
    have hctp : (fullCircleCrossBranchSymmetricCausalPair q 1 X k).re = 0 := by
      exact fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_on_critical
        q (by simpa only [deningerDivisorThetaEigen] using hline) X k
    have hflux : crossedOpticalFlux q = 0 := by
      rw [crossedOpticalFlux_eq]
      simp [hline]
    constructor
    · unfold amplitudeOrientedIncidence
      rw [crossed_one,hctp,hflux]
      ring
    · unfold amplitudeOrientedIncidence
      rw [crossed_two,completedCTP_amplitude_four]
      norm_num [hctp,hflux]

/-- A fixed nonzero scalar calibration cannot repair the difference between
quartic CTP and eighth-degree crossed optical source scaling off the line. -/
theorem calibrated_two_amplitudes_forces_critical (q : XiZeroCopy)
    (X k κ : ℝ) (hκ : κ ≠ 0)
    (h1 : (q.1 : ℂ).im *
      (fullCircleCrossBranchSymmetricCausalPair q 1 X k).re =
        κ * amplitudeCrossedFlux q 1)
    (h2 : (q.1 : ℂ).im *
      (fullCircleCrossBranchSymmetricCausalPair q 2 X k).re =
        κ * amplitudeCrossedFlux q 2) :
    (q.1 : ℂ).re = 1/2 := by
  have hc2 := completedCTP_amplitude_four q 2 X k
  have hprod : κ * crossedOpticalFlux q = 0 := by
    rw [crossed_one] at h1
    rw [crossed_two,hc2] at h2
    norm_num at h2
    nlinarith [h1,h2]
  have hF : crossedOpticalFlux q = 0 := (mul_eq_zero.mp hprod).resolve_left hκ
  have hmassT : weakSourceMass q true ≠ 0 := ne_of_gt (pwb_weakSourceMass_pos q true)
  have hmassF : weakSourceMass q false ≠ 0 := ne_of_gt (pwb_weakSourceMass_pos q false)
  have him : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hcoef : (-16 : ℝ) * (q.1 : ℂ).im *
      (weakSourceMass q true * weakSourceMass q false) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) him) (mul_ne_zero hmassT hmassF)
  have hfactor : crossedOpticalFlux q =
      ((q.1 : ℂ).re - 1/2) *
        ((-16 : ℝ) * (q.1 : ℂ).im *
          (weakSourceMass q true * weakSourceMass q false)) := by
    rw [crossedOpticalFlux_eq]
    ring
  rw [hfactor] at hF
  have hδ : (q.1 : ℂ).re - 1/2 = 0 :=
    (mul_eq_zero.mp hF).resolve_right hcoef
  linarith

end
end RHTower.D4BMPWAmplitudeIncidence
