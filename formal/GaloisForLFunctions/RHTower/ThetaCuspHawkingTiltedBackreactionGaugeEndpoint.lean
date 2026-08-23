import GaloisForLFunctions.RHTower.ThetaCuspHawkingTiltedMirrorOpticalTheoremEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingModularSuperselectionEndpoint

/-!
# Tilted Hawking backreaction gauge and modular-centralizer endpoint

The tilted moving mirror with source `k_a(x) = exp(a*x) k(x)` reads
`XiC(w + a*i)` at ordinary real pair frequency `w`.  The same divisor has a second, dynamical
realization: it is the two-ended backreaction mode of the reflected source `k_{-a}` at real
frequency `w`.

The reason is an exact Hawking-horizon gauge covariance.  Multiplication of the density-dressed
mode by `exp(-a*x)` conjugates the laboratory pencil `D + (w + a*i)` to the reflected tilted
pencil `D + w`.  Equivalently, the reflected tilt subtracts `a` from the logarithmic source
connection while leaving the rapidity response unchanged.

This has a sharp consequence for the passivity route.  A tilted dark mode has zero
horizon-relative charge, while its laboratory port imbalance is exactly the modular work term

`2 * thetaSource.mass * a * physicalEnergy`.

Thus ordinary co-moving passivity is automatically saturated by every hypothetical off-line
zero; it cannot prove RH.  The new Hawking-specific endpoint is instead **resonance-centralizer
rigidity**: the reflected theta horizon has no nonzero-tilt, source-coupled, two-ended zero mode.
This is a one-particle scattering sector, not a claim that a full KMS algebra has trivial
centralizer.  Its intended producer is strict mixing of the coefficient-faithful theta response,
not a generic positivity slogan.

**[LOCAL-RESEARCH] [PAPER-PROVED] [LEAN-PROVED]** The gauge, anomaly-pencil, charge, work, and
RH-equivalence statements below are unconditional.

**[OPEN CORE]** Derive resonance-centralizer rigidity from a coefficient-faithful Hawking KMS
dilation.  KMS passivity alone is insufficient because zero modular frequency is passive, and a
generic KMS centralizer need not be trivial.
-/

open Complex Function

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmThetaSource

/-! ## Reflected-tilt gauge covariance -/

/-- Laboratory spectral point read by real frequency `w` on the mirror of tilt `a`. -/
def thetaCuspHawkingTiltedSpectralPoint (a w : ℝ) : ℂ :=
  (w : ℂ) + (a : ℂ) * Complex.I

@[simp] theorem thetaCuspHawkingTiltedSpectralPoint_re (a w : ℝ) :
    (thetaCuspHawkingTiltedSpectralPoint a w).re = w := by
  simp [thetaCuspHawkingTiltedSpectralPoint, Complex.mul_re]

@[simp] theorem thetaCuspHawkingTiltedSpectralPoint_im (a w : ℝ) :
    (thetaCuspHawkingTiltedSpectralPoint a w).im = a := by
  simp [thetaCuspHawkingTiltedSpectralPoint, Complex.mul_im]

/-- Density-dressed response after reflection of the physical mirror tilt. -/
def thetaCuspHawkingReflectedTiltDressedMode (a w x : ℝ) : ℂ :=
  (Real.exp (-(a * x)) : ℂ) *
    thetaTwoEndedSourceSolution (thetaCuspHawkingTiltedSpectralPoint a w) x

/-- Undressing by the reflected tilted source. -/
def thetaCuspHawkingReflectedTiltRapidityMode (a w x : ℝ) : ℂ :=
  thetaCuspHawkingReflectedTiltDressedMode a w x /
    (thetaCuspTiltedSource (-a) x : ℂ)

/-- **Gauge-invariant rapidity.** Reflection of the density tilt cancels exactly on undressing;
the rapidity is the original theta backreaction response at `w + a*i`. -/
theorem thetaCuspHawkingReflectedTiltRapidityMode_eq
    (a w x : ℝ) :
    thetaCuspHawkingReflectedTiltRapidityMode a w x =
      thetaCuspHawkingBackreactionRapidityMode
        (thetaCuspHawkingTiltedSpectralPoint a w) x := by
  unfold thetaCuspHawkingReflectedTiltRapidityMode
    thetaCuspHawkingReflectedTiltDressedMode
    thetaCuspHawkingBackreactionRapidityMode thetaCuspTiltedSource
  have hexp : (Real.exp (-(a * x)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos (-(a * x))).ne'
  have hk : (thetaCuspFullSource x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaCuspFullSource_pos_all x).ne'
  rw [show -a * x = -(a * x) by ring]
  field_simp [hexp, hk]
  push_cast
  ring

/-- Reflected tilted logarithmic connection and real-frequency anomaly pencil. -/
def thetaCuspHawkingReflectedTiltBackreactionPencil
    (q a w : ℝ) (eta eta' : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(q : ℂ) *
      (eta' x + (((sourceLogDeriv x - a : ℝ) : ℝ) : ℂ) * eta x) -
    Complex.I * (q : ℂ) * (w : ℂ) * eta x

/-- **Exact reflected-tilt anomaly covariance.** The real-frequency reflected-source pencil is
the laboratory theta pencil at the complex frequency `w + a*i`. -/
theorem thetaCuspHawkingReflectedTiltBackreactionPencil_eq
    (q a w : ℝ) (eta eta' : ℝ → ℂ) (x : ℝ) :
    thetaCuspHawkingReflectedTiltBackreactionPencil q a w eta eta' x =
      thetaCuspHawkingBackreactionPencil q
        (thetaCuspHawkingTiltedSpectralPoint a w) eta eta' x := by
  rw [thetaCuspHawkingBackreactionPencil,
    thetaCuspHawkingAnomalyLinearization_eq]
  unfold thetaCuspHawkingReflectedTiltBackreactionPencil
    thetaCuspHawkingTiltedSpectralPoint
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The gauge-invariant rapidity solves the reflected tilted anomaly equation at real frequency
for every tilt.  Xi enters only through the future endpoint. -/
theorem thetaCuspHawkingReflectedTiltRapidityMode_equation
    (q a w x : ℝ) :
    thetaCuspHawkingReflectedTiltBackreactionPencil q a w
        (thetaCuspHawkingReflectedTiltRapidityMode a w)
        (deriv (thetaCuspHawkingReflectedTiltRapidityMode a w)) x =
      -(q : ℂ) := by
  rw [thetaCuspHawkingReflectedTiltBackreactionPencil_eq]
  have hfun :
      thetaCuspHawkingReflectedTiltRapidityMode a w =
        thetaCuspHawkingBackreactionRapidityMode
          (thetaCuspHawkingTiltedSpectralPoint a w) := by
    funext y
    exact thetaCuspHawkingReflectedTiltRapidityMode_eq a w y
  rw [hfun]
  exact thetaCuspHawkingBackreactionRapidityMode_equation q
    (thetaCuspHawkingTiltedSpectralPoint a w) x

/-! ## Dark modes, horizon-relative charge, and modular work -/

/-- **Optical/backreaction weld.** A real dark frequency of the tilt-`a` moving mirror is
exactly a two-ended backreaction resonance of the reflected tilted anomaly pencil. -/
theorem thetaCuspHawkingTiltedPairCarrier_eq_zero_iff_backreactionResonance
    (a w : ℝ) :
    thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0 ↔
      ThetaCuspHawkingBackreactionResonance
        (thetaCuspHawkingTiltedSpectralPoint a w) := by
  simpa [thetaCuspHawkingTiltedDeembeddedPairCarrier,
    thetaCuspHawkingTiltedSpectralPoint] using
    (xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance
      (thetaCuspHawkingTiltedSpectralPoint a w))

/-- A real-frequency tilted dark mode, reinterpreted as a literal two-ended theta
backreaction resonance in the laboratory spectral coordinate. -/
def thetaCuspHawkingTiltedDarkBackreactionMode
    {a w : ℝ}
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0) :
    ThetaCuspHawkingBackreactionResonantMode :=
  ⟨thetaCuspHawkingTiltedSpectralPoint a w,
    (thetaCuspHawkingTiltedPairCarrier_eq_zero_iff_backreactionResonance a w).mp hzero⟩

@[simp] theorem thetaCuspHawkingTiltedDarkBackreactionMode_coe
    {a w : ℝ}
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0) :
    (thetaCuspHawkingTiltedDarkBackreactionMode hzero).1 =
      thetaCuspHawkingTiltedSpectralPoint a w := rfl

/-- Horizon charge relative to the reflected tilted generator.  This is the exact analog of
subtracting a horizon chemical-potential term from the laboratory generator. -/
def thetaCuspHawkingTiltedRelativeHorizonCharge
    (a : ℝ) (r : ThetaCuspHawkingBackreactionResonantMode) : ℝ :=
  thetaCuspHawkingBackreactionHorizonCharge r - a

theorem thetaCuspHawkingTiltedRelativeHorizonCharge_eq
    (a : ℝ) (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingTiltedRelativeHorizonCharge a r = r.1.im - a := by
  rw [thetaCuspHawkingTiltedRelativeHorizonCharge,
    thetaCuspHawkingBackreactionHorizonCharge_eq_im]

/-- **Grand-canonical port split.** Laboratory boundary power is relative horizon dissipation
plus the exact modular-work contribution of the tilt. -/
theorem thetaCuspHawkingBackreactionPortDissipation_eq_relative_add_modularWork
    (a : ℝ) (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingBackreactionPortDissipation r =
      2 * thetaSource.mass *
        thetaCuspHawkingTiltedRelativeHorizonCharge a r *
          thetaCuspHawkingBackreactionPhysicalEnergy r +
      2 * thetaSource.mass * a *
          thetaCuspHawkingBackreactionPhysicalEnergy r := by
  rw [thetaCuspHawkingBackreactionPortDissipation_eq,
    thetaCuspHawkingTiltedRelativeHorizonCharge_eq]
  ring

/-- **Co-moving neutrality of every tilted dark mode.** A hypothetical off-line Xi zero is a
zero-frequency mode of the reflected horizon generator. -/
theorem thetaCuspHawkingTiltedDarkBackreactionMode_relativeHorizonCharge_eq_zero
    {a w : ℝ}
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0) :
    thetaCuspHawkingTiltedRelativeHorizonCharge a
      (thetaCuspHawkingTiltedDarkBackreactionMode hzero) = 0 := by
  rw [thetaCuspHawkingTiltedRelativeHorizonCharge_eq]
  rw [thetaCuspHawkingTiltedDarkBackreactionMode_coe,
    thetaCuspHawkingTiltedSpectralPoint_im, sub_self]

/-- **Laboratory work saturation.** At a tilted dark mode the entire laboratory port imbalance
is modular work; no residual dissipative term survives in the reflected horizon frame. -/
theorem thetaCuspHawkingTiltedDarkBackreactionMode_portDissipation_eq_modularWork
    {a w : ℝ}
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0) :
    thetaCuspHawkingBackreactionPortDissipation
        (thetaCuspHawkingTiltedDarkBackreactionMode hzero) =
      2 * thetaSource.mass * a *
        thetaCuspHawkingBackreactionPhysicalEnergy
          (thetaCuspHawkingTiltedDarkBackreactionMode hzero) := by
  rw [thetaCuspHawkingBackreactionPortDissipation_eq_relative_add_modularWork a,
    thetaCuspHawkingTiltedDarkBackreactionMode_relativeHorizonCharge_eq_zero]
  ring

/-- Natural horizon-relative passivity is saturated, not violated, by every tilted dark mode. -/
theorem thetaCuspHawkingTiltedDarkBackreactionMode_relativePassive
    {a w : ℝ}
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0) :
    0 ≤ thetaCuspHawkingTiltedRelativeHorizonCharge a
      (thetaCuspHawkingTiltedDarkBackreactionMode hzero) := by
  rw [thetaCuspHawkingTiltedDarkBackreactionMode_relativeHorizonCharge_eq_zero]

/-! ## New RH endpoint: source-coupled resonance-centralizer rigidity -/

/-- No nonzero modular tilt supports a real-frequency, two-ended reflected-horizon zero mode. -/
def ThetaCuspHawkingTiltedResonanceCentralizerRigid : Prop :=
  ∀ (a w : ℝ), |a| < 1 →
    ThetaCuspHawkingBackreactionResonance
      (thetaCuspHawkingTiltedSpectralPoint a w) →
    a = 0

/-- **Hawking modular-centralizer RH endpoint.** RH is exactly triviality of the nonzero-tilt
two-ended centralizer sector.  Unlike passivity, this targets zero modular-frequency modes. -/
theorem riemannHypothesis_iff_thetaCuspHawkingTiltedResonanceCentralizerRigid :
    RiemannHypothesis ↔ ThetaCuspHawkingTiltedResonanceCentralizerRigid := by
  rw [riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real]
  constructor
  · intro hreal a w _ha hres
    have him := hreal (thetaCuspHawkingTiltedSpectralPoint a w) hres
    simpa using him
  · intro hrigid alpha hres
    have hzero : XiC alpha = 0 :=
      (xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance alpha).mpr hres
    have ha : |alpha.im| < 1 := abs_im_lt_one_of_XiC_eq_zero hzero
    have hspectral :
        thetaCuspHawkingTiltedSpectralPoint alpha.im alpha.re = alpha := by
      apply Complex.ext <;> simp
    have him := hrigid alpha.im alpha.re ha (by simpa [hspectral] using hres)
    exact him

end RHTower
