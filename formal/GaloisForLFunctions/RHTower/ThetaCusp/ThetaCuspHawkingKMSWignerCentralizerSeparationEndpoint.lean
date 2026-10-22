import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTiltedBackreactionGaugeEndpoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingWignerSmithWindingEndpoint
import GaloisForLFunctions.HTGeometry.FiniteKMSFluctuationDissipation

/-!
# KMS-zero/Wigner-positive separation at tilted theta-Hawking centralizers

A tilted theta-Hawking dark mode is a literal two-ended resonance whose energy relative to the
reflected horizon generator vanishes.  Finite KMS fluctuation--dissipation therefore assigns zero
commutator and zero energy-weighted dissipative intensity to that transition, independently of
inverse temperature and microscopic transition amplitude.  This is the exact zero-gap limit of
the standard KMS factor `2 sinh (beta * gap / 2)`.

The same mode is not dynamically empty.  For positive tilt its causal all-pass factor has strictly
positive zero-frequency Wigner--Smith delay, and its laboratory backreaction port work is strictly
positive.  More sharply, every upper theta-Hawking resonance obeys the exact source-normalized law

`port work = source mass * normSq(resonance) * physical energy * central Wigner clock`.

This welds three previously separate objects: Hawking anomaly backreaction, KMS response, and
phase-sensitive scattering delay.  It also closes a proposed KMS/Krein route negatively.  Generic
KMS passivity or fluctuation--dissipation cannot remove the tilted centralizer: co-moving
dissipation is zero while a positive phase/work defect survives in the laboratory frame.

The conclusion is consistent with moving-mirror fluctuation--dissipation calculations of Stargen,
Kothawala, and Sriramkumar (`arXiv:1602.02526`) and the microscopic coloured-noise/nonlocal-
dissipation kernels of Butera (`arXiv:2306.03813`).  Those relations connect fluctuation and
dissipation spectra; they do not determine intensity-invisible all-pass phase.

**[LOCAL-RESEARCH] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]** All identities and strict
separations below are unconditional.

**[FALSIFIED]** A generic KMS fluctuation--dissipation or Krein-signature theorem forces
resonance-centralizer rigidity.  Zero relative gap kills its dissipative reporter for every
amplitude.

**[OPEN CORE]** Remaining RH-bearing producer must be source-specific and phase-sensitive: derive
from microscopic theta-mirror dynamics a laboratory-frame Ward/Krein crossing law that controls
the positive Wigner defect, rather than only the co-moving KMS dissipative spectrum.  Identifying
the raw full mirror with the canonical Cayley block is unavailable: the established nonzero even
full-mirror coupling jet already rules out that identification.
-/

open Complex Real

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open HTGeometry
open HedenmalmThetaSource

/-- Two-level energy measured by the reflected tilted horizon generator. -/
def thetaCuspHawkingRelativeCentralizerEnergy
    (a : ℝ) (r : ThetaCuspHawkingBackreactionResonantMode) (b : Bool) : ℝ :=
  if b then thetaCuspHawkingTiltedRelativeHorizonCharge a r else 0

@[simp] theorem thetaCuspHawkingRelativeCentralizerEnergy_true_sub_false
    (a : ℝ) (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingRelativeCentralizerEnergy a r true -
        thetaCuspHawkingRelativeCentralizerEnergy a r false =
      thetaCuspHawkingTiltedRelativeHorizonCharge a r := by
  simp [thetaCuspHawkingRelativeCentralizerEnergy]

/-- A tilted dark mode has zero finite-KMS commutator intensity for every Hermitian transition
amplitude: its reflected-horizon energy gap is exactly zero. -/
theorem thetaCuspHawkingTiltedDarkMode_KMSCommutatorIntensity_eq_zero
    {a w : ℝ}
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0)
    (beta : ℝ) (amplitude : Bool → Bool → ℂ)
    (hHermitian : ∀ p q, amplitude q p = star (amplitude p q)) :
    finiteKMSCommutatorTransitionIntensity beta
        (thetaCuspHawkingRelativeCentralizerEnergy a
          (thetaCuspHawkingTiltedDarkBackreactionMode hzero))
        amplitude true false = 0 := by
  rw [finiteKMSCommutatorTransitionIntensity_eq_sinh beta _ amplitude hHermitian]
  rw [thetaCuspHawkingRelativeCentralizerEnergy_true_sub_false,
    thetaCuspHawkingTiltedDarkBackreactionMode_relativeHorizonCharge_eq_zero hzero]
  simp

/-- Energy-weighted finite-KMS dissipation also vanishes at every tilted dark mode, independently
of transition amplitude or inverse temperature. -/
theorem thetaCuspHawkingTiltedDarkMode_KMSDissipativeIntensity_eq_zero
    {a w : ℝ}
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0)
    (beta : ℝ) (amplitude : Bool → Bool → ℂ) :
    finiteKMSDissipativeTransitionIntensity beta
        (thetaCuspHawkingRelativeCentralizerEnergy a
          (thetaCuspHawkingTiltedDarkBackreactionMode hzero))
        amplitude true false = 0 := by
  rw [finiteKMSDissipativeTransitionIntensity]
  rw [thetaCuspHawkingRelativeCentralizerEnergy_true_sub_false,
    thetaCuspHawkingTiltedDarkBackreactionMode_relativeHorizonCharge_eq_zero hzero]
  simp

/-- Hawking anomaly port work is exactly the zero-frequency Wigner--Smith clock multiplied by
source mass, resonance norm, and physical response energy. -/
theorem thetaCuspHawkingBackreactionPortDissipation_eq_wignerSmithClockZero
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    thetaCuspHawkingBackreactionPortDissipation r =
      thetaSource.mass * Complex.normSq r.1 *
        thetaCuspHawkingBackreactionPhysicalEnergy r *
          thetaCuspHawkingAllPassDressedBornClockZero r := by
  rw [thetaCuspHawkingBackreactionPortDissipation_eq,
    thetaCuspHawkingAllPassDressedBornClockZero_eq r hr]
  field_simp [(Complex.normSq_pos.mpr
    (thetaCuspHawkingBackreactionResonantMode_ne_zero r)).ne']

/-- At positive tilt a dark centralizer mode is invisible to KMS dissipation but retains strictly
positive Wigner delay and laboratory port work. -/
theorem thetaCuspHawkingTiltedDarkMode_KMSZero_wignerSmith_portWork_pos
    {a w : ℝ} (ha : 0 < a)
    (hzero : thetaCuspHawkingTiltedDeembeddedPairCarrier a w = 0)
    (beta : ℝ) (amplitude : Bool → Bool → ℂ) :
    finiteKMSDissipativeTransitionIntensity beta
        (thetaCuspHawkingRelativeCentralizerEnergy a
          (thetaCuspHawkingTiltedDarkBackreactionMode hzero))
        amplitude true false = 0 ∧
      0 < thetaCuspHawkingAllPassDressedBornClockZero
        (thetaCuspHawkingTiltedDarkBackreactionMode hzero) ∧
      0 < thetaCuspHawkingBackreactionPortDissipation
        (thetaCuspHawkingTiltedDarkBackreactionMode hzero) := by
  let r := thetaCuspHawkingTiltedDarkBackreactionMode hzero
  have hr : 0 < r.1.im := by
    simp [r, ha]
  refine ⟨thetaCuspHawkingTiltedDarkMode_KMSDissipativeIntensity_eq_zero
      hzero beta amplitude,
    thetaCuspHawkingAllPassDressedBornClockZero_pos r hr, ?_⟩
  rw [thetaCuspHawkingTiltedDarkBackreactionMode_portDissipation_eq_modularWork hzero]
  exact mul_pos (mul_pos (mul_pos (by norm_num) thetaSource.mass_pos) ha)
    (thetaCuspHawkingBackreactionPhysicalEnergy_pos r)

end RHTower
