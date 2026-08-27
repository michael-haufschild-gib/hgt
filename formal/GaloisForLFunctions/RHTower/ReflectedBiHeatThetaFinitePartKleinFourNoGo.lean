import GaloisForLFunctions.RHTower.ReflectedBiHeatThetaFinitePartWallSchwarz
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# Klein-four zero-cross no-go for reflected bi-heat finite part

Canonical finite-part imaginary channel is wall-odd, but it is not a universal
wall detector: conjugation forces it to vanish on every real-order datum as well
as on critical wall.  This file proves closed counterexample and extracts exact
positive survivor.  Mixed grade--phase coordinate `(Re z - 1/2) Im z` has same
Klein-four character, vanishes exactly on forced cross, and recovers exact wall
detection on actual Xi divisor support because those divisors have nonzero
height.
-/

open Complex Filter Set Topology

noncomputable section

namespace RHTower

/-- Fixed locus of datum conjugation is exactly real-order locus. -/
theorem ReflectedBiHeatDatum.conjugate_eq_iff_im_eq_zero
    (P : ReflectedBiHeatDatum) :
    P.conjugate = P ↔ P.z.im = 0 := by
  constructor
  · intro h
    have him := congrArg (fun Q : ReflectedBiHeatDatum => Q.z.im) h
    simp at him
    linarith
  · intro him
    cases P with
    | mk z x hz0 hz1 hx =>
        have hz : (starRingEnd ℂ) z = z := by
          apply Complex.ext
          · simp
          · simp
            linarith
        simp [ReflectedBiHeatDatum.conjugate, hz]

/-- Every real-order datum has real canonical theta finite part. -/
theorem reflectedBiHeatFinitePart_im_eq_zero_of_z_im_eq_zero
    (P : ReflectedBiHeatDatum) (him : P.z.im = 0) :
    (reflectedBiHeatFinitePart P).im = 0 := by
  have hc : P.conjugate = P :=
    (P.conjugate_eq_iff_im_eq_zero).2 him
  have hcov := reflectedBiHeatFinitePart_conjugate P
  rw [hc] at hcov
  have h := congrArg Complex.im hcov
  simp at h
  linarith

/-- Minimal mixed grade--phase coordinate with same Klein-four character as finite-part imaginary
channel. -/
def reflectedBiHeatMixedOrientationCoordinate (z : ℂ) : ℝ :=
  (z.re - 1 / 2) * z.im

theorem reflectedBiHeatMixedOrientationCoordinate_one_sub
    (z : ℂ) :
    reflectedBiHeatMixedOrientationCoordinate (1 - z) =
      reflectedBiHeatMixedOrientationCoordinate z := by
  simp [reflectedBiHeatMixedOrientationCoordinate]
  ring

theorem reflectedBiHeatMixedOrientationCoordinate_conj
    (z : ℂ) :
    reflectedBiHeatMixedOrientationCoordinate ((starRingEnd ℂ) z) =
      -reflectedBiHeatMixedOrientationCoordinate z := by
  simp [reflectedBiHeatMixedOrientationCoordinate]

theorem reflectedBiHeatMixedOrientationCoordinate_wallReflect
    (z : ℂ) :
    reflectedBiHeatMixedOrientationCoordinate (1 - (starRingEnd ℂ) z) =
      -reflectedBiHeatMixedOrientationCoordinate z := by
  simp [reflectedBiHeatMixedOrientationCoordinate]
  ring

/-- Exact zero cross of minimal mixed orientation coordinate. -/
theorem reflectedBiHeatMixedOrientationCoordinate_eq_zero_iff
    (z : ℂ) :
    reflectedBiHeatMixedOrientationCoordinate z = 0 ↔
      z.re = 1 / 2 ∨ z.im = 0 := by
  rw [reflectedBiHeatMixedOrientationCoordinate, mul_eq_zero, sub_eq_zero]

/-- Entire symmetry-forced cross lies in zero set of canonical odd finite-part channel. -/
theorem reflectedBiHeatFinitePart_im_eq_zero_of_mixedOrientationCoordinate_eq_zero
    (P : ReflectedBiHeatDatum)
    (hzero : reflectedBiHeatMixedOrientationCoordinate P.z = 0) :
    (reflectedBiHeatFinitePart P).im = 0 := by
  rcases (reflectedBiHeatMixedOrientationCoordinate_eq_zero_iff P.z).mp hzero with
    hwall | hreal
  · exact reflectedBiHeatFinitePart_im_eq_zero_of_re_eq_half P hwall
  · exact reflectedBiHeatFinitePart_im_eq_zero_of_z_im_eq_zero P hreal

/-- Explicit real off-wall datum witnessing failure of universal wall selectivity. -/
def reflectedBiHeatOffWallRealWitness : ReflectedBiHeatDatum where
  z := 1 / 4
  x := 1
  z_re_pos := by norm_num
  z_re_lt_one := by norm_num
  x_pos := by norm_num

theorem reflectedBiHeatOffWallRealWitness_re_ne_half :
    reflectedBiHeatOffWallRealWitness.z.re ≠ 1 / 2 := by
  norm_num [reflectedBiHeatOffWallRealWitness]

theorem reflectedBiHeatOffWallRealWitness_finitePart_im_eq_zero :
    (reflectedBiHeatFinitePart reflectedBiHeatOffWallRealWitness).im = 0 := by
  apply reflectedBiHeatFinitePart_im_eq_zero_of_z_im_eq_zero
  norm_num [reflectedBiHeatOffWallRealWitness]

/-- Canonical imaginary finite part is not a universal exact critical-wall detector. -/
theorem not_forall_reflectedBiHeatFinitePart_im_eq_zero_iff_re_eq_half :
    ¬ ∀ P : ReflectedBiHeatDatum,
      (reflectedBiHeatFinitePart P).im = 0 ↔ P.z.re = 1 / 2 := by
  intro h
  exact reflectedBiHeatOffWallRealWitness_re_ne_half
    ((h reflectedBiHeatOffWallRealWitness).mp
      reflectedBiHeatOffWallRealWitness_finitePart_im_eq_zero)

/-- On actual Xi support, nonzero height removes real-axis branch of mixed coordinate. -/
theorem reflectedBiHeatMixedOrientationCoordinate_xiSupport_eq_zero_iff
    (rho : XiDivisorSupport) :
    reflectedBiHeatMixedOrientationCoordinate (rho : ℂ) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatMixedOrientationCoordinate_eq_zero_iff]
  simp [xi_divisor_support_im_ne_zero rho]

end RHTower
