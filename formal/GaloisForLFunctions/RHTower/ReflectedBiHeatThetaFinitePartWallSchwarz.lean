import GaloisForLFunctions.RHTower.ReflectedBiHeatThetaFinitePartReflectionNoGo
import GaloisForLFunctions.RHTower.Reflection

/-!
# Critical-wall Schwarz law for the reflected bi-heat theta finite part

Complementary factor reflection `z ↦ 1-z` is blind, but critical-wall reflection
`z ↦ 1-conj z` preserves height and retains a canonical odd channel.  This file
proves exact conjugation covariance first for regulated pair sums and then for
their canonical theta-pole finite parts.  Consequently real finite-part channel
is wall-even, imaginary channel is wall-odd, and entire wall defect is exactly
twice imaginary channel.
-/

open Complex Filter Set Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Complex conjugation of datum while preserving the real heat scale. -/
def ReflectedBiHeatDatum.conjugate
    (P : ReflectedBiHeatDatum) : ReflectedBiHeatDatum where
  z := (starRingEnd ℂ) P.z
  x := P.x
  z_re_pos := by simpa using P.z_re_pos
  z_re_lt_one := by simpa using P.z_re_lt_one
  x_pos := P.x_pos

@[simp] theorem ReflectedBiHeatDatum.conjugate_z (P : ReflectedBiHeatDatum) :
    P.conjugate.z = (starRingEnd ℂ) P.z := rfl

@[simp] theorem ReflectedBiHeatDatum.conjugate_x (P : ReflectedBiHeatDatum) :
    P.conjugate.x = P.x := rfl

@[simp] theorem ReflectedBiHeatDatum.conjugate_conjugate (P : ReflectedBiHeatDatum) :
    P.conjugate.conjugate = P := by
  cases P
  simp [ReflectedBiHeatDatum.conjugate]

@[simp] theorem ReflectedBiHeatDatum.conjugate_leftOrder_real
    (P : ReflectedBiHeatDatum) (epsilon : ℝ) :
    P.conjugate.leftOrder (epsilon : ℂ) =
      (starRingEnd ℂ) (P.leftOrder (epsilon : ℂ)) := by
  simp [ReflectedBiHeatDatum.conjugate, ReflectedBiHeatDatum.leftOrder]
  rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by exact map_ofNat (starRingEnd ℂ) 2]

@[simp] theorem ReflectedBiHeatDatum.conjugate_rightOrder_real
    (P : ReflectedBiHeatDatum) (epsilon : ℝ) :
    P.conjugate.rightOrder (epsilon : ℂ) =
      (starRingEnd ℂ) (P.rightOrder (epsilon : ℂ)) := by
  simp [ReflectedBiHeatDatum.conjugate, ReflectedBiHeatDatum.rightOrder]
  rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by exact map_ofNat (starRingEnd ℂ) 2]

/-- Pair term commutes with conjugation of its two Dirichlet orders. -/
theorem asymmetricHeatPairTerm_conjugate
    (a b : ℂ) (x : ℝ) (p : ℕ × ℕ) :
    asymmetricHeatPairTerm ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) x p =
      (starRingEnd ℂ) (asymmetricHeatPairTerm a b x p) := by
  rw [asymmetricHeatPairTerm, asymmetricHeatPairTerm, map_mul, map_mul]
  rw [show ((((p.1 : ℝ) + 1 : ℝ) : ℂ)) = ((p.1 + 1 : ℕ) : ℂ) by norm_num,
    show ((((p.2 : ℝ) + 1 : ℝ) : ℂ)) = ((p.2 + 1 : ℕ) : ℂ) by norm_num]
  rw [← natCast_cpow_conj, ← natCast_cpow_conj]
  simp

/-- Real-regulator pair sum commutes with complex conjugation. -/
theorem reflectedBiHeatPairSum_conjugate_real
    (P : ReflectedBiHeatDatum) (epsilon : ℝ) :
    reflectedBiHeatPairSum P.conjugate (epsilon : ℂ) =
      (starRingEnd ℂ) (reflectedBiHeatPairSum P (epsilon : ℂ)) := by
  rw [reflectedBiHeatPairSum, reflectedBiHeatPairSum,
    Complex.conj_tsum]
  apply tsum_congr
  intro p
  rw [ReflectedBiHeatDatum.conjugate_leftOrder_real,
    ReflectedBiHeatDatum.conjugate_rightOrder_real,
    ReflectedBiHeatDatum.conjugate_x,
    asymmetricHeatPairTerm_conjugate]

/-- Canonical theta finite part is equivariant under complex conjugation. -/
theorem reflectedBiHeatFinitePart_conjugate (P : ReflectedBiHeatDatum) :
    reflectedBiHeatFinitePart P.conjugate =
      (starRingEnd ℂ) (reflectedBiHeatFinitePart P) := by
  have hP := tendsto_reflectedBiHeatPairSum_sub_thetaPole_finitePart P
  have hstar : Tendsto (fun epsilon : ℝ =>
      (starRingEnd ℂ) (reflectedBiHeatPairSum P (epsilon : ℂ) -
        ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((starRingEnd ℂ) (reflectedBiHeatFinitePart P))) :=
    Complex.continuous_conj.continuousAt.tendsto.comp hP
  have hstar' : Tendsto (fun epsilon : ℝ =>
      reflectedBiHeatPairSum P.conjugate (epsilon : ℂ) -
        ((heatCoeffSum P.conjugate.x : ℝ) : ℂ) / (epsilon : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((starRingEnd ℂ) (reflectedBiHeatFinitePart P))) := by
    convert hstar using 1
    funext epsilon
    rw [map_sub, map_div₀, reflectedBiHeatPairSum_conjugate_real,
      ReflectedBiHeatDatum.conjugate_x]
    simp
  exact tendsto_nhds_unique
    (tendsto_reflectedBiHeatPairSum_sub_thetaPole_finitePart P.conjugate) hstar'

/-- Critical-wall reflection preserves height and sends `Re z` to `1 - Re z`. -/
def ReflectedBiHeatDatum.wallReflect
    (P : ReflectedBiHeatDatum) : ReflectedBiHeatDatum :=
  P.conjugate.reflect

@[simp] theorem ReflectedBiHeatDatum.wallReflect_z (P : ReflectedBiHeatDatum) :
    P.wallReflect.z = 1 - (starRingEnd ℂ) P.z := rfl

@[simp] theorem ReflectedBiHeatDatum.wallReflect_x (P : ReflectedBiHeatDatum) :
    P.wallReflect.x = P.x := rfl

@[simp] theorem ReflectedBiHeatDatum.wallReflect_re (P : ReflectedBiHeatDatum) :
    P.wallReflect.z.re = 1 - P.z.re := by simp

@[simp] theorem ReflectedBiHeatDatum.wallReflect_im (P : ReflectedBiHeatDatum) :
    P.wallReflect.z.im = P.z.im := by simp

@[simp] theorem ReflectedBiHeatDatum.wallReflect_wallReflect
    (P : ReflectedBiHeatDatum) :
    P.wallReflect.wallReflect = P := by
  cases P
  simp [ReflectedBiHeatDatum.wallReflect, ReflectedBiHeatDatum.conjugate,
    ReflectedBiHeatDatum.reflect]

/-- Fixed locus of height-preserving reflection is exactly the critical wall. -/
theorem ReflectedBiHeatDatum.wallReflect_eq_iff_re_eq_half
    (P : ReflectedBiHeatDatum) :
    P.wallReflect = P ↔ P.z.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg (fun Q : ReflectedBiHeatDatum => Q.z.re) h
    simp at hre
    linarith
  · intro hre
    cases P with
    | mk z x hz0 hz1 hx =>
        have hz : 1 - (starRingEnd ℂ) z = z := by
          apply Complex.ext
          · simp
            linarith
          · simp
        simp [ReflectedBiHeatDatum.wallReflect, ReflectedBiHeatDatum.conjugate,
          ReflectedBiHeatDatum.reflect, hz]

/-- Regulated pair sum obeys exact Schwarz covariance under critical-wall reflection. -/
theorem reflectedBiHeatPairSum_wallReflect_real
    (P : ReflectedBiHeatDatum) (epsilon : ℝ) :
    reflectedBiHeatPairSum P.wallReflect (epsilon : ℂ) =
      (starRingEnd ℂ) (reflectedBiHeatPairSum P (epsilon : ℂ)) := by
  rw [ReflectedBiHeatDatum.wallReflect, reflectedBiHeatPairSum_reflect,
    reflectedBiHeatPairSum_conjugate_real]

/-- Canonical finite part obeys exact Schwarz covariance under critical-wall reflection. -/
theorem reflectedBiHeatFinitePart_wallReflect (P : ReflectedBiHeatDatum) :
    reflectedBiHeatFinitePart P.wallReflect =
      (starRingEnd ℂ) (reflectedBiHeatFinitePart P) := by
  rw [ReflectedBiHeatDatum.wallReflect, reflectedBiHeatFinitePart_reflect,
    reflectedBiHeatFinitePart_conjugate]

theorem reflectedBiHeatFinitePart_wallReflect_re (P : ReflectedBiHeatDatum) :
    (reflectedBiHeatFinitePart P.wallReflect).re =
      (reflectedBiHeatFinitePart P).re := by
  rw [reflectedBiHeatFinitePart_wallReflect]
  simp

theorem reflectedBiHeatFinitePart_wallReflect_im (P : ReflectedBiHeatDatum) :
    (reflectedBiHeatFinitePart P.wallReflect).im =
      -(reflectedBiHeatFinitePart P).im := by
  rw [reflectedBiHeatFinitePart_wallReflect]
  simp

/-- Exact canonical wall-reflection defect: only the imaginary channel survives. -/
theorem reflectedBiHeatFinitePart_sub_wallReflect (P : ReflectedBiHeatDatum) :
    reflectedBiHeatFinitePart P - reflectedBiHeatFinitePart P.wallReflect =
      (((2 * (reflectedBiHeatFinitePart P).im : ℝ) : ℂ) * I) := by
  rw [reflectedBiHeatFinitePart_wallReflect]
  apply Complex.ext <;> simp
  ring

/-- On critical wall the canonical theta finite part is real. -/
theorem reflectedBiHeatFinitePart_im_eq_zero_of_re_eq_half
    (P : ReflectedBiHeatDatum) (hre : P.z.re = 1 / 2) :
    (reflectedBiHeatFinitePart P).im = 0 := by
  have hw : P.wallReflect = P :=
    (P.wallReflect_eq_iff_re_eq_half).2 hre
  have hcov := reflectedBiHeatFinitePart_wallReflect P
  rw [hw] at hcov
  have him := congrArg Complex.im hcov
  simp at him
  linarith

end RHTower
