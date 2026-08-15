import GaloisForLFunctions.RHTower.XiWardCubicPrimeGammaSecantQuantumMismatchNoGo
import GaloisForLFunctions.RHTower.XiWardCubicHerglotzExternalMixedJet

/-!
# Cubic Ward adaptive-secant half-density quantum (W-H208)

W-H207 proves that every fixed strict-Euler secant reflection gap is too soft at the critical
line to pay the cubic Hellinger quantum.  This module identifies the unique scale visible in that
failure which has the correct homogeneity.  Coalesce the secant aperture and set its pole rate to
twice the horizontal depth.  The resulting reflection defect is exactly

`-8 / (9 a^2)`.

After multiplication by the half-density factor `a`, its square is not merely comparable to the
cubic Hellinger self-charge: with universal normalization `345 / 2048` it is exactly equal to
`115 / (864 a^3)`.  The doubled rate is the same horizontal doubling already generated
holomorphically by the W-H199 bichamber map.

This exact identity is not itself a source contraction.  For `a <= 1/4`, the adaptive rate
`2a <= 1/2` lies below every literal primitive Euler rate, which is strictly larger than `1/2`.
Thus the quantum cannot be obtained by selecting an Euler cell whose rate happens to match the
zero.  The positive survivor is precise: horizontal doubling and its half-density must be created
before divisor restriction by the completed bichamber residue current; primitive congruence may
only be applied afterward to its source trace.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Coalescent reflection defect of a lower Cauchy secant with pole rate `lambda`. -/
def xiWardCubicCoalescentLowerSecantReflectionDefect
    (lambda a : ℝ) : ℝ :=
  -4 * a * lambda /
    ((lambda - a) ^ 2 * (lambda + a) ^ 2)

/-- Finite-aperture primitive defect converges to its coalescent boundary value. -/
theorem tendsto_xiWardCubicPrimitiveLowerSecantReflectionDefect_aperture_zero
    {lambda a : ℝ} (ha : 0 < a) (hala : a < lambda) :
    Tendsto
      (fun c : ℝ =>
        xiWardCubicPrimitiveLowerSecantReflectionDefect lambda c a)
      (nhds 0)
      (nhds (xiWardCubicCoalescentLowerSecantReflectionDefect lambda a)) := by
  have hlma : 0 < lambda - a := sub_pos.mpr hala
  have hlpa : 0 < lambda + a := by linarith
  have hcont : ContinuousAt
      (fun c : ℝ =>
        xiWardCubicPrimitiveLowerSecantReflectionDefect lambda c a) 0 := by
    unfold xiWardCubicPrimitiveLowerSecantReflectionDefect
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa only [add_zero] using
        mul_ne_zero
          (mul_ne_zero (mul_ne_zero hlma.ne' hlma.ne') hlpa.ne') hlpa.ne'
  convert hcont.tendsto using 1
  unfold xiWardCubicPrimitiveLowerSecantReflectionDefect
    xiWardCubicCoalescentLowerSecantReflectionDefect
  field_simp [hlma.ne', hlpa.ne']
  ring

/-- **W-H208 doubled-rate law.**  At adaptive rate `lambda = 2a`, the coalescent reflection
defect has the exact inverse-square scale required by the cubic charge. -/
theorem xiWardCubicCoalescentLowerSecantReflectionDefect_two_mul
    {a : ℝ} (ha : 0 < a) :
    xiWardCubicCoalescentLowerSecantReflectionDefect (2 * a) a =
      -8 / (9 * a ^ 2) := by
  unfold xiWardCubicCoalescentLowerSecantReflectionDefect
  field_simp [ha.ne']
  ring

/-- **W-H208 half-density identity.**  Half-density times squared adaptive reflection defect is
exactly the cubic Hellinger self-charge, with one universal normalization. -/
theorem cubicLogMomentHellingerHorizontalKernel_eq_adaptiveSecantHalfDensity
    {a : ℝ} (ha : 0 < a) :
    cubicLogMomentHellingerHorizontalKernel a a =
      (345 / 2048 : ℝ) * a *
        xiWardCubicCoalescentLowerSecantReflectionDefect (2 * a) a ^ 2 := by
  rw [xiWardCubicCoalescentLowerSecantReflectionDefect_two_mul ha,
    cubicLogMomentHellingerHorizontalKernel_self ha]
  field_simp [ha.ne']
  ring

/-- Finite secants at the adaptive rate converge, after the universal half-density
normalization, to the exact cubic Hellinger self-charge. -/
theorem tendsto_xiWardCubicAdaptiveSecantHalfDensity_charge
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun c : ℝ =>
        (345 / 2048 : ℝ) * a *
          xiWardCubicPrimitiveLowerSecantReflectionDefect (2 * a) c a ^ 2)
      (nhds 0)
      (nhds (cubicLogMomentHellingerHorizontalKernel a a)) := by
  have hala : a < 2 * a := by linarith
  have hdef :=
    tendsto_xiWardCubicPrimitiveLowerSecantReflectionDefect_aperture_zero ha hala
  have hscaled : Tendsto
      (fun c : ℝ =>
        ((345 / 2048 : ℝ) * a) *
          xiWardCubicPrimitiveLowerSecantReflectionDefect (2 * a) c a ^ 2)
      (nhds 0)
      (nhds (((345 / 2048 : ℝ) * a) *
        xiWardCubicCoalescentLowerSecantReflectionDefect (2 * a) a ^ 2)) :=
    (hdef.pow 2).const_mul ((345 / 2048 : ℝ) * a)
  convert hscaled using 1
  · funext c
    ring
  rw [cubicLogMomentHellingerHorizontalKernel_eq_adaptiveSecantHalfDensity ha]
  ring

/-- W-H199's pre-divisor holomorphic chamber map generates exactly the doubled horizontal rate
appearing in the adaptive half-density identity. -/
theorem xiWardCubicBichamberRightDouble_reflection_re
    (z : ℂ) :
    (xiWardCubicBichamberRightDouble z (star z)).re = 2 * z.re := by
  rw [xiWardCubicBichamberRightDouble_reflection]
  simp

/-- Sharp source-faithfulness wall: near the critical line the adaptive doubled rate lies outside
the strict primitive Euler source sector. -/
theorem xiWardCubic_adaptiveRate_lt_primitiveFrequency
    (pe : Nat.Primes × ℕ) {a : ℝ} (ha : a ≤ 1 / 4) :
    2 * a < xiGammaEulerPrimitiveLogFrequency pe := by
  have hfreq := half_lt_xiGammaEulerPrimitiveLogFrequency pe
  linarith

/-- Consequently no primitive Euler cell can literally realize the adaptive rate at depth at
most `1/4`; the match must arise collectively through completed residue transport. -/
theorem xiWardCubic_adaptiveRate_ne_primitiveFrequency
    (pe : Nat.Primes × ℕ) {a : ℝ} (ha : a ≤ 1 / 4) :
    2 * a ≠ xiGammaEulerPrimitiveLogFrequency pe :=
  ne_of_lt (xiWardCubic_adaptiveRate_lt_primitiveFrequency pe ha)

end

end RHTower
