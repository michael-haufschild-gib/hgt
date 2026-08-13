import GaloisForLFunctions.RHTower.SuzukiApertureCutoffScalarDerivative
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelDifferentialSystemCoupled

/-!
# Aperture derivative of Suzuki's compact Mellin transforms

This module differentiates the literal compact physical Mellin transform of each Fredholm
solution.  A locally fixed reciprocal clamp removes the apparent singularity of the Mellin weight
at zero; Suzuki's exact support gap proves that this changes no value.  The derivative is obtained
from the strong fixed-window `L¹` derivative and the scalar moving-cutoff Leibniz rule, so it holds
at arithmetic cusp apertures as well as on the classical pointwise regular locus.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Mellin weight `x^(-1/2+iz)` with its logarithm clamped away from zero. -/
def suzukiClampedMellinWeightValue (c : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((-(1 / 2 : ℂ) + I * z) * (Real.log (max c x) : ℂ))

/-- Continuous interval realization of the clamped Mellin weight. -/
def suzukiClampedMellinWeight
    {B c : ℝ} (hc : 0 < c) (z : ℂ) : C(ClosedInterval 0 B, ℂ) where
  toFun x := suzukiClampedMellinWeightValue c z (x : ℝ)
  continuous_toFun := by
    have hmax : Continuous (fun x : ClosedInterval 0 B => max c (x : ℝ)) :=
      continuous_const.max continuous_subtype_val
    have hlog : Continuous (fun x : ClosedInterval 0 B =>
        Real.log (max c (x : ℝ))) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hcomp := ContinuousAt.comp
        (f := fun y : ClosedInterval 0 B => max c (y : ℝ))
        (g := Real.log)
        (Real.continuousAt_log
          (ne_of_gt (lt_of_lt_of_le hc (le_max_left c (x : ℝ)))))
        hmax.continuousAt
      change ContinuousAt (Real.log ∘ fun y : ClosedInterval 0 B => max c (y : ℝ)) x
      exact hcomp
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

@[simp] theorem suzukiClampedMellinWeight_apply
    {B c : ℝ} (hc : 0 < c) (z : ℂ) (x : ClosedInterval 0 B) :
    suzukiClampedMellinWeight hc z x =
      suzukiClampedMellinWeightValue c z (x : ℝ) := rfl

/-- Literal compact physical Mellin transform
`∫₀ᵃ φ_a^ε(x) x^(1/2+iz) dx/x`.  The reciprocal clamp is invisible because the Fredholm
solution vanishes on `[0,1/a]`, but makes the total integrand continuous at zero. -/
def suzukiHankelCompactMellin
    (epsilon : SuzukiHankelSign) (omega a : ℝ)
    (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..a,
    suzukiClampedMellinWeightValue (1 / a) z x *
      suzukiHankelPhiGlobal epsilon omega a homega ha x

/-- Total aperture curve used for real differentiation. -/
def suzukiHankelCompactMellinRight
    (epsilon : SuzukiHankelSign) (omega : ℝ) (homega : 1 < omega)
    (z : ℂ) (a : ℝ) : ℂ :=
  if ha : 1 < a then
    suzukiHankelCompactMellin epsilon omega a homega ha z
  else 0

/-- On a fixed enclosing window, replacing the moving reciprocal clamp by `1/B` does not alter
the compact Mellin integral. -/
theorem suzukiHankelCompactMellin_eq_fixedClamp
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (haB : a < B) (z : ℂ) :
    suzukiHankelCompactMellin epsilon omega a homega ha z =
      ∫ x in (0 : ℝ)..a,
        suzukiClampedMellinWeightValue (1 / B) z x *
          suzukiHankelPhiGlobal epsilon omega a homega ha x := by
  unfold suzukiHankelCompactMellin
  apply intervalIntegral.integral_congr
  intro x hx
  have h0a : 0 ≤ a := by linarith
  rw [uIcc_of_le h0a] at hx
  by_cases hxc : x ≤ 1 / a
  · change suzukiClampedMellinWeightValue (1 / a) z x *
        suzukiHankelPhiGlobal epsilon omega a homega ha x =
      suzukiClampedMellinWeightValue (1 / B) z x *
        suzukiHankelPhiGlobal epsilon omega a homega ha x
    rw [suzukiHankelPhiGlobal_eq_zero_below_reciprocal
      epsilon homega ha hx.1 hxc, mul_zero, mul_zero]
  · have hax : 1 / a < x := lt_of_not_ge hxc
    have hBa : 1 / B < 1 / a := by
      exact one_div_lt_one_div_of_lt (by linarith) haB
    have hBx : 1 / B < x := hBa.trans hax
    change suzukiClampedMellinWeightValue (1 / a) z x *
        suzukiHankelPhiGlobal epsilon omega a homega ha x =
      suzukiClampedMellinWeightValue (1 / B) z x *
        suzukiHankelPhiGlobal epsilon omega a homega ha x
    unfold suzukiClampedMellinWeightValue
    rw [max_eq_right hax.le, max_eq_right hBx.le]

/-- The fixed-window scalar pairing is exactly the literal compact Mellin transform. -/
theorem suzukiIntervalL1ContinuousPairing_fixedWindowPhi_eq_compactMellin
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B)
    (z : ℂ) :
    suzukiIntervalL1ContinuousPairing B
        (suzukiClampedMellinWeight
          (B := B) (show 0 < 1 / B by positivity) z)
        (suzukiApertureCutoffL1 a B
          (suzukiFixedWindowPhiL1 epsilon omega B homega hB a)) =
      suzukiHankelCompactMellin epsilon omega a homega ha z := by
  let w := suzukiClampedMellinWeight
    (B := B) (show 0 < 1 / B by positivity) z
  let P := suzukiFixedWindowPhiL1 epsilon omega B homega hB a
  have hcut := suzukiApertureCutoffL1_ae a B P
  have hP := suzukiFixedWindowPhiL1_ae_global
    epsilon homega hB ha haB
  rw [suzukiHankelCompactMellin_eq_fixedClamp epsilon homega ha haB z]
  rw [suzukiIntervalL1ContinuousPairing_eq_integral]
  let F : ℝ → ℂ := fun x =>
    suzukiClampedMellinWeightValue (1 / B) z x *
      suzukiHankelPhiGlobal epsilon omega a homega ha x
  calc
    (∫ x : ClosedInterval 0 B,
        w x * suzukiApertureCutoffL1 a B P x ∂volume) =
        ∫ x : ClosedInterval 0 B,
          (suzukiApertureSet a B).indicator (fun x => F (x : ℝ)) x
            ∂volume := by
      apply integral_congr_ae
      filter_upwards [hcut, hP] with x hcutx hPx
      rw [hcutx]
      by_cases hx : x ∈ suzukiApertureSet a B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hPx]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    _ = ∫ x in (0 : ℝ)..a, F x :=
      integral_subtype_apertureSet_eq_intervalIntegral B a (by linarith) haB.le F
    _ = _ := rfl

/-- Local fixed-window realization of the total compact Mellin aperture curve. -/
theorem suzukiHankelCompactMellinRight_eventuallyEq_fixedWindowPairing
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B)
    (z : ℂ) :
    suzukiHankelCompactMellinRight epsilon omega homega z =ᶠ[𝓝 a]
      fun b : ℝ =>
        suzukiIntervalL1ContinuousPairing B
          (suzukiClampedMellinWeight
            (B := B) (show 0 < 1 / B by positivity) z)
          (suzukiApertureCutoffL1 b B
            (suzukiFixedWindowPhiL1 epsilon omega B homega hB b)) := by
  filter_upwards [Ioo_mem_nhds ha haB] with b hb
  rw [suzukiHankelCompactMellinRight, dif_pos hb.1]
  exact (suzukiIntervalL1ContinuousPairing_fixedWindowPhi_eq_compactMellin
    epsilon homega hB hb.1 hb.2 z).symm

/-- Aperture derivative of the literal compact Mellin transform at every `a>1`, including
arithmetic cusp apertures.  The derivative is expressed through the already proved strong `L¹`
Fredholm derivative plus the literal moving endpoint. -/
theorem hasDerivAt_suzukiHankelCompactMellinRight
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    let B := a + 1
    let hB : 1 < B := by linarith
    let haB : a < B := by linarith
    let w := suzukiClampedMellinWeight
      (B := B) (show 0 < 1 / B by positivity) z
    HasDerivAt (suzukiHankelCompactMellinRight epsilon omega homega z)
      (suzukiIntervalL1ContinuousPairing B w
          (suzukiApertureCutoffL1 a B
            (suzukiFixedWindowPhiDerivativeL1
              epsilon omega B homega hB a (by linarith) haB)) +
        w ⟨a, ⟨by linarith, haB.le⟩⟩ *
          suzukiHankelPhiGlobal epsilon omega a homega ha a) a := by
  dsimp only
  let B := a + 1
  let hB : 1 < B := by dsimp only [B]; linarith
  let haB : a < B := by dsimp only [B]; linarith
  let u := suzukiFixedWindowPhiL1 epsilon omega B homega hB
  let du := suzukiFixedWindowPhiDerivativeL1
    epsilon omega B homega hB a (by linarith : 0 < a) haB
  let f := suzukiFixedWindowPhiContinuous
    epsilon omega B homega hB a (by linarith : 0 < a) haB.le
  let w := suzukiClampedMellinWeight
    (B := B) (show 0 < 1 / B by positivity) z
  have hu : HasDerivAt u du a :=
    hasDerivAt_suzukiFixedWindowPhiL1 epsilon homega hB
      (by linarith : 0 < a) haB
  have huf : u a = ContinuousMap.toLp 1 volume ℂ f := by
    exact (suzukiFixedWindowPhiContinuous_toLp_one_eq
      epsilon omega B homega hB a (by linarith) haB.le).symm
  have hpair :=
    hasDerivAt_suzukiIntervalL1ContinuousPairing_apertureCutoff
      (by linarith : 0 < a) haB hu f w huf
  have hev :=
    suzukiHankelCompactMellinRight_eventuallyEq_fixedWindowPairing
      epsilon homega hB ha haB z
  have hfpoint : f ⟨a, ⟨by linarith, haB.le⟩⟩ =
      suzukiHankelPhiGlobal epsilon omega a homega ha a := by
    change suzukiFixedWindowPhiPoint epsilon omega B homega hB a
      ⟨a, ⟨by linarith, haB.le⟩⟩ = _
    exact suzukiFixedWindowPhiPoint_eq_global
      epsilon homega ha hB haB.le _ (by linarith)
  rw [hfpoint] at hpair
  exact hpair.congr_of_eventuallyEq (by simpa only [w, u] using hev)

end RHTower
