import GaloisForLFunctions.RHTower.ReflectedBiHeatGammaCoefficient
import GaloisForLFunctions.RHTower.HeatEchoCompleted
import GaloisForLFunctions.RHTower.LevinsonDetectorFE
import GaloisForLFunctions.RHTower.PolarizedAdditiveHeatSharpRemainder

/-!
# Completed channels of the reflected bi-heat pairing

The two singular--regular terms in the reflected Jonquière product have coefficients

`heatEchoC z * ζ(1-z)` and `ζ(z) * heatEchoC (1-z)`.

Both are exactly one half of the same completed zeta value.  This module records the literal
coefficient identities and their equality under the unconditional zeta functional equation.
-/

open Complex Filter Topology

namespace RHTower

/-- The card's completed zeta factor
`Lambda(s) = pi^(-s/2) Gamma(s/2) zeta(s)`. -/
noncomputable def reflectedCompletedLambda (s : ℂ) : ℂ :=
  Complex.Gammaℝ s * riemannZeta s

theorem reflectedCompletedLambda_eq (s : ℂ) :
    reflectedCompletedLambda s =
      ((Real.pi : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s := by
  rw [reflectedCompletedLambda, Complex.Gammaℝ]

/-- First reflected cross coefficient, equation `(9)`. -/
noncomputable def reflectedBiHeatLeftCrossCoefficient (z : ℂ) : ℂ :=
  heatEchoC z * riemannZeta (1 - z)

/-- Second reflected cross coefficient, equation `(10)`. -/
noncomputable def reflectedBiHeatRightCrossCoefficient (z : ℂ) : ℂ :=
  riemannZeta z * heatEchoC (1 - z)

theorem reflectedBiHeatLeftCrossCoefficient_eq_completed
    (P : ReflectedBiHeatRegulator) :
    reflectedBiHeatLeftCrossCoefficient P.z =
      1 / 2 * reflectedCompletedLambda (1 - P.z) := by
  have hz2 : P.z.re < 2 := by linarith [P.z_re_lt_one]
  have hpow : ((Real.pi : ℝ) : ℂ) ^ ((P.z - 1) / 2) =
      ((Real.pi : ℝ) : ℂ) ^ (-(1 - P.z) / 2) := by
    congr 1
    ring
  rw [reflectedBiHeatLeftCrossCoefficient,
    heatEchoC_eq_completed P.z_re_pos hz2,
    reflectedCompletedLambda_eq, hpow]
  ring

theorem reflectedBiHeatRightCrossCoefficient_eq_completed
    (P : ReflectedBiHeatRegulator) :
    reflectedBiHeatRightCrossCoefficient P.z =
      1 / 2 * reflectedCompletedLambda P.z := by
  have h0 : 0 < (1 - P.z).re := by simp; linarith [P.z_re_lt_one]
  have h2 : (1 - P.z).re < 2 := by simp; linarith [P.z_re_pos]
  have hpow : ((Real.pi : ℝ) : ℂ) ^ (((1 - P.z) - 1) / 2) =
      ((Real.pi : ℝ) : ℂ) ^ (-P.z / 2) := by
    congr 1
    ring
  have hgamma : (1 - (1 - P.z)) / 2 = P.z / 2 := by ring
  rw [reflectedBiHeatRightCrossCoefficient,
    heatEchoC_eq_completed h0 h2,
    reflectedCompletedLambda_eq, hpow, hgamma]
  ring

/-- Unconditional functional equation for the card's completed factor on the open strip. -/
theorem reflectedCompletedLambda_one_sub (P : ReflectedBiHeatRegulator) :
    reflectedCompletedLambda (1 - P.z) = reflectedCompletedLambda P.z := by
  have h1z : 0 < (1 - P.z).re := by simp; linarith [P.z_re_lt_one]
  rw [reflectedCompletedLambda, reflectedCompletedLambda,
    ← completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE h1z,
    ← completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE P.z_re_pos,
    completedRiemannZeta_one_sub]

/-- Equations `(9)`--`(10)`: both small-aperture channels carry the same completed coefficient. -/
theorem reflectedBiHeat_crossCoefficients_eq (P : ReflectedBiHeatRegulator) :
    reflectedBiHeatLeftCrossCoefficient P.z =
      reflectedBiHeatRightCrossCoefficient P.z := by
  rw [reflectedBiHeatLeftCrossCoefficient_eq_completed P,
    reflectedBiHeatRightCrossCoefficient_eq_completed P,
    reflectedCompletedLambda_one_sub P]

/-- Premise-free coefficient capstone on the card's closed parameter space. -/
theorem reflectedBiHeatCompletedChannels_capstone :
    ∀ P : ReflectedBiHeatRegulator,
      reflectedBiHeatLeftCrossCoefficient P.z =
        reflectedBiHeatRightCrossCoefficient P.z := by
  intro P
  exact reflectedBiHeat_crossCoefficients_eq P

/-! ## Reflected aperture-scale geometry -/

/-- Real scale order of the `x^((z-1)/2)` channel. -/
noncomputable def reflectedBiHeatLeftScaleOrder (z : ℂ) : ℝ := (z.re - 1) / 2

/-- Real scale order of the `x^(-z/2)` channel. -/
noncomputable def reflectedBiHeatRightScaleOrder (z : ℂ) : ℝ := -z.re / 2

theorem reflectedBiHeat_scaleOrder_difference (z : ℂ) :
    reflectedBiHeatLeftScaleOrder z - reflectedBiHeatRightScaleOrder z =
      z.re - 1 / 2 := by
  rw [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
  ring

theorem reflectedBiHeat_scaleOrders_eq_iff (z : ℂ) :
    reflectedBiHeatLeftScaleOrder z = reflectedBiHeatRightScaleOrder z ↔
      z.re = 1 / 2 := by
  rw [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
  constructor <;> intro h
  · linarith
  · linarith

theorem reflectedBiHeat_scaleOrders_reflect_left (z : ℂ) :
    reflectedBiHeatLeftScaleOrder (1 - z) = reflectedBiHeatRightScaleOrder z := by
  rw [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
  simp

theorem reflectedBiHeat_scaleOrders_reflect_right (z : ℂ) :
    reflectedBiHeatRightScaleOrder (1 - z) = reflectedBiHeatLeftScaleOrder z := by
  rw [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
  simp

/-- Premise-free scale-tomography capstone: difference, reflection exchange, and self-dual wall. -/
theorem reflectedBiHeatScaleTomography_capstone :
    ∀ P : ReflectedBiHeatRegulator,
      (reflectedBiHeatLeftScaleOrder P.z - reflectedBiHeatRightScaleOrder P.z =
          P.z.re - 1 / 2) ∧
      (reflectedBiHeatLeftScaleOrder (1 - P.z) =
          reflectedBiHeatRightScaleOrder P.z) ∧
      (reflectedBiHeatRightScaleOrder (1 - P.z) =
          reflectedBiHeatLeftScaleOrder P.z) ∧
      (reflectedBiHeatLeftScaleOrder P.z = reflectedBiHeatRightScaleOrder P.z ↔
          P.z.re = 1 / 2) := by
  intro P
  exact ⟨reflectedBiHeat_scaleOrder_difference P.z,
    reflectedBiHeat_scaleOrders_reflect_left P.z,
    reflectedBiHeat_scaleOrders_reflect_right P.z,
    reflectedBiHeat_scaleOrders_eq_iff P.z⟩

/-! ## Exact reflected Jonquière remainder -/

/-- The heat-averaged remainder after subtracting all four principal reflected channels. -/
noncomputable def reflectedBiHeatSharpRemainder
    (P : ReflectedBiHeatRegulator) (x : ℝ) : ℂ :=
  polarizedHeatSharpRemainder P.z ((starRingEnd ℂ) (1 - P.z)) x

/-- At complementary regulator-zero orders, every omitted Jonquière term is `o(1)`. -/
theorem tendsto_reflectedBiHeatSharpRemainder (P : ReflectedBiHeatRegulator) :
    Tendsto (reflectedBiHeatSharpRemainder P)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hw₀ : 0 < ((starRingEnd ℂ) (1 - P.z)).re := by
    simp
    linarith [P.z_re_lt_one]
  have hw₁ : ((starRingEnd ℂ) (1 - P.z)).re < 1 := by
    simp
    linarith [P.z_re_pos]
  exact tendsto_polarizedHeatSharpRemainder
    P.z_re_pos P.z_re_lt_one hw₀ hw₁

/-- Premise-free reflected remainder capstone. -/
theorem reflectedBiHeatSharpRemainder_capstone :
    ∀ P : ReflectedBiHeatRegulator,
      Tendsto (reflectedBiHeatSharpRemainder P)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro P
  exact tendsto_reflectedBiHeatSharpRemainder P

end RHTower
