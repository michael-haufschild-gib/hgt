/-
Copyright (c) 2026 Michael L. Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael L. Walker
-/
import GaloisForLFunctions.RHTower.SuzukiGammaSkewFrequencyFlux
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Weighted Gamma-tail coercivity

Vertical translation by `σ ∈ (0,1)` makes the Gamma jump multiplier non-self-adjoint, but its
real part has an exact finite lower majorant. Pointwise in the jump length `s`,

`2(1 - cosh(σs) cos(xs))/(exp s - 1) ≥ -2(cosh(σs)-1)/(exp s - 1)`.

The second theorem certifies the load-bearing Hilbert energy step. If multiplication by the
physical logarithmic coordinate supplies `2L₀`, the shifted Gamma term loses at most `κ`, and the
self-adjoint seam term loses at most `τ`, then the forced equation bounds the weighted derivative
by the source. This is the algebraic core of the weak mollifier argument on the paper side.
-/

open Complex RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Negative majorant for the real part of the vertically shifted Gamma jump integrand. -/
def suzukiGammaShiftLowerKernel (σ s : ℝ) : ℝ :=
  2 * (Real.cosh (σ * s) - 1) / (Real.exp s - 1)

/-- Real part of the exact Gamma jump integrand on frequency `x + iσ`. -/
def suzukiGammaShiftRealIntegrand (σ x s : ℝ) : ℝ :=
  2 * (1 - Real.cosh (σ * s) * Real.cos (x * s)) / (Real.exp s - 1)

/-- Exact pointwise numerical-range lower bound for the shifted Gamma jump. -/
theorem neg_suzukiGammaShiftLowerKernel_le_realIntegrand
    (σ x : ℝ) {s : ℝ} (hs : 0 < s) :
    -suzukiGammaShiftLowerKernel σ s ≤
      suzukiGammaShiftRealIntegrand σ x s := by
  have hden : 0 < Real.exp s - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr hs)
  have hcos := Real.cos_le_one (x * s)
  have hcosh := Real.one_le_cosh (σ * s)
  rw [suzukiGammaShiftLowerKernel, suzukiGammaShiftRealIntegrand]
  calc
    -(2 * (Real.cosh (σ * s) - 1) / (Real.exp s - 1)) =
        (-(2 * (Real.cosh (σ * s) - 1))) / (Real.exp s - 1) := by ring
    _ ≤ 2 * (1 - Real.cosh (σ * s) * Real.cos (x * s)) /
          (Real.exp s - 1) := by
      apply (div_le_div_iff_of_pos_right hden).mpr
      nlinarith

theorem suzukiGammaShiftLowerKernel_nonneg
    (σ : ℝ) {s : ℝ} (hs : 0 < s) :
    0 ≤ suzukiGammaShiftLowerKernel σ s := by
  have hden : 0 < Real.exp s - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr hs)
  rw [suzukiGammaShiftLowerKernel]
  exact div_nonneg
    (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_cosh (σ * s))))
    hden.le

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
local instance suzukiGammaWeightedTailCoercivityLocalInst1 : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- **Weighted tail energy estimate.**

`Mu`, `Ru`, and `Tu` are respectively the physical `2L` term, shifted Gamma term, and bounded
self-adjoint seam term applied to the weighted derivative `u`. The hypotheses are their exact
quadratic-form bounds. The conclusion is the coercive norm estimate used after weak
mollification. -/
theorem suzukiGammaWeightedTailEnergy_norm_le
    (κ τ L₀ c : ℝ) (u Mu Ru Tu v g : H)
    (hbudget : c ≤ 2 * L₀ - κ - τ)
    (hM : 2 * L₀ * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ u Mu)
    (hR : -(κ * ‖u‖ ^ (2 : ℕ)) ≤ inner ℝ u Ru)
    (hT : inner ℝ u Tu ≤ τ * ‖u‖ ^ (2 : ℕ))
    (heq : Mu + Ru - Tu = g - v) :
    c * ‖u‖ ≤ ‖g - v‖ := by
  have hform :
      (2 * L₀ - κ - τ) * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ u (g - v) := by
    rw [← heq, inner_sub_right, inner_add_right]
    nlinarith
  have hinner :
      inner ℝ u (g - v) ≤ ‖u‖ * ‖g - v‖ :=
    le_trans (le_abs_self _) (abs_real_inner_le_norm u (g - v))
  have hscaled :
      c * ‖u‖ ^ (2 : ℕ) ≤ (2 * L₀ - κ - τ) * ‖u‖ ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_right hbudget (sq_nonneg ‖u‖)
  by_cases hu : u = 0
  · simp [hu]
  · have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    nlinarith

/-- Recover the ordinary weighted derivative from `u = v' - σv`. -/
theorem suzukiGammaWeightedTail_derivative_norm_le
    (σ : ℝ) (u v v' : H) (hu : u = v' - (σ : ℂ) • v) :
    ‖v'‖ ≤ ‖u‖ + |σ| * ‖v‖ := by
  have hv' : v' = u + (σ : ℂ) • v := by
    rw [hu]
    abel
  rw [hv']
  calc
    ‖u + (σ : ℂ) • v‖ ≤ ‖u‖ + ‖(σ : ℂ) • v‖ := norm_add_le _ _
    _ = ‖u‖ + |σ| * ‖v‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

end GaloisForLFunctions.RHTower
