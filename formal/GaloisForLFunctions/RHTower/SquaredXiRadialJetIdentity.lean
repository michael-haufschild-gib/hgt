import Mathlib

/-!
# Radial-derivative identity for squared-Xi jets: analytic core

The squared-radial jet identity (equation (4) of the source-alignment card) applies the operator
`D = (1/(2w)) d/dw` iteratively to `F(w) = L(1/2+w)/w` and re-expresses `D^n F` through the shifted
derivatives `L^(j)(1/2+w)` weighted by the reverse-Bessel magnitudes.  This file formalizes the exact
calculus content of the induction step (equation (6)) for an arbitrary smooth `L`, unconditionally:
the chain rule for a shifted iterated derivative and the single-term product rule
`d/dw [w^m L^(j)(1/2+w)] = m w^(m-1) L^(j)(1/2+w) + w^m L^(j+1)(1/2+w)`.
-/

open scoped Topology

namespace RHTower

/-- The radial operator `D f = f'/(2w)`. -/
noncomputable def radialOp (f : ℝ → ℝ) (w : ℝ) : ℝ := deriv f w / (2 * w)

/-- The radial profile `F(w) = L(1/2+w)/w`. -/
noncomputable def radialProfile (L : ℝ → ℝ) (w : ℝ) : ℝ := L (1 / 2 + w) / w

/-- Chain rule for a shifted iterated derivative: `d/dw [L^(j)(c+w)] = L^(j+1)(c+w)`. -/
theorem deriv_iteratedDeriv_shift
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (j : ℕ) (c w : ℝ) :
    deriv (fun v => iteratedDeriv j L (c + v)) w = iteratedDeriv (j + 1) L (c + w) := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j L) (c + w) :=
    (hL.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
  rw [show (fun v => iteratedDeriv j L (c + v)) = (iteratedDeriv j L) ∘ (fun v => c + v) from rfl,
    deriv_comp w hd (by fun_prop), ← iteratedDeriv_succ]
  simp

/-- **Single-term radial derivative (equation (6) core).**  For a smooth `L`,
`d/dw [w^m · L^(j)(1/2+w)] = m·w^(m-1)·L^(j)(1/2+w) + w^m·L^(j+1)(1/2+w)`. -/
theorem deriv_pow_mul_iteratedDeriv_shift
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (m j : ℕ) (w : ℝ) :
    deriv (fun v => v ^ m * iteratedDeriv j L (1 / 2 + v)) w =
      (m : ℝ) * w ^ (m - 1) * iteratedDeriv j L (1 / 2 + w) +
        w ^ m * iteratedDeriv (j + 1) L (1 / 2 + w) := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j L) (1 / 2 + w) :=
    (hL.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
  have hg : DifferentiableAt ℝ (fun v => iteratedDeriv j L (1 / 2 + v)) w :=
    hd.comp w (by fun_prop)
  have hpow : HasDerivAt (fun v : ℝ => v ^ m) ((m : ℝ) * w ^ (m - 1)) w := by
    simpa using hasDerivAt_pow m w
  have hshift : HasDerivAt (fun v => iteratedDeriv j L (1 / 2 + v))
      (iteratedDeriv (j + 1) L (1 / 2 + w)) w := by
    have h := hg.hasDerivAt
    rwa [deriv_iteratedDeriv_shift hL j (1 / 2) w] at h
  have hmul : HasDerivAt (fun v => v ^ m * iteratedDeriv j L (1 / 2 + v))
      ((m : ℝ) * w ^ (m - 1) * iteratedDeriv j L (1 / 2 + w) +
        w ^ m * iteratedDeriv (j + 1) L (1 / 2 + w)) w := by
    have h := hpow.mul hshift
    convert h using 1
  exact hmul.deriv

end RHTower
