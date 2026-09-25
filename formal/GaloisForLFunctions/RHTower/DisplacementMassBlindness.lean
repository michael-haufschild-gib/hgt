import GaloisForLFunctions.RHTower.CriticalLinePoissonPotential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mass blindness: why no `L¹` handle on the off-line divisor can decide the hypothesis

The critical-line potential decides the hypothesis through its **height**: `U ≡ 0` under the
hypothesis, and `U ≥ 1` somewhere otherwise, with the unit independent of how far the offending zero
sits from the line. This module proves that the **mass** of the same object carries none of that
information.

A single zero at displacement `d` contributes the bump `d²/(d² + (t − γ)²)`. Two exact computations
sit side by side:

* its height is `1`, attained at `t = γ`, for every `d ≠ 0`;
* its mass over any symmetric window is `2 d arctan(R/d)`, hence strictly below `π d` on the whole
  line.

So as `d → 0` the mass tends to zero while the height does not move. Every unconditional handle this
field has on the off-line divisor — Littlewood's lemma, Jensen's formula, the zero-density integrals
`∫ N(σ,T) dσ`, mollified moments, smoothed counting functions — bounds a quantity of the first kind,
a total displacement mass `Σ_ρ |δ_ρ|`. The final theorem here says that no such bound, at any
constant and any tolerance, constrains the height. The two norms are decoupled at every scale, and a
criterion that reads only the mass is blind to a near-line counterexample by construction, not by
weakness of the estimate.

This is the quantitative form of the earlier finding that the hypothesis is a separation target
rather than a resolution target: seeing a zero at displacement `d` requires resolution `d`, and an
average at any fixed resolution dilutes the bump by a factor that tends to zero.
-/

open Real MeasureTheory

namespace RHTower

noncomputable section

/-- A single Poisson bump: displacement `d`, centre `g`. -/
def bumpKernel (d g t : ℝ) : ℝ := d ^ (2 : ℕ) / (d ^ (2 : ℕ) + (t - g) ^ (2 : ℕ))

theorem poissonBumpTerm_eq_bumpKernel (t : ℝ) (ρ : XiDivisorSupport) :
    poissonBumpTerm t ρ = bumpKernel ((ρ : ℂ).re - 1 / 2) ((ρ : ℂ).im) t := rfl

theorem bumpKernel_neg (d g t : ℝ) : bumpKernel (-d) g t = bumpKernel d g t := by
  rw [bumpKernel, bumpKernel, neg_sq]

theorem bumpKernel_nonneg (d g t : ℝ) : 0 ≤ bumpKernel d g t :=
  div_nonneg (sq_nonneg _) (by positivity)

/-- The bump in scale-invariant form: height one, width `|d|`. -/
theorem bumpKernel_eq_scaled {d : ℝ} (hd : d ≠ 0) (g t : ℝ) :
    bumpKernel d g t = 1 / (1 + ((t - g) / d) ^ (2 : ℕ)) := by
  have hd2 : d ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hd
  have key : 1 + ((t - g) / d) ^ (2 : ℕ)
      = (d ^ (2 : ℕ) + (t - g) ^ (2 : ℕ)) / d ^ (2 : ℕ) := by
    rw [div_pow, add_div, div_self hd2]
  rw [bumpKernel, key, one_div_div]

/-- **The height.** The bump reaches one at its centre, whatever the displacement. -/
theorem bumpKernel_peak {d : ℝ} (hd : d ≠ 0) (g : ℝ) : bumpKernel d g g = 1 := by
  have hd2 : d ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hd
  rw [bumpKernel, sub_self, show ((0 : ℝ)) ^ (2 : ℕ) = 0 by norm_num, add_zero, div_self hd2]

/-- **The width.** The superlevel set at height `lam` is the interval of half-width
`|d| √((1−lam)/lam)`. -/
theorem bumpKernel_superlevel_iff {d : ℝ} (hd : d ≠ 0) (g t : ℝ) (lam : ℝ) :
    lam ≤ bumpKernel d g t ↔ lam * (t - g) ^ (2 : ℕ) ≤ (1 - lam) * d ^ (2 : ℕ) := by
  have hpos : 0 < d ^ (2 : ℕ) + (t - g) ^ (2 : ℕ) := by
    have : 0 < d ^ (2 : ℕ) := by positivity
    nlinarith [sq_nonneg (t - g)]
  rw [bumpKernel, le_div_iff₀ hpos]
  constructor <;> intro h <;> nlinarith

/-- At half height the superlevel set has half-width exactly `|d|`. -/
theorem bumpKernel_half_superlevel_iff {d : ℝ} (hd : d ≠ 0) (g t : ℝ) :
    1 / 2 ≤ bumpKernel d g t ↔ (t - g) ^ (2 : ℕ) ≤ d ^ (2 : ℕ) := by
  rw [bumpKernel_superlevel_iff hd g t (1 / 2)]
  constructor <;> intro h <;> nlinarith

/-- **The mass.** The exact mass of the bump over a symmetric window. -/
theorem integral_bumpKernel {d : ℝ} (hd : 0 < d) (g R : ℝ) :
    (∫ t in (g - R)..(g + R), bumpKernel d g t) = 2 * d * Real.arctan (R / d) := by
  have hd0 : d ≠ 0 := hd.ne'
  have hfun : (fun t => bumpKernel d g t)
      = fun t => (fun y => 1 / (1 + (y / d) ^ (2 : ℕ))) (t - g) := by
    funext t
    rw [bumpKernel_eq_scaled hd0]
  rw [hfun, intervalIntegral.integral_comp_sub_right
    (fun y => 1 / (1 + (y / d) ^ (2 : ℕ))) g]
  rw [show g - R - g = -R by ring, show g + R - g = R by ring]
  rw [intervalIntegral.integral_comp_div (fun x => 1 / (1 + x ^ (2 : ℕ))) hd0]
  rw [smul_eq_mul, integral_one_div_one_add_sq, neg_div, Real.arctan_neg]
  ring

/-- **The mass is bounded by `π d`, uniformly in the window.** -/
theorem integral_bumpKernel_lt {d : ℝ} (hd : 0 < d) (g R : ℝ) :
    (∫ t in (g - R)..(g + R), bumpKernel d g t) < Real.pi * d := by
  rw [integral_bumpKernel hd g R]
  have := Real.arctan_lt_pi_div_two (R / d)
  nlinarith

/-- **The no-go.** For every amplification constant and every tolerance there is a displacement
whose bump mass stays under the tolerance on every window, while the bump still attains its full
height one. No bound on the mass constrains the height. -/
theorem no_mass_bound_controls_height (g : ℝ) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧
      (∀ R : ℝ, C * (∫ t in (g - R)..(g + R), bumpKernel d g t) < ε) ∧
      bumpKernel d g g = 1 := by
  refine ⟨ε / (2 * C * Real.pi), by positivity, fun R => ?_, bumpKernel_peak (by positivity) g⟩
  have hd : (0 : ℝ) < ε / (2 * C * Real.pi) := by positivity
  have hmass := integral_bumpKernel_lt hd g R
  have hbound : Real.pi * (ε / (2 * C * Real.pi)) = ε / (2 * C) := by
    field_simp
  rw [hbound] at hmass
  have hlt : C * (∫ t in (g - R)..(g + R), bumpKernel (ε / (2 * C * Real.pi)) g t)
      < C * (ε / (2 * C)) := mul_lt_mul_of_pos_left hmass hC
  have : C * (ε / (2 * C)) = ε / 2 := by field_simp
  rw [this] at hlt
  linarith

/-- The transfer to the divisor: an off-line zero's bump has mass at most `π` times its
displacement, and height exactly one at its own ordinate. -/
theorem poissonBumpTerm_mass_lt {ρ : XiDivisorSupport} (h : 1 / 2 < (ρ : ℂ).re) (R : ℝ) :
    (∫ t in ((ρ : ℂ).im - R)..((ρ : ℂ).im + R), poissonBumpTerm t ρ)
      < Real.pi * ((ρ : ℂ).re - 1 / 2) := by
  have hd : 0 < (ρ : ℂ).re - 1 / 2 := by linarith
  simpa [poissonBumpTerm_eq_bumpKernel] using
    integral_bumpKernel_lt hd ((ρ : ℂ).im) R

end

end RHTower
