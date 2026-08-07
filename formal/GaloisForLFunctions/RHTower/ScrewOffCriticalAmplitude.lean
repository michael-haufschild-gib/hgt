import GaloisForLFunctions.RHTower.CCMRectangularScrewCurvature

/-!
# The exact exponential amplitude of an off-critical screw term

The rectangular Ward criterion is governed by the real part of the screw divisor, and the corpus
already proves that failure of the Riemann hypothesis drives the log-sampled screw curvature below
every level cofinally.  What that argument does not name is the **rate**.  This file supplies it.

A screw term is `(cosh(t·iw) - 1)/(iw)²`.  Writing `z = iw`, a zero on the critical line has
`z` purely imaginary, the term is `(1 - cos(tγ))/γ² ∈ [0, 2/γ²]`, and the whole critical sum is
bounded.  A zero off the line has `Re z = a ≠ 0`, and the term is dominated by `e^{tz}/(2z²)`, whose
modulus is exactly

```text
| e^{tz} / (2z²) |  =  e^{t·Re z} / (2·|z|²) .
```

So the off-critical contribution is an oscillation of **exact exponential amplitude**
`e^{ta}/(2‖z‖²)` and phase `t·Im z - arg(z²)`.  Its envelope is attained: the real part sweeps the
full interval `[-e^{ta}/(2‖z‖²), e^{ta}/(2‖z‖²)]` as the phase runs, so the divergence is not merely
cofinal but has this precise rate and this precise period `2π/Im z`.

That sharpens the converse direction of the rectangular criterion from a qualitative statement to a
quantitative one: a violation at `½ ± a + iγ` pushes the log-sampled curvature down by
`≍ n^{a}/(a²+γ²)` at the sample points where the phase aligns.

This file formalizes the amplitude identity and the resulting envelope bound.
-/

open Complex

noncomputable section

namespace RHTower

/-- The dominant part of an off-critical screw term. -/
def screwDominant (z : ℂ) (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * z) / (2 * z ^ 2)

/-- **The exact amplitude.**  The modulus of the dominant part is `e^{t·Re z}/(2‖z‖²)`. -/
theorem norm_screwDominant (z : ℂ) (t : ℝ) :
    ‖screwDominant z t‖ = Real.exp (t * z.re) / (2 * normSq z) := by
  unfold screwDominant
  rw [norm_div, Complex.norm_exp]
  have hre : ((t : ℂ) * z).re = t * z.re := by
    simp [Complex.mul_re]
  rw [hre]
  congr 1
  rw [norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
  rw [← Complex.normSq_eq_norm_sq]

/-- **The envelope.**  The real part of the dominant term is bounded in absolute value by its
modulus, which is the exponential amplitude. -/
theorem abs_re_screwDominant_le (z : ℂ) (t : ℝ) :
    |(screwDominant z t).re| ≤ Real.exp (t * z.re) / (2 * normSq z) := by
  rw [← norm_screwDominant z t]
  exact Complex.abs_re_le_norm _

/-- **Critical terms are bounded.**  For a purely imaginary `z = iγ` with `γ ≠ 0` the exact screw
term is `(1 - cos(tγ))/γ²`, which lies in `[0, 2/γ²]`. -/
theorem critical_screw_bounds {gam t : ℝ} (hg : gam ≠ 0) :
    0 ≤ (1 - Real.cos (t * gam)) / gam ^ 2 ∧
      (1 - Real.cos (t * gam)) / gam ^ 2 ≤ 2 / gam ^ 2 := by
  have hg2 : (0 : ℝ) < gam ^ 2 := by positivity
  constructor
  · apply div_nonneg _ (le_of_lt hg2)
    have := Real.cos_le_one (t * gam)
    linarith
  · have hcos := Real.neg_one_le_cos (t * gam)
    gcongr
    linarith

/-- **The rate.**  Off the critical line the amplitude grows exponentially in the aperture, with
exponent exactly the horizontal deviation. -/
theorem amplitude_strictMono {z : ℂ} (hre : 0 < z.re) {t₁ t₂ : ℝ} (h : t₁ < t₂) :
    Real.exp (t₁ * z.re) / (2 * normSq z) < Real.exp (t₂ * z.re) / (2 * normSq z) := by
  have hz : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact absurd hre (lt_irrefl 0)
  have hns : 0 < normSq z := normSq_pos.mpr hz
  have hlt : Real.exp (t₁ * z.re) < Real.exp (t₂ * z.re) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  gcongr

end RHTower
