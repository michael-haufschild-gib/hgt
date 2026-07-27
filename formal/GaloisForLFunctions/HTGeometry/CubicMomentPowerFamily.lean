import Mathlib

/-!
# The cubic moment inequality fails for log-concave densities, and where it fails

For `φ(x) = exp(−x^p)` on `[0,∞)` — log-concave exactly for `p ≥ 1` — the moments are
`Mₖ = Γ((k+1)/p)/p`, so with `q = 1/p` the two-step ratios of `Lₖ = Mₖ/k!` are

```text
R₀ = Γ(3q)/(2Γ(q)) ,      R₂ = Γ(5q)/(12Γ(3q)) ,      R₄ = Γ(7q)/(30Γ(5q)) ,
```

and the cubic moment functional `C` has the sign of

```text
Ψ(q) = R₀ + 3R₄ − 4R₂ = Γ(3q)/(2Γ(q)) + Γ(7q)/(10Γ(5q)) − Γ(5q)/(3Γ(3q)) .
```

Three exact values:

```text
q = 1    (p = 1, exponential)     R = (1, 1, 1)                 Ψ = 1 + 3 − 4      = 0
q = 1/2  (p = 2, half-Gaussian)   R = (1/4, 1/8, 1/12)          Ψ = 1/4 + 1/4 − 1/2 = 0
q → 0    (p → ∞, uniform)         R = (1/6, 1/20, 1/42)         Ψ = 4/105 > 0
```

and the derivative at the exponential is a `γ`-free rational:

```text
Ψ′(1) = (9/2 − 2γ) + 3(101/15 − 2γ) − 4(71/12 − 2γ) = 9/2 + 101/5 − 71/3 = 31/30 > 0 .
```

Since `Ψ(1) = 0` and `Ψ′(1) > 0`, `Ψ(q) < 0` for `q` slightly below `1`, i.e. for `p` slightly above
`1` — squarely inside the log-concave range.  **So log-concavity does not imply `C ≥ 0`.**

The sign pattern on this family is `Ψ = 0` at `p = 1`, `Ψ < 0` on `(1,2)`, `Ψ = 0` at `p = 2`, `Ψ > 0`
for `p > 2`.  That matches the sign of `V‴` for `V = x^p`: `V″ = p(p−1)x^{p−2}` is decreasing exactly
on `1 < p < 2` and increasing exactly for `p > 2`.  The theta source has
`V″ = −(log Φ)″ ≥ 4π e^{2x}`, manifestly increasing, so it lies in the region where the family
satisfies the inequality — but that is a heuristic about one family, not a theorem.

This file records the exact arithmetic: the two equality cases, the uniform value, and the rational
derivative.
-/

open Real

namespace GaloisForLFunctions

namespace CubicMomentPower

/-- `Ψ` at a triple of two-step ratios. -/
noncomputable def ratioFunctional (R₀ R₂ R₄ : ℝ) : ℝ := R₀ + 3 * R₄ - 4 * R₂

/-- **Exponential (`p = 1`)**: all two-step ratios are `1` and the functional vanishes. -/
theorem ratioFunctional_exponential : ratioFunctional 1 1 1 = 0 := by
  unfold ratioFunctional; norm_num

/-- **Half-Gaussian (`p = 2`)**: `R = (1/4, 1/8, 1/12)` and the functional vanishes.  These values are
exact: `R₀ = Γ(3/2)/(2Γ(1/2)) = 1/4`, `R₂ = Γ(5/2)/(12Γ(3/2)) = 1/8`,
`R₄ = Γ(7/2)/(30Γ(5/2)) = 1/12`, each by one step of the Γ recurrence. -/
theorem ratioFunctional_halfGaussian : ratioFunctional (1 / 4) (1 / 8) (1 / 12) = 0 := by
  unfold ratioFunctional; norm_num

/-- **Uniform (`p → ∞`)**: `R = (1/6, 1/20, 1/42)` and the functional is `4/105 > 0`. -/
theorem ratioFunctional_uniform : ratioFunctional (1 / 6) (1 / 20) (1 / 42) = 4 / 105 := by
  unfold ratioFunctional; norm_num

theorem ratioFunctional_uniform_pos : 0 < ratioFunctional (1 / 6) (1 / 20) (1 / 42) := by
  rw [ratioFunctional_uniform]; norm_num

/-- The digamma values entering `Ψ′(1)`, as harmonic numbers: `ψ(n) = −γ + H_{n−1}`.  Only the
combinations below are needed, and in each the `γ` cancels. -/
theorem digamma_combination_one : (3 : ℝ) * (3 / 2) - 0 = 9 / 2 := by norm_num

theorem digamma_combination_two : (7 : ℝ) * (49 / 20) - 5 * (25 / 12) = 101 / 15 := by norm_num

theorem digamma_combination_three : (5 : ℝ) * (25 / 12) - 3 * (3 / 2) = 71 / 12 := by norm_num

/-- **The derivative at the exponential is `31/30`.**  With `Tᵢ(1) = 1, 3, 4` and the `γ`-free
logarithmic derivatives `9/2, 101/15, 71/12`, the Euler–Mascheroni terms cancel and

`Ψ′(1) = 1·(9/2) + 3·(101/15) − 4·(71/12) = 31/30`. -/
theorem psi_deriv_at_one : (1 : ℝ) * (9 / 2) + 3 * (101 / 15) - 4 * (71 / 12) = 31 / 30 := by
  norm_num

theorem psi_deriv_at_one_pos : (0 : ℝ) < 31 / 30 := by norm_num

/-- **The refutation, in the form it is used.**  A function vanishing at a point with strictly
positive derivative there is strictly negative immediately to the left.  Applied to `Ψ` at `q = 1`,
where `q < 1` corresponds to `p > 1` — the log-concave range — this exhibits log-concave densities
violating `C ≥ 0`. -/
theorem neg_left_of_deriv_pos {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivAt f d a)
    (h0 : f a = 0) (hd : 0 < d) :
    ∀ᶠ q in nhdsWithin a (Set.Iio a), f q < 0 := by
  have hslope : Filter.Tendsto (slope f a) (nhdsWithin a {a}ᶜ) (nhds d) :=
    hasDerivAt_iff_tendsto_slope.mp hf
  have hev : ∀ᶠ q in nhdsWithin a {a}ᶜ, 0 < slope f a q :=
    hslope.eventually (eventually_gt_nhds hd)
  have hsub : nhdsWithin a (Set.Iio a) ≤ nhdsWithin a {a}ᶜ :=
    nhdsWithin_mono a fun x hx => ne_of_lt hx
  filter_upwards [hsub hev, self_mem_nhdsWithin] with q hq hqlt
  rw [slope_def_field] at hq
  have hden : q - a < 0 := sub_neg.mpr hqlt
  by_contra hcon
  rw [not_lt] at hcon
  have hnum : 0 ≤ f q - f a := by rw [h0]; linarith
  have : (f q - f a) / (q - a) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hnum hden.le
  linarith


/-! ### The exponential is a strict local maximum: adding any Gaussian factor makes `C` negative

The repaired hypothesis suggested by the power family — increasing log-curvature, `V‴ ≥ 0` — fails at
the very first perturbation of the exponential, and the computation is exact.

Take `φ_s(x) = e^{−x} e^{−s x²}` on `[0,∞)`, `s ≥ 0`.  Here `V = x + s x²`, so `V″ = 2s ≥ 0` and
`V‴ = 0 ≥ 0`: log-concave with increasing (constant) log-curvature.  Differentiating the moments
under the integral at `s = 0`,

```text
∂ₛ Mₖ |₀ = −∫₀^∞ x^{k+2} e^{−x} dx = −(k+2)! ,      so      ∂ₛ Lₖ |₀ = −(k+1)(k+2) ,
```

and since `Lₖ(0) = 1` for every `k`, the two-step ratios satisfy

```text
∂ₛ Rₖ |₀ = ∂ₛ L_{k+2} − ∂ₛ Lₖ = −[(k+3)(k+4) − (k+1)(k+2)] = −(4k + 10) .
```

Hence

```text
∂ₛ Ψ |₀ = ∂ₛR₀ + 3∂ₛR₄ − 4∂ₛR₂ = −10 + 3(−26) − 4(−18) = −16 .
```

`Ψ(0) = 0` and `∂ₛΨ|₀ = −16 < 0`, so `Ψ < 0` for every small `s > 0`.  **`V‴ ≥ 0` does not imply
`C ≥ 0`**, and the exponential is a strict local maximum of `Ψ` in the Gaussian direction.

So no convexity-of-log-curvature hypothesis rescues the target: the counterexamples are not confined
to slowly-decaying densities after all — they reach into every neighbourhood of the exponential. -/

/-- `∂ₛ Rₖ|₀ = −(4k + 10)` for the Gaussian tilt of the exponential. -/
theorem gaussianTilt_ratioDeriv (k : ℕ) :
    -(((k : ℝ) + 3) * ((k : ℝ) + 4) - ((k : ℝ) + 1) * ((k : ℝ) + 2)) = -(4 * (k : ℝ) + 10) := by
  ring

/-- **The exponential is a strict local maximum in the Gaussian direction**: the derivative of `Ψ`
along `φ_s = e^{−x−sx²}` at `s = 0` is `−16`. -/
theorem gaussianTilt_psi_deriv :
    (-(4 * (0 : ℝ) + 10)) + 3 * (-(4 * (4 : ℝ) + 10)) - 4 * (-(4 * (2 : ℝ) + 10)) = -16 := by
  norm_num

theorem gaussianTilt_psi_deriv_neg : (-16 : ℝ) < 0 := by norm_num

/-- The refutation of the repaired hypothesis, in the form it is used: `Ψ(0) = 0` together with a
strictly negative derivative puts `Ψ` below zero immediately to the right. -/
theorem neg_right_of_deriv_neg {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivAt f d a)
    (h0 : f a = 0) (hd : d < 0) :
    ∀ᶠ s in nhdsWithin a (Set.Ioi a), f s < 0 := by
  have hslope : Filter.Tendsto (slope f a) (nhdsWithin a {a}ᶜ) (nhds d) :=
    hasDerivAt_iff_tendsto_slope.mp hf
  have hev : ∀ᶠ s in nhdsWithin a {a}ᶜ, slope f a s < 0 :=
    hslope.eventually (eventually_lt_nhds hd)
  have hsub : nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {a}ᶜ :=
    nhdsWithin_mono a fun x hx => (ne_of_lt hx).symm
  filter_upwards [hsub hev, self_mem_nhdsWithin] with s hs hsgt
  rw [slope_def_field] at hs
  have hden : 0 < s - a := sub_pos.mpr hsgt
  by_contra hcon
  rw [not_lt] at hcon
  have hnum : 0 ≤ f s - f a := by rw [h0]; linarith
  have : 0 ≤ (f s - f a) / (s - a) := div_nonneg hnum hden.le
  linarith

end CubicMomentPower

end GaloisForLFunctions
