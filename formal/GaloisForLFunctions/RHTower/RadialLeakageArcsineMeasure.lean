import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import GaloisForLFunctions.RHTower.ConstrainedProlateExteriorWeil

/-!
# The limiting radial leakage measure and its arcsine slices

The exterior Fourier leakage of the constrained two-mode prolate source has, after normalization
by the first leakage scale, the limiting radial density

```text
dν∞(x) = (8/(11π)) · dx/(x√(x² − 1))   on (1, ∞).
```

This module evaluates every tail slice of that density.  The function `x ↦ −arcsin(1/x)` is an
antiderivative of `x ↦ 1/(x√(x² − 1))` on `(1, ∞)` and tends to `0` at `+∞`, so

```text
∫_a^∞ dx/(x√(x² − 1)) = arcsin(1/a)   for every a ≥ 1.
```

At `a = 1` this is the total mass `π/2`, giving the exact total mass `4/11` of `ν∞`; at an integer
dilation `a = k` it is the arcsine diagonal of the radial dilation Gram matrix.  The resulting
slices are exactly the summands of the already-defined universal archimedean coefficient
`constrainedProlateArchConstant`, so the arcsine spectrum is a family of tail integrals of a
single density rather than a formal series.
-/

open MeasureTheory Filter Set

noncomputable section

namespace RHTower

/-- The limiting radial leakage density `1/(x√(x² − 1))` on `(1, ∞)`. -/
def radialLeakageDensity (x : ℝ) : ℝ := 1 / (x * Real.sqrt (x ^ 2 - 1))

theorem radialLeakageDensity_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ radialLeakageDensity x := by
  unfold radialLeakageDensity
  positivity

/-- On `(1, ∞)` the density has the elementary antiderivative `−arcsin(1/x)`. -/
theorem hasDerivAt_neg_arcsin_one_div {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y : ℝ => -Real.arcsin (1 / y)) (radialLeakageDensity x) x := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hx2 : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hlt : 1 / x < 1 := (div_lt_one hx0).2 hx
  have hpos : (0 : ℝ) < 1 / x := by positivity
  have hne1 : (1 : ℝ) / x ≠ 1 := ne_of_lt hlt
  have hne2 : (1 : ℝ) / x ≠ -1 := by
    intro h; rw [h] at hpos; linarith
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x ^ 2)) x := by
    simpa [one_div] using hasDerivAt_inv hx0.ne'
  have hcomp := (Real.hasDerivAt_arcsin hne2 hne1).comp x hinv
  have hsqrt : Real.sqrt (1 - (1 / x) ^ 2) = Real.sqrt (x ^ 2 - 1) / x := by
    have hEq : (1 : ℝ) - (1 / x) ^ 2 = (Real.sqrt (x ^ 2 - 1) / x) ^ 2 := by
      rw [div_pow (Real.sqrt (x ^ 2 - 1)) x, Real.sq_sqrt hx2.le]
      field_simp
    rw [hEq, Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hx0.le)]
  have hsne : Real.sqrt (x ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.2 hx2).ne'
  have hval : 1 / Real.sqrt (1 - (1 / x) ^ 2) * -(1 / x ^ 2)
      = -radialLeakageDensity x := by
    rw [hsqrt]
    unfold radialLeakageDensity
    field_simp
  have hneg := hcomp.neg
  rw [hval, neg_neg] at hneg
  simpa [Function.comp_def] using hneg

/-- **The arcsine tail law for the radial leakage density.**  For every `a ≥ 1`,
`∫_a^∞ dx/(x√(x² − 1)) = arcsin(1/a)`.  The antiderivative `−arcsin(1/x)` is continuous at the
endpoint and tends to `0` at infinity, so the improper integral converges to the endpoint
value. -/
theorem integral_Ioi_radialLeakageDensity {a : ℝ} (ha : 1 ≤ a) :
    ∫ x in Ioi a, radialLeakageDensity x = Real.arcsin (1 / a) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  set g : ℝ → ℝ := fun y => -Real.arcsin (1 / y) with hg
  have hderiv : ∀ x ∈ Ioi a, HasDerivAt g (radialLeakageDensity x) x := by
    intro x hx
    exact hasDerivAt_neg_arcsin_one_div (lt_of_le_of_lt ha hx)
  have hcont : ContinuousWithinAt g (Ici a) a := by
    refine ContinuousAt.continuousWithinAt ?_
    exact (Real.continuous_arcsin.continuousAt.comp
      (continuousAt_const.div continuousAt_id ha0.ne')).neg
  have hlim : Tendsto g atTop (nhds 0) := by
    have h1 : Tendsto (fun y : ℝ => 1 / y) atTop (nhds 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
    have h2 : Tendsto (fun y : ℝ => Real.arcsin (1 / y)) atTop (nhds 0) := by
      have h := (Real.continuous_arcsin.tendsto (0 : ℝ)).comp h1
      simpa [Function.comp_def, Real.arcsin_zero] using h
    simpa [hg] using h2.neg
  have hnonneg : ∀ x ∈ Ioi a, 0 ≤ radialLeakageDensity x := by
    intro x hx
    exact radialLeakageDensity_nonneg (le_of_lt (lt_trans ha0 hx))
  have hint : IntegrableOn radialLeakageDensity (Ioi a) volume :=
    integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg hlim
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  simpa [hg] using hres

/-- **Total mass of the limiting radial leakage density.**  The `a = 1` case of the arcsine tail
law. -/
theorem integral_Ioi_one_radialLeakageDensity :
    ∫ x in Ioi (1 : ℝ), radialLeakageDensity x = Real.pi / 2 := by
  rw [integral_Ioi_radialLeakageDensity (le_refl 1)]
  norm_num [Real.arcsin_one]

/-- **The exact total mass `4/11` of the limiting radial leakage measure `ν∞`.**  This upgrades
the lower bound `constrainedProlateArchConstant_ge_four_div_eleven` to an identity for the
measure itself: the density integrates to exactly one half of the constrained `8/11` leakage
fraction. -/
theorem radialLeakageMeasure_total_mass :
    (8 / (11 * Real.pi)) * ∫ x in Ioi (1 : ℝ), radialLeakageDensity x = 4 / 11 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [integral_Ioi_one_radialLeakageDensity]
  field_simp
  ring

/-- **The radial dilation Gram diagonal as a measure slice.**  For every dilation `k ≥ 1`, the
`k`-th diagonal entry of the limiting radial Gram matrix is the `k`-tail of `ν∞` scaled by
`1/k`. -/
theorem radialGramDiagonal_eq_measure_slice {k : ℝ} (hk : 1 ≤ k) :
    (8 / (11 * Real.pi)) * ((1 / k) * ∫ x in Ioi k, radialLeakageDensity x)
      = 8 / (11 * Real.pi * k) * Real.arcsin (1 / k) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le one_pos hk
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [integral_Ioi_radialLeakageDensity hk]
  field_simp

/-- **Identification of the arcsine spectrum with the leakage tails.**  Every summand of the
universal archimedean coefficient is the `1/k`-scaled `k`-tail of the limiting radial leakage
density, with paper index `k = n + 1`. -/
theorem constrainedProlateArchSeriesTerm_eq_measure_slice (n : ℕ) :
    GaloisForLFunctions.constrainedProlateArchSeriesTerm n
      = (1 / ((n : ℝ) + 1)) * ∫ x in Ioi ((n : ℝ) + 1), radialLeakageDensity x := by
  have hk : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [integral_Ioi_radialLeakageDensity hk]
  unfold GaloisForLFunctions.constrainedProlateArchSeriesTerm
  ring

/-- **The limiting radial leakage density is integrable on every tail.**  The antiderivative
`-arcsin(1/x)` is monotone with a finite limit at infinity, so the improper integral at the
inverse square-root endpoint singularity is genuine. -/
theorem integrableOn_Ioi_radialLeakageDensity {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn radialLeakageDensity (Ioi a) volume := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hderiv : ∀ x ∈ Ioi a, HasDerivAt (fun y => -Real.arcsin (1 / y))
      (radialLeakageDensity x) x := fun x hx =>
    hasDerivAt_neg_arcsin_one_div (lt_of_le_of_lt ha hx)
  have hcont : ContinuousWithinAt (fun y => -Real.arcsin (1 / y)) (Ici a) a :=
    ContinuousAt.continuousWithinAt
      ((Real.continuous_arcsin.continuousAt.comp
        (continuousAt_const.div continuousAt_id ha0.ne')).neg)
  have hlim : Tendsto (fun y => -Real.arcsin (1 / y)) atTop (nhds 0) := by
    have h1 : Tendsto (fun y : ℝ => 1 / y) atTop (nhds 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
    have h2 : Tendsto (fun y : ℝ => Real.arcsin (1 / y)) atTop (nhds 0) := by
      have h := (Real.continuous_arcsin.tendsto (0 : ℝ)).comp h1
      simpa [Function.comp_def, Real.arcsin_zero] using h
    simpa using h2.neg
  exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv
    (fun x hx => radialLeakageDensity_nonneg (le_of_lt (lt_trans ha0 hx))) hlim

end RHTower
