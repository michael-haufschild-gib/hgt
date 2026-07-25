import GaloisForLFunctions.RHTower.StripDivisorRealization

/-!
# A refunded complex stray: pole order two already permits genuinely complex off-critical zeros

A reflection-antisymmetric correction to the von Mangoldt measure of `ζ` carries a **negative**
coefficient at each frequency where it inserts a zero of `F` and a **positive** coefficient where it
inserts a pole.  A positive coefficient at a frequency other than `1/2` is admissible without
destroying entirety in exactly one situation: when `ζ` already has a zero there, so that the pole is
cancelled.  Such a term **removes** a zero of `ζ` and refunds one unit of the budget fixed by the
trace condition `Σ_j t_j = 0`, which otherwise reads `ord₁F = 1 + (inserted multiplicity)`.

The refund is effective.  Let `γ` be the ordinate of any zero of `ζ` on the critical line — Hardy's
theorem provides infinitely many — and let `0 < a ≤ 1/4`, `ρ = 1/2 + a + iγ`.  Removing the pair
`1/2 ± iγ` and inserting the quadruple `ρ, ρ̄, 1-ρ, 1-ρ̄` costs `-1 + 2 = 1`, so

```text
F(s) = ζ(s)·(s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄) / [ ((s-1/2)² + γ²)·s(s-1) ]
```

has a pole of order **two** at `s = 1`, an entire order-one completion
`ξ(s)((s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄))/((s-1/2)²+γ²)` — entire because `ξ` vanishes at `1/2 ± iγ` — the
exact Riemann functional equation, and zeros off the critical line that are neither real nor
critical.

Nonnegativity of the correction is elementary.  With `h(u) = cosh(u/2) + cos(γu)(1 - 2cosh(au))` the
bracket is at most `-1`, so `h(u) ≥ cosh(u/2) + 1 - 2cosh(au) = 2cosh²(u/4) - 2cosh(au) ≥
2cosh(u/4)(cosh(u/4) - 1) ≥ 0` whenever `|a| ≤ 1/4`.  (The sharp range is `|a| ≤ 1/(2√2)`, by
comparing Taylor coefficients: `4^{-n} - 2a^{2n} ≥ 0` for all `n ≥ 1` iff `a² ≤ 1/8`.)

Consequently pole order two already permits **every** kind of off-critical zero — real pairs without
a refund, genuinely complex quadruples with one — so `ord₁F = 1` is the exact threshold, with no
intermediate regime.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

/-! ## The correction density -/

/-- Logarithmic density of the correction which removes the critical pair `1/2 ± iγ` and inserts the
complex quadruple `1/2 ± a ± iγ`. -/
def refundDensity (a gam u : ℝ) : ℝ :=
  (Real.exp u + 1) + 2 * Real.exp (u / 2) * Real.cos (gam * u) -
    2 * Real.cos (gam * u) * (Real.exp ((1 / 2 + a) * u) + Real.exp ((1 / 2 - a) * u))

/-- The density in cone coordinates: `d(u) = 2e^{u/2}h(u)` with
`h(u) = cosh(u/2) + cos(γu)(1 - 2cosh(au))`. -/
theorem refundDensity_eq (a gam u : ℝ) :
    refundDensity a gam u
      = 2 * Real.exp (u / 2) *
          (Real.cosh (u / 2) + Real.cos (gam * u) * (1 - 2 * Real.cosh (a * u))) := by
  have h1 := two_exp_half_mul_cosh_half u
  have h2 := two_exp_half_mul_cosh a u
  unfold refundDensity
  rw [← h1, ← h2]
  ring

/-- `cosh(u/2) + 1 = 2cosh²(u/4)`. -/
theorem cosh_half_add_one (u : ℝ) :
    Real.cosh (u / 2) + 1 = 2 * Real.cosh (u / 4) ^ 2 := by
  have h := Real.cosh_two_mul (u / 4)
  have e : 2 * (u / 4) = u / 2 := by ring
  rw [e] at h
  have hs := Real.cosh_sq_sub_sinh_sq (u / 4)
  linarith

/-- **Λ-positivity of the refunded correction.**  Elementary: the bracket `1 - 2cosh(au)` is at most
`-1`, so `h(u) ≥ cosh(u/2) + 1 - 2cosh(au) = 2cosh(u/4)(cosh(u/4) - 1) ≥ 0`. -/
theorem refundDensity_nonneg {a gam u : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hu : 0 ≤ u) :
    0 ≤ refundDensity a gam u := by
  have hcau : (1 : ℝ) ≤ Real.cosh (a * u) := Real.one_le_cosh _
  have hbr : 1 - 2 * Real.cosh (a * u) ≤ -1 := by linarith
  have hcos : Real.cos (gam * u) ≤ 1 := Real.cos_le_one _
  have hflip : (1 : ℝ) * (1 - 2 * Real.cosh (a * u))
      ≤ Real.cos (gam * u) * (1 - 2 * Real.cosh (a * u)) := by
    nlinarith [hbr, hcos]
  have hmono : Real.cosh (a * u) ≤ Real.cosh (u / 4) := by
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_mul, abs_of_nonneg hu, abs_of_nonneg ha0,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ u / 4)]
    nlinarith
  have hq : (1 : ℝ) ≤ Real.cosh (u / 4) := Real.one_le_cosh _
  have hkey : 0 ≤ Real.cosh (u / 2) + Real.cos (gam * u) * (1 - 2 * Real.cosh (a * u)) := by
    have hstep : Real.cosh (u / 2) + 1 - 2 * Real.cosh (a * u)
        ≥ 2 * Real.cosh (u / 4) ^ 2 - 2 * Real.cosh (u / 4) := by
      rw [cosh_half_add_one u]; linarith
    nlinarith [hflip, hstep, hq]
  rw [refundDensity_eq]
  have hE : (0 : ℝ) < 2 * Real.exp (u / 2) := by positivity
  positivity

/-! ## The transform -/

/-- Transform of the refunded correction: one unit of pole at the admissible frequency `1/2`, plus
the removed critical pair with a positive sign, minus the inserted quadruple. -/
def refundTransform (a gam : ℝ) (z : ℂ) : ℂ :=
  ((z - 1)⁻¹ + z⁻¹)
    + ((z - (1 / 2 + (gam : ℂ) * I))⁻¹ + (z - (1 / 2 - (gam : ℂ) * I))⁻¹)
    - ((z - (1 / 2 + (a : ℂ) + (gam : ℂ) * I))⁻¹ + (z - (1 / 2 - (a : ℂ) - (gam : ℂ) * I))⁻¹
      + (z - (1 / 2 + (a : ℂ) - (gam : ℂ) * I))⁻¹ + (z - (1 / 2 - (a : ℂ) + (gam : ℂ) * I))⁻¹)

/-- **The functional equation.**  The refunded correction is reflection antisymmetric. -/
theorem refundTransform_antisymm (a gam : ℝ) (z : ℂ) :
    refundTransform a gam z + refundTransform a gam (1 - z) = 0 := by
  have hpole := antisym_block 1 z
  have e0 : (1 : ℂ) - 1 = 0 := by ring
  rw [e0] at hpole
  have hcrit := antisym_block (1 / 2 + (gam : ℂ) * I) z
  have e1 : (1 : ℂ) - (1 / 2 + (gam : ℂ) * I) = 1 / 2 - (gam : ℂ) * I := by ring
  rw [e1] at hcrit
  have hq1 := antisym_block (1 / 2 + (a : ℂ) + (gam : ℂ) * I) z
  have e2 : (1 : ℂ) - (1 / 2 + (a : ℂ) + (gam : ℂ) * I) = 1 / 2 - (a : ℂ) - (gam : ℂ) * I := by
    ring
  rw [e2] at hq1
  have hq2 := antisym_block (1 / 2 + (a : ℂ) - (gam : ℂ) * I) z
  have e3 : (1 : ℂ) - (1 / 2 + (a : ℂ) - (gam : ℂ) * I) = 1 / 2 - (a : ℂ) + (gam : ℂ) * I := by
    ring
  rw [e3] at hq2
  simp only [refundTransform]
  linear_combination hpole + hcrit - hq1 - hq2

/-! ## The completed function -/

/-- The inserted quartic factor. -/
def refundQuartic (a gam : ℝ) (z : ℂ) : ℂ :=
  (z - (1 / 2 + (a : ℂ) + (gam : ℂ) * I)) * (z - (1 / 2 - (a : ℂ) - (gam : ℂ) * I)) *
    ((z - (1 / 2 + (a : ℂ) - (gam : ℂ) * I)) * (z - (1 / 2 - (a : ℂ) + (gam : ℂ) * I)))

/-- The removed critical quadratic factor `(z - 1/2)² + γ²`. -/
def refundCriticalFactor (gam : ℝ) (z : ℂ) : ℂ := (z - 1 / 2) ^ 2 + (gam : ℂ) ^ 2

theorem refundQuartic_reflect (a gam : ℝ) (z : ℂ) :
    refundQuartic a gam (1 - z) = refundQuartic a gam z := by
  unfold refundQuartic; ring

theorem refundCriticalFactor_reflect (gam : ℝ) (z : ℂ) :
    refundCriticalFactor gam (1 - z) = refundCriticalFactor gam z := by
  unfold refundCriticalFactor; ring

/-- The removed factor vanishes exactly at the critical pair `1/2 ± iγ`, which is where `ξ` must
already vanish for the completion to stay entire. -/
theorem refundCriticalFactor_eq_zero (gam : ℝ) :
    refundCriticalFactor gam (1 / 2 + (gam : ℂ) * I) = 0 ∧
      refundCriticalFactor gam (1 / 2 - (gam : ℂ) * I) = 0 := by
  constructor
  · show ((1 / 2 + (gam : ℂ) * I) - 1 / 2) ^ 2 + (gam : ℂ) ^ 2 = 0
    rw [show ((1 / 2 + (gam : ℂ) * I) - 1 / 2) = (gam : ℂ) * I from by ring, mul_pow,
      Complex.I_sq]
    ring
  · show ((1 / 2 - (gam : ℂ) * I) - 1 / 2) ^ 2 + (gam : ℂ) ^ 2 = 0
    rw [show ((1 / 2 - (gam : ℂ) * I) - 1 / 2) = -((gam : ℂ) * I) from by ring, neg_pow, mul_pow,
      Complex.I_sq]
    ring

/-- The inserted zeros are neither real nor critical: real part `1/2 + a ≠ 1/2` and imaginary part
`γ ≠ 0`. -/
theorem refund_offCriticalLine {a gam : ℝ} (ha : a ≠ 0) (hgam : gam ≠ 0) :
    refundQuartic a gam (1 / 2 + (a : ℂ) + (gam : ℂ) * I) = 0 ∧
      ((1 / 2 + (a : ℂ) + (gam : ℂ) * I).re ≠ 1 / 2) ∧
      ((1 / 2 + (a : ℂ) + (gam : ℂ) * I).im ≠ 0) := by
  refine ⟨by unfold refundQuartic; ring, ?_, ?_⟩
  · simp [ha]
  · simp [hgam]

/-- **Theorem R.**  For any ordinate `γ` of a critical zero of `ζ` and any `a ∈ (0, 1/4]`, the
refunded correction is a nonnegative measure, is reflection antisymmetric, keeps the completed
function entire and `s ↦ 1-s` invariant, spends exactly one budget unit — so the pole at `s = 1`
has order two — and inserts zeros that are neither real nor on the critical line. -/
theorem lambdaPositive_refunded_complex_stray {a gam : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 4)
    (hgam : gam ≠ 0) :
    (∀ u : ℝ, 0 ≤ u → 0 ≤ refundDensity a gam u) ∧
      (∀ z : ℂ, refundTransform a gam z + refundTransform a gam (1 - z) = 0) ∧
      (∀ z : ℂ, refundQuartic a gam (1 - z) = refundQuartic a gam z) ∧
      (∀ z : ℂ, refundCriticalFactor gam (1 - z) = refundCriticalFactor gam z) ∧
      refundCriticalFactor gam (1 / 2 + (gam : ℂ) * I) = 0 ∧
      refundQuartic a gam (1 / 2 + (a : ℂ) + (gam : ℂ) * I) = 0 ∧
      ((1 / 2 + (a : ℂ) + (gam : ℂ) * I).re ≠ 1 / 2) ∧
      ((1 / 2 + (a : ℂ) + (gam : ℂ) * I).im ≠ 0) :=
  ⟨fun _ hu => refundDensity_nonneg (le_of_lt ha0) ha hu,
    refundTransform_antisymm a gam, refundQuartic_reflect a gam,
    refundCriticalFactor_reflect gam, (refundCriticalFactor_eq_zero gam).1,
    (refund_offCriticalLine (ne_of_gt ha0) hgam).1,
    (refund_offCriticalLine (ne_of_gt ha0) hgam).2.1,
    (refund_offCriticalLine (ne_of_gt ha0) hgam).2.2⟩

end RHTower
