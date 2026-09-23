import Mathlib
import GaloisForLFunctions.RHTower.ProlateWKBSubsolution

/-!
# The prolate tunnelling action, sharp to first order in the separation

The WKB exponent of the prolate equation on the forbidden band is

```text
c ∫_{√s}^{1} √((y² − s)/(1 − y²)) dy ,
```

`s` being the normalized separation.  The substitution `y = sin θ` removes the endpoint singularity
and turns it into `c · A(s)` with

```text
A(s) = ∫_{arcsin √s}^{π/2} √(sin²θ − s) dθ .
```

The crude bound `A(s) ≤ 1` — equivalently `exponent ≤ c` — loses exactly the factor that carries the
polynomial part of the leakage.  The first correction is *logarithmic*:

```text
0 ≤ 1 + (s/4)·log s − A(s) ≤ 3 s ,
```

so `A(s) = 1 + (s/4)·log s + O(s)`.  At a fixed mode the separation is `s ≍ 1/c`, hence `c·s` is
bounded and

```text
c A(s) = c + (cs/4)·log s + O(1) = c − ((cs)/4)·log c + O(1) ,
```

which is what converts a pure exponential clock `e^{−2c}` into `c^{(cs)/2} e^{−2c}`.

The proof splits `sin θ − √(sin²θ − s) = s/(2 sin θ) + O(s²/sin³θ)`, integrates the first term
exactly — the antiderivative of `1/sin` is `log tan(θ/2)`, and `tan(t/2) = √s/(1+√(1−s))` at the
turning angle — and controls the second by Jordan's inequality `sin θ ≥ 2θ/π`.  Every error term is
one-signed, so the estimate is one-sided as stated.
-/

noncomputable section

open Real Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions.RHTower

/-- The prolate tunnelling action in the angular variable. -/
def prolateAngleAction (s : ℝ) : ℝ :=
  ∫ θ in Real.arcsin (Real.sqrt s)..(π / 2), Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)

/-! ## The turning angle -/

section TurningAngle

variable {s : ℝ}

theorem sqrt_le_one (hs1 : s ≤ 1) : Real.sqrt s ≤ 1 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt hs1

theorem sin_arcsin_sqrt (hs1 : s ≤ 1) :
    Real.sin (Real.arcsin (Real.sqrt s)) = Real.sqrt s :=
  Real.sin_arcsin (by linarith [Real.sqrt_nonneg s]) (sqrt_le_one hs1)

theorem cos_arcsin_sqrt (hs0 : 0 ≤ s) :
    Real.cos (Real.arcsin (Real.sqrt s)) = Real.sqrt (1 - s) := by
  rw [Real.cos_arcsin, Real.sq_sqrt hs0]

theorem arcsin_sqrt_pos (hs0 : 0 < s) : 0 < Real.arcsin (Real.sqrt s) :=
  Real.arcsin_pos.2 (Real.sqrt_pos.2 hs0)

theorem arcsin_sqrt_le : Real.arcsin (Real.sqrt s) ≤ π / 2 :=
  Real.arcsin_le_pi_div_two _

/-- The turning angle is at least its sine. -/
theorem sqrt_le_arcsin_sqrt (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Real.sqrt s ≤ Real.arcsin (Real.sqrt s) := by
  have h := sin_arcsin_sqrt hs1
  have hpos := arcsin_sqrt_pos hs0
  have := Real.sin_lt hpos
  linarith [h ▸ this]

/-- Beyond the turning angle the sine dominates its turning value. -/
theorem sqrt_le_sin_of_mem (hs1 : s ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Icc (Real.arcsin (Real.sqrt s)) (π / 2)) :
    Real.sqrt s ≤ Real.sin θ := by
  have hmono := Real.strictMonoOn_sin.monotoneOn
  have hmem1 : Real.arcsin (Real.sqrt s) ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
  have hmem2 : θ ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨le_trans hmem1.1 hθ.1, hθ.2⟩
  have := hmono hmem1 hmem2 hθ.1
  rwa [sin_arcsin_sqrt hs1] at this

theorem sin_pos_of_mem (hs0 : 0 < s) (hs1 : s ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Icc (Real.arcsin (Real.sqrt s)) (π / 2)) : 0 < Real.sin θ :=
  lt_of_lt_of_le (Real.sqrt_pos.2 hs0) (sqrt_le_sin_of_mem hs1 hθ)

theorem le_sin_sq_of_mem (hs0 : 0 < s) (hs1 : s ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Icc (Real.arcsin (Real.sqrt s)) (π / 2)) : s ≤ Real.sin θ ^ (2 : ℕ) := by
  have h := sqrt_le_sin_of_mem hs1 hθ
  have hnn : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg s
  nlinarith [Real.sq_sqrt hs0.le]

end TurningAngle

/-! ## The pointwise defect of the shifted square root -/

/-- **The exact size of the square-root defect.**  For `u ≥ √s > 0` the difference
`u − √(u²−s)` is `s/(2u)` up to a relative error of order `s/u²`. -/
theorem sub_sqrt_sq_sub_bounds {s u : ℝ} (hs0 : 0 < s) (hu : Real.sqrt s ≤ u) :
    s / (2 * u) ≤ u - Real.sqrt (u ^ (2 : ℕ) - s) ∧
      u - Real.sqrt (u ^ (2 : ℕ) - s) ≤ s / (2 * u) + s ^ (2 : ℕ) / (2 * u ^ (3 : ℕ)) := by
  have hupos : 0 < u := lt_of_lt_of_le (Real.sqrt_pos.2 hs0) hu
  have hsq : s ≤ u ^ (2 : ℕ) := by nlinarith [Real.sq_sqrt hs0.le, Real.sqrt_nonneg s]
  set w := Real.sqrt (u ^ (2 : ℕ) - s) with hwdef
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw : w ^ (2 : ℕ) = u ^ (2 : ℕ) - s := Real.sq_sqrt (by linarith)
  have hwu : w ≤ u := by nlinarith
  have hkey : 2 * u ^ (3 : ℕ) * (u - w) ≤ s * u ^ (2 : ℕ) + s ^ (2 : ℕ) := by
    have hprod : 0 ≤ w * (2 * u + w) * (u - w) ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg hw0 (by linarith)) (sq_nonneg _)
    nlinarith [hprod, hw]
  constructor
  · rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg (u - w)]
  · have hsplit : s / (2 * u) + s ^ (2 : ℕ) / (2 * u ^ (3 : ℕ)) = (s * u ^ (2 : ℕ) + s ^ (2 : ℕ)) / (2 * u ^ (3 : ℕ)) := by
      field_simp
    rw [hsplit, le_div_iff₀ (by positivity)]
    nlinarith [hkey]

/-! ## The antiderivative of the cosecant -/

/-- `log ∘ tan ∘ (·/2)` differentiates to the cosecant. -/
theorem hasDerivAt_log_tan_half {θ : ℝ} (h1 : 0 < θ) (h2 : θ < π) :
    HasDerivAt (fun x => Real.log (Real.tan (x / 2))) (1 / Real.sin θ) θ := by
  have hhalf1 : 0 < θ / 2 := by linarith
  have hhalf2 : θ / 2 < π / 2 := by linarith
  have hcos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf2⟩
  have hsin : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi hhalf1 (by linarith [Real.pi_pos])
  have htan : 0 < Real.tan (θ / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    positivity
  have hd1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) θ := by
    simpa using (hasDerivAt_id θ).div_const 2
  have hd2 : HasDerivAt Real.tan (1 / Real.cos (θ / 2) ^ (2 : ℕ)) (θ / 2) :=
    Real.hasDerivAt_tan hcos.ne'
  have hd3 : HasDerivAt (fun x : ℝ => Real.tan (x / 2))
      (1 / Real.cos (θ / 2) ^ (2 : ℕ) * (1 / 2)) θ := by
    simpa [Function.comp_def] using hd2.comp θ hd1
  have hd4 := hd3.log htan.ne'
  convert hd4 using 1
  rw [Real.tan_eq_sin_div_cos]
  have hsin2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have := Real.sin_two_mul (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at this
  rw [hsin2]
  field_simp

/-- The cosecant is continuous beyond the turning angle. -/
theorem continuousOn_one_div_sin {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ContinuousOn (fun θ => 1 / Real.sin θ) (Icc (Real.arcsin (Real.sqrt s)) (π / 2)) := by
  refine ContinuousOn.div continuousOn_const (Real.continuous_sin.continuousOn) ?_
  intro θ hθ
  exact (sin_pos_of_mem hs0 hs1 hθ).ne'

/-- **The cosecant integral, in closed form.** -/
theorem integral_one_div_sin {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∫ θ in Real.arcsin (Real.sqrt s)..(π / 2), 1 / Real.sin θ)
      = -Real.log (Real.tan (Real.arcsin (Real.sqrt s) / 2)) := by
  set t := Real.arcsin (Real.sqrt s) with htdef
  have ht0 : 0 < t := arcsin_sqrt_pos hs0
  have ht1 : t ≤ π / 2 := arcsin_sqrt_le
  have hpi := Real.pi_pos
  have hderiv : ∀ θ ∈ uIcc t (π / 2),
      HasDerivAt (fun x => Real.log (Real.tan (x / 2))) (1 / Real.sin θ) θ := by
    intro θ hθ
    rw [uIcc_of_le ht1] at hθ
    exact hasDerivAt_log_tan_half (lt_of_lt_of_le ht0 hθ.1) (lt_of_le_of_lt hθ.2 (by linarith))
  have hint : IntervalIntegrable (fun θ => 1 / Real.sin θ) volume t (π / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht1]
    exact continuousOn_one_div_sin hs0 hs1
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [this]
  have : Real.tan (π / 2 / 2) = 1 := by
    rw [show π / 2 / 2 = π / 4 by ring, Real.tan_pi_div_four]
  rw [this, Real.log_one, zero_sub]

/-- The tangent of the half turning angle. -/
theorem tan_half_arcsin_sqrt {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Real.tan (Real.arcsin (Real.sqrt s) / 2)
      = Real.sqrt s / (1 + Real.sqrt (1 - s)) := by
  set t := Real.arcsin (Real.sqrt s) with htdef
  have ht0 : 0 < t := arcsin_sqrt_pos hs0
  have ht1 : t ≤ π / 2 := arcsin_sqrt_le
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos (t / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin2 : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    have := Real.sin_two_mul (t / 2)
    rwa [show 2 * (t / 2) = t by ring] at this
  have hcos2 : 1 + Real.cos t = 2 * Real.cos (t / 2) ^ (2 : ℕ) := by
    have := Real.cos_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring] at this
    linarith
  have hst : Real.sin t = Real.sqrt s := sin_arcsin_sqrt hs1
  have hct : Real.cos t = Real.sqrt (1 - s) := cos_arcsin_sqrt hs0.le
  rw [← hst, ← hct, hsin2, hcos2, Real.tan_eq_sin_div_cos]
  field_simp

/-- **The cosecant integral, expanded.** -/
theorem integral_one_div_sin_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∫ θ in Real.arcsin (Real.sqrt s)..(π / 2), 1 / Real.sin θ)
      = -(Real.log s / 2) + Real.log (1 + Real.sqrt (1 - s)) := by
  rw [integral_one_div_sin hs0 hs1, tan_half_arcsin_sqrt hs0 hs1]
  have h1 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0
  have h2 : (0 : ℝ) < 1 + Real.sqrt (1 - s) := by positivity
  rw [Real.log_div h1.ne' h2.ne', Real.log_sqrt hs0.le]
  ring


/-! ## The cubic cosecant tail -/

/-- An antiderivative of the inverse cube. -/
theorem hasDerivAt_neg_inv_two_sq {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (-1 : ℝ) / (2 * y ^ (2 : ℕ))) (1 / x ^ (3 : ℕ)) x := by
  have h : HasDerivAt (fun y : ℝ => 2 * y ^ (2 : ℕ)) (2 * (2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_mul (2 : ℝ))
  have hne : 2 * x ^ (2 : ℕ) ≠ 0 := by positivity
  have h2 : HasDerivAt (fun y : ℝ => (-1 : ℝ) / (2 * y ^ (2 : ℕ)))
      ((0 * (2 * x ^ (2 : ℕ)) - (-1) * (2 * (2 * x))) / (2 * x ^ (2 : ℕ)) ^ (2 : ℕ)) x :=
    (hasDerivAt_const x (-1 : ℝ)).div h hne
  have h3 : (0 * (2 * x ^ (2 : ℕ)) - (-1) * (2 * (2 * x))) / (2 * x ^ (2 : ℕ)) ^ (2 : ℕ) = 1 / x ^ (3 : ℕ) := by
    field_simp
    ring
  rwa [h3] at h2

/-- The inverse-cube tail over an interval inside the positive axis. -/
theorem integral_one_div_cube_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ π / 2) :
    (∫ x in t..(π / 2), 1 / x ^ (3 : ℕ)) ≤ 1 / (2 * t ^ (2 : ℕ)) := by
  have hderiv : ∀ x ∈ uIcc t (π / 2),
      HasDerivAt (fun y : ℝ => (-1 : ℝ) / (2 * y ^ (2 : ℕ))) (1 / x ^ (3 : ℕ)) x := by
    intro x hx
    rw [uIcc_of_le ht1] at hx
    exact hasDerivAt_neg_inv_two_sq (lt_of_lt_of_le ht0 hx.1).ne'
  have hint : IntervalIntegrable (fun x : ℝ => 1 / x ^ (3 : ℕ)) volume t (π / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht1]
    refine ContinuousOn.div continuousOn_const (continuousOn_pow 3) ?_
    intro x hx
    exact pow_ne_zero 3 (lt_of_lt_of_le ht0 hx.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hpi : (0 : ℝ) < π / 2 := by linarith [Real.pi_pos]
  have hp : (0 : ℝ) < 1 / (2 * (π / 2) ^ (2 : ℕ)) := by positivity
  have e1 : (-1 : ℝ) / (2 * (π / 2) ^ (2 : ℕ)) = -(1 / (2 * (π / 2) ^ (2 : ℕ))) := by ring
  have e2 : (-1 : ℝ) / (2 * t ^ (2 : ℕ)) = -(1 / (2 * t ^ (2 : ℕ))) := by ring
  rw [e1, e2]
  linarith

/-- **The cubic cosecant tail is at most `π³/(16 s)`.** -/
theorem integral_one_div_sin_cube_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∫ θ in Real.arcsin (Real.sqrt s)..(π / 2), 1 / Real.sin θ ^ (3 : ℕ))
      ≤ π ^ (3 : ℕ) / (16 * s) := by
  set t := Real.arcsin (Real.sqrt s) with htdef
  have ht0 : 0 < t := arcsin_sqrt_pos hs0
  have ht1 : t ≤ π / 2 := arcsin_sqrt_le
  have hpi := Real.pi_pos
  have hts : Real.sqrt s ≤ t := sqrt_le_arcsin_sqrt hs0 hs1
  have hint1 : IntervalIntegrable (fun θ : ℝ => 1 / Real.sin θ ^ (3 : ℕ)) volume t (π / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht1]
    refine ContinuousOn.div continuousOn_const
      ((Real.continuous_sin.continuousOn).pow 3) ?_
    intro θ hθ
    exact pow_ne_zero 3 (sin_pos_of_mem hs0 hs1 hθ).ne'
  have hint2 : IntervalIntegrable (fun θ : ℝ => (π / 2) ^ (3 : ℕ) * (1 / θ ^ (3 : ℕ))) volume t (π / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht1]
    refine ContinuousOn.mul continuousOn_const
      (ContinuousOn.div continuousOn_const (continuousOn_pow 3) ?_)
    intro θ hθ
    exact pow_ne_zero 3 (lt_of_lt_of_le ht0 hθ.1).ne'
  have hpoint : ∀ θ ∈ Icc t (π / 2),
      1 / Real.sin θ ^ (3 : ℕ) ≤ (π / 2) ^ (3 : ℕ) * (1 / θ ^ (3 : ℕ)) := by
    intro θ hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le ht0 hθ.1
    have hjor : 2 / π * θ ≤ Real.sin θ := mul_le_sin hθ0.le hθ.2
    have hjor0 : 0 < 2 / π * θ := by positivity
    have hcube : (2 / π * θ) ^ (3 : ℕ) ≤ Real.sin θ ^ (3 : ℕ) :=
      pow_le_pow_left₀ hjor0.le hjor 3
    have hsin0 : 0 < Real.sin θ ^ (3 : ℕ) := by
      have := sin_pos_of_mem hs0 hs1 hθ
      positivity
    have hstep : 1 / Real.sin θ ^ (3 : ℕ) ≤ 1 / (2 / π * θ) ^ (3 : ℕ) :=
      one_div_le_one_div_of_le (by positivity) hcube
    refine hstep.trans (le_of_eq ?_)
    field_simp
  have hmono := intervalIntegral.integral_mono_on ht1 hint1 hint2 hpoint
  have hcalc : (∫ θ in t..(π / 2), (π / 2) ^ (3 : ℕ) * (1 / θ ^ (3 : ℕ)))
      = (π / 2) ^ (3 : ℕ) * ∫ θ in t..(π / 2), 1 / θ ^ (3 : ℕ) :=
    intervalIntegral.integral_const_mul _ _
  rw [hcalc] at hmono
  have hcube := integral_one_div_cube_le ht0 ht1
  have hpos3 : (0 : ℝ) < (π / 2) ^ (3 : ℕ) := by positivity
  have hfin : (π / 2) ^ (3 : ℕ) * (∫ θ in t..(π / 2), 1 / θ ^ (3 : ℕ))
      ≤ (π / 2) ^ (3 : ℕ) * (1 / (2 * t ^ (2 : ℕ))) :=
    mul_le_mul_of_nonneg_left hcube hpos3.le
  have hst : s ≤ t ^ (2 : ℕ) := by
    have hnn : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg s
    nlinarith [Real.sq_sqrt hs0.le]
  have hlast : (π / 2) ^ (3 : ℕ) * (1 / (2 * t ^ (2 : ℕ))) ≤ π ^ (3 : ℕ) / (16 * s) := by
    have heq : (π / 2) ^ (3 : ℕ) * (1 / (2 * t ^ (2 : ℕ))) = π ^ (3 : ℕ) / (16 * t ^ (2 : ℕ)) := by
      field_simp
      ring
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hpi 3, hst]
  linarith

/-! ## Assembly -/

theorem intervalIntegrable_sqrt_sin_sq_sub (s a b : ℝ) :
    IntervalIntegrable (fun θ => Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)) volume a b :=
  (Real.continuous_sqrt.comp
    ((Real.continuous_sin.pow 2).sub continuous_const)).intervalIntegrable a b

theorem integral_sin_from_turning {s : ℝ} (hs0 : 0 < s) :
    (∫ θ in Real.arcsin (Real.sqrt s)..(π / 2), Real.sin θ) = Real.sqrt (1 - s) := by
  rw [integral_sin, Real.cos_pi_div_two, cos_arcsin_sqrt hs0.le, sub_zero]

/-- The action is the sine integral minus the square-root defect. -/
theorem prolateAngleAction_eq {s : ℝ} (hs0 : 0 < s) :
    prolateAngleAction s = Real.sqrt (1 - s)
      - ∫ θ in Real.arcsin (Real.sqrt s)..(π / 2),
          (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)) := by
  rw [intervalIntegral.integral_sub (Real.continuous_sin.intervalIntegrable _ _)
    (intervalIntegrable_sqrt_sin_sq_sub s _ _), integral_sin_from_turning hs0,
    prolateAngleAction]
  ring

theorem intervalIntegrable_defect (s : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun θ => Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)) volume a b :=
  (Real.continuous_sin.intervalIntegrable a b).sub (intervalIntegrable_sqrt_sin_sq_sub s a b)

theorem intervalIntegrable_scaled_csc {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (r : ℝ) :
    IntervalIntegrable (fun θ => r * (1 / Real.sin θ)) volume
      (Real.arcsin (Real.sqrt s)) (π / 2) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le arcsin_sqrt_le]
  exact continuousOn_const.mul (continuousOn_one_div_sin hs0 hs1)

theorem intervalIntegrable_scaled_csc_cube {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (r q : ℝ) :
    IntervalIntegrable (fun θ => r * (1 / Real.sin θ) + q * (1 / Real.sin θ ^ (3 : ℕ))) volume
      (Real.arcsin (Real.sqrt s)) (π / 2) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le arcsin_sqrt_le]
  refine (continuousOn_const.mul (continuousOn_one_div_sin hs0 hs1)).add
    (continuousOn_const.mul (ContinuousOn.div continuousOn_const
      ((Real.continuous_sin.continuousOn).pow 3) ?_))
  intro θ hθ
  exact pow_ne_zero 3 (sin_pos_of_mem hs0 hs1 hθ).ne'

/-- **The defect integral is trapped between the cosecant integral and its cubic correction.** -/
theorem defect_integral_bounds {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    s / 2 * (∫ θ in Real.arcsin (Real.sqrt s)..(π / 2), 1 / Real.sin θ)
        ≤ (∫ θ in Real.arcsin (Real.sqrt s)..(π / 2),
            (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s))) ∧
      (∫ θ in Real.arcsin (Real.sqrt s)..(π / 2),
          (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)))
        ≤ s / 2 * (∫ θ in Real.arcsin (Real.sqrt s)..(π / 2), 1 / Real.sin θ)
          + s ^ (2 : ℕ) / 2 * ∫ θ in Real.arcsin (Real.sqrt s)..(π / 2), 1 / Real.sin θ ^ (3 : ℕ) := by
  have hle : Real.arcsin (Real.sqrt s) ≤ π / 2 := arcsin_sqrt_le
  constructor
  · have hmono := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_scaled_csc hs0 hs1 (s / 2)) (intervalIntegrable_defect s _ _)
      (fun θ hθ => ?_)
    · rw [intervalIntegral.integral_const_mul] at hmono
      exact hmono
    · have hu := sqrt_le_sin_of_mem hs1 hθ
      have h := (sub_sqrt_sq_sub_bounds hs0 hu).1
      have hpos := sin_pos_of_mem hs0 hs1 hθ
      calc s / 2 * (1 / Real.sin θ) = s / (2 * Real.sin θ) := by
            field_simp
        _ ≤ Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s) := h
  · have hmono := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_defect s _ _)
      (intervalIntegrable_scaled_csc_cube hs0 hs1 (s / 2) (s ^ (2 : ℕ) / 2)) (fun θ hθ => ?_)
    · rw [intervalIntegral.integral_add (intervalIntegrable_scaled_csc hs0 hs1 (s / 2))
        (by
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hle]
          refine continuousOn_const.mul (ContinuousOn.div continuousOn_const
            ((Real.continuous_sin.continuousOn).pow 3) ?_)
          intro θ hθ
          exact pow_ne_zero 3 (sin_pos_of_mem hs0 hs1 hθ).ne'),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
      exact hmono
    · have hu := sqrt_le_sin_of_mem hs1 hθ
      have h := (sub_sqrt_sq_sub_bounds hs0 hu).2
      have hpos := sin_pos_of_mem hs0 hs1 hθ
      calc Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)
          ≤ s / (2 * Real.sin θ) + s ^ (2 : ℕ) / (2 * Real.sin θ ^ (3 : ℕ)) := h
        _ = s / 2 * (1 / Real.sin θ) + s ^ (2 : ℕ) / 2 * (1 / Real.sin θ ^ (3 : ℕ)) := by
            field_simp

/-! ## The sharp action estimate -/

/-- **The prolate tunnelling action, to first order in the separation.**  The action falls below
its unperturbed value `1` by exactly `−(s/4)·log s` up to `O(s)`, and the defect is one-signed. -/
theorem prolateAngleAction_sub_bounds {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ 1 + s / 4 * Real.log s - prolateAngleAction s ∧
      1 + s / 4 * Real.log s - prolateAngleAction s ≤ 3 * s := by
  have hpi := Real.pi_pos
  set M : ℝ := ∫ θ in Real.arcsin (Real.sqrt s)..(π / 2), 1 / Real.sin θ with hM
  set N : ℝ := ∫ θ in Real.arcsin (Real.sqrt s)..(π / 2), 1 / Real.sin θ ^ (3 : ℕ) with hN
  set D : ℝ := ∫ θ in Real.arcsin (Real.sqrt s)..(π / 2),
    (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)) with hD
  have hact : prolateAngleAction s = Real.sqrt (1 - s) - D := prolateAngleAction_eq hs0
  have hMval : M = -(Real.log s / 2) + Real.log (1 + Real.sqrt (1 - s)) :=
    integral_one_div_sin_eq hs0 hs1
  obtain ⟨hDlow, hDup⟩ := defect_integral_bounds hs0 hs1
  have hNle : N ≤ π ^ (3 : ℕ) / (16 * s) := integral_one_div_sin_cube_le hs0 hs1
  -- elementary facts about the square root
  have hr0 : (0 : ℝ) ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hr1 : Real.sqrt (1 - s) ≤ 1 := sqrt_le_one (by linarith)
  have hrs : 1 - s ≤ Real.sqrt (1 - s) := by
    have h0 : (0 : ℝ) ≤ 1 - s := by linarith
    have hstep := Real.sqrt_le_sqrt (show (1 - s) ^ (2 : ℕ) ≤ 1 - s by nlinarith)
    rwa [Real.sqrt_sq h0] at hstep
  have hlog0 : 0 ≤ Real.log (1 + Real.sqrt (1 - s)) :=
    Real.log_nonneg (by linarith)
  have hlog1 : Real.log (1 + Real.sqrt (1 - s)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + Real.sqrt (1 - s))
    linarith
  have hcube : s ^ (2 : ℕ) / 2 * N ≤ s := by
    have hbound : s ^ (2 : ℕ) / 2 * N ≤ s ^ (2 : ℕ) / 2 * (π ^ (3 : ℕ) / (16 * s)) :=
      mul_le_mul_of_nonneg_left hNle (by positivity)
    have heq : s ^ (2 : ℕ) / 2 * (π ^ (3 : ℕ) / (16 * s)) = s * (π ^ (3 : ℕ) / 32) := by
      field_simp
      ring
    have hpi3 : π ^ (3 : ℕ) / 32 ≤ 1 := by
      have h315 : π < 3.15 := Real.pi_lt_d2
      have hp : (0 : ℝ) < π := Real.pi_pos
      have hsq : π ^ (2 : ℕ) ≤ 3.15 ^ (2 : ℕ) := by nlinarith [h315, hp]
      have hcube : π ^ (3 : ℕ) ≤ 32 := by nlinarith [hsq, h315, hp]
      linarith
    calc s ^ (2 : ℕ) / 2 * N ≤ s * (π ^ (3 : ℕ) / 32) := by rw [← heq]; exact hbound
      _ ≤ s * 1 := mul_le_mul_of_nonneg_left hpi3 hs0.le
      _ = s := mul_one s
  have hMD : s / 2 * M = -(s / 4 * Real.log s) + s / 2 * Real.log (1 + Real.sqrt (1 - s)) := by
    rw [hMval]
    ring
  rw [hact]
  constructor
  · have : s / 2 * M ≤ D := hDlow
    rw [hMD] at this
    nlinarith [hlog0, hs0.le]
  · have hup : D ≤ s / 2 * M + s ^ (2 : ℕ) / 2 * N := hDup
    rw [hMD] at hup
    have hlogterm : s / 2 * Real.log (1 + Real.sqrt (1 - s)) ≤ s / 2 :=
      by nlinarith [hlog1, hs0.le]
    nlinarith [hcube, hlogterm, hrs]

/-! ## Back to the band variable -/

/-- The WKB integrand of the radial prolate equation, with the bandwidth factored out. -/
def prolateWKBProfile (s : ℝ) (y : ℝ) : ℝ := Real.sqrt ((y ^ (2 : ℕ) - s) / (1 - y ^ (2 : ℕ)))

theorem prolateWKB_eq_mul_profile {c s y : ℝ} (hc : 0 ≤ c) :
    prolateWKB c (-(s * c ^ (2 : ℕ))) y = c * prolateWKBProfile s y := by
  have key : c * Real.sqrt ((y ^ (2 : ℕ) - s) / (1 - y ^ (2 : ℕ)))
      = Real.sqrt (c ^ (2 : ℕ) * ((y ^ (2 : ℕ) - s) / (1 - y ^ (2 : ℕ)))) := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rw [prolateWKBProfile, key, prolateWKB]
  congr 1
  by_cases h : (1 : ℝ) - y ^ (2 : ℕ) = 0
  · rw [h]
    simp
  · field_simp
    ring

theorem continuousOn_prolateWKBProfile {s b : ℝ} (hs0 : 0 < s) (hb1 : b < 1) :
    ContinuousOn (prolateWKBProfile s) (Icc (Real.sqrt s) b) := by
  refine Real.continuous_sqrt.comp_continuousOn
    (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
  intro y hy
  have h0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hy0 : 0 < y := lt_of_lt_of_le h0 hy.1
  have hy1 : y < 1 := lt_of_le_of_lt hy.2 hb1
  nlinarith

/-- **The band-variable WKB integral is the angular action, up to the endpoint tail.** -/
theorem integral_prolateWKBProfile_eq {s b : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hb0 : Real.sqrt s ≤ b) (hb1 : b < 1) :
    (∫ y in Real.sqrt s..b, prolateWKBProfile s y)
      = ∫ θ in Real.arcsin (Real.sqrt s)..Real.arcsin b,
          Real.sqrt (Real.sin θ ^ (2 : ℕ) - s) := by
  have hspos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hb0' : (0 : ℝ) < b := lt_of_lt_of_le hspos hb0
  have hbm : b ≤ 1 := hb1.le
  set t := Real.arcsin (Real.sqrt s) with htdef
  set u := Real.arcsin b with hudef
  have ht0 : 0 < t := arcsin_sqrt_pos hs0
  have htu : t ≤ u := Real.monotone_arcsin hb0
  have hu2 : u < π / 2 := by
    rw [hudef]
    exact (Real.arcsin_lt_pi_div_two).2 hb1
  have hsint : Real.sin t = Real.sqrt s := sin_arcsin_sqrt hs1
  have hsinu : Real.sin u = b := Real.sin_arcsin (by linarith) hbm
  -- the image of the angular window is the band window
  have himg : Real.sin '' uIcc t u ⊆ Icc (Real.sqrt s) b := by
    rw [uIcc_of_le htu]
    rintro _ ⟨θ, hθ, rfl⟩
    have hmem1 : t ∈ Icc (-(π / 2)) (π / 2) :=
      ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
    have hmemθ : θ ∈ Icc (-(π / 2)) (π / 2) :=
      ⟨le_trans hmem1.1 hθ.1, le_trans hθ.2 hu2.le⟩
    have hmemu : u ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hmem1.1, hθ.1, hθ.2], hu2.le⟩
    have h1 := Real.strictMonoOn_sin.monotoneOn hmem1 hmemθ hθ.1
    have h2 := Real.strictMonoOn_sin.monotoneOn hmemθ hmemu hθ.2
    rw [hsint] at h1
    rw [hsinu] at h2
    exact ⟨h1, h2⟩
  have hsub := intervalIntegral.integral_deriv_smul_comp'
    (f := Real.sin) (f' := Real.cos) (g := prolateWKBProfile s)
    (fun x _ => Real.hasDerivAt_sin x) (Real.continuous_cos.continuousOn)
    ((continuousOn_prolateWKBProfile hs0 hb1).mono himg)
  rw [hsint, hsinu] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le htu] at hθ
  have hcos : 0 < Real.cos θ := by
    refine Real.cos_pos_of_mem_Ioo ⟨?_, lt_of_le_of_lt hθ.2 hu2⟩
    have : (0 : ℝ) < t := ht0
    linarith [hθ.1, Real.pi_pos]
  have hden : 1 - Real.sin θ ^ (2 : ℕ) = Real.cos θ ^ (2 : ℕ) := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  show Real.cos θ • prolateWKBProfile s (Real.sin θ) = Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)
  rw [smul_eq_mul, prolateWKBProfile, hden,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq hcos.le]
  field_simp

/-- **The sharp upper bound for the band-variable WKB integral.**  Every window inside the
forbidden band has WKB action at most the full angular action. -/
theorem integral_prolateWKB_le_angleAction {c s b : ℝ} (hc : 0 ≤ c) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hb0 : Real.sqrt s ≤ b) (hb1 : b < 1) :
    (∫ y in Real.sqrt s..b, prolateWKB c (-(s * c ^ (2 : ℕ))) y) ≤ c * prolateAngleAction s := by
  have hspos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  set t := Real.arcsin (Real.sqrt s) with htdef
  set u := Real.arcsin b with hudef
  have htu : t ≤ u := Real.monotone_arcsin hb0
  have hu2 : u ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hrw : (∫ y in Real.sqrt s..b, prolateWKB c (-(s * c ^ (2 : ℕ))) y)
      = c * ∫ y in Real.sqrt s..b, prolateWKBProfile s y := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun y _ => prolateWKB_eq_mul_profile hc
  rw [hrw, integral_prolateWKBProfile_eq hs0 hs1 hb0 hb1]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [prolateAngleAction]
  have hsplit : (∫ θ in t..(π / 2), Real.sqrt (Real.sin θ ^ (2 : ℕ) - s))
      = (∫ θ in t..u, Real.sqrt (Real.sin θ ^ (2 : ℕ) - s))
        + ∫ θ in u..(π / 2), Real.sqrt (Real.sin θ ^ (2 : ℕ) - s) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sqrt_sin_sq_sub s t u)
      (intervalIntegrable_sqrt_sin_sq_sub s u (π / 2))).symm
  have htail : 0 ≤ ∫ θ in u..(π / 2), Real.sqrt (Real.sin θ ^ (2 : ℕ) - s) :=
    intervalIntegral.integral_nonneg hu2 fun _ _ => Real.sqrt_nonneg _
  linarith [hsplit, htail]

/-! ## The sharp endpoint bound -/

section Endpoint

open _root_.RHTower

/-- **The sharp outer-band endpoint bound.**  From the turning point to any point of the forbidden
band a positive solution loses at most the factor `exp(−c·A(s))`. -/
theorem exp_neg_angleAction_le_endpoint {c s b : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hc : 0 ≤ c) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hab : Real.sqrt s ≤ b) (hb : b < 1)
    (hpos : ∀ y ∈ Icc (Real.sqrt s) b, 0 < Φ y)
    (hQ : ∀ y ∈ Icc (Real.sqrt s) b, 0 < -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ))
    (houter : ∀ y ∈ Icc (Real.sqrt s) b, c ^ (2 : ℕ) * (1 - 2 * y ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hinit : prolateLogDeriv Φ b ≤ prolateWKB c (-(s * c ^ (2 : ℕ))) b) :
    Φ (Real.sqrt s) * Real.exp (-(c * prolateAngleAction s)) ≤ Φ b := by
  have hs : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hmain := le_endpoint_prolateWKB hsm heig hab hs (by linarith) hb hpos hQ houter hinit
  have hbound := integral_prolateWKB_le_angleAction hc hs0 hs1 hab hb
  have hexp : Real.exp (-(c * prolateAngleAction s))
      ≤ Real.exp (-∫ t in Real.sqrt s..b, prolateWKB c (-(s * c ^ (2 : ℕ))) t) :=
    Real.exp_le_exp.mpr (by linarith)
  have hΦa : 0 < Φ (Real.sqrt s) := hpos _ (left_mem_Icc.mpr hab)
  calc Φ (Real.sqrt s) * Real.exp (-(c * prolateAngleAction s))
      ≤ Φ (Real.sqrt s) * Real.exp (-∫ t in Real.sqrt s..b, prolateWKB c (-(s * c ^ (2 : ℕ))) t) :=
        mul_le_mul_of_nonneg_left hexp hΦa.le
    _ ≤ Φ b := hmain

/-- **The sharp endpoint bound, explicitly.**  The crude clock `exp(−c)` is improved by the factor
`s^(−cs/4)`; for a fixed mode, where `c·s` is bounded, that factor is a positive power of the
bandwidth. -/
theorem exp_neg_sharp_le_endpoint {c s b : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hc : 0 ≤ c) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hab : Real.sqrt s ≤ b) (hb : b < 1)
    (hpos : ∀ y ∈ Icc (Real.sqrt s) b, 0 < Φ y)
    (hQ : ∀ y ∈ Icc (Real.sqrt s) b, 0 < -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ))
    (houter : ∀ y ∈ Icc (Real.sqrt s) b, c ^ (2 : ℕ) * (1 - 2 * y ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hinit : prolateLogDeriv Φ b ≤ prolateWKB c (-(s * c ^ (2 : ℕ))) b) :
    Φ (Real.sqrt s) * Real.exp (-(c + c * s / 4 * Real.log s)) ≤ Φ b := by
  have hmain := exp_neg_angleAction_le_endpoint hsm heig hc hs0 hs1 hab hb hpos hQ houter hinit
  have hA := (prolateAngleAction_sub_bounds hs0 hs1).1
  have hΦa : 0 < Φ (Real.sqrt s) := hpos _ (left_mem_Icc.mpr hab)
  have hle : c * prolateAngleAction s ≤ c + c * s / 4 * Real.log s := by
    have hstep : prolateAngleAction s ≤ 1 + s / 4 * Real.log s := by linarith
    nlinarith [hstep, hc]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hΦa.le) hmain
  exact Real.exp_le_exp.mpr (by linarith)

end Endpoint

/-! ## The endpoint tail of the action -/

/-- The inverse sine is at most `π/2` times its argument, by Jordan's inequality. -/
theorem arcsin_le_pi_div_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arcsin x ≤ π / 2 * x := by
  have hpi := Real.pi_pos
  have harg0 : 0 ≤ π / 2 * x := by positivity
  have harg1 : π / 2 * x ≤ π / 2 := by nlinarith
  have hjor : 2 / π * (π / 2 * x) ≤ Real.sin (π / 2 * x) := mul_le_sin harg0 harg1
  have hsimp : 2 / π * (π / 2 * x) = x := by field_simp
  rw [hsimp] at hjor
  have hmono := Real.monotone_arcsin hjor
  rwa [Real.arcsin_sin (by linarith) harg1] at hmono

/-- **The action beyond a band point is small.**  Past `b` the angular action is at most `π/2`
times the endpoint gap. -/
theorem angleAction_tail_le {s b : ℝ} (hs0 : 0 ≤ s) (hb0 : 0 ≤ b) :
    (∫ θ in Real.arcsin b..(π / 2), Real.sqrt (Real.sin θ ^ (2 : ℕ) - s))
      ≤ π / 2 * Real.sqrt (1 - b ^ (2 : ℕ)) := by
  have hle : Real.arcsin b ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hpoint : ∀ θ ∈ Icc (Real.arcsin b) (π / 2),
      Real.sqrt (Real.sin θ ^ (2 : ℕ) - s) ≤ 1 := by
    intro θ _
    rcases le_or_gt (Real.sin θ ^ (2 : ℕ) - s) 0 with h | h
    · rw [Real.sqrt_eq_zero_of_nonpos h]
      norm_num
    · have hle1 : Real.sin θ ^ (2 : ℕ) - s ≤ 1 := by
        nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ), h]
      calc Real.sqrt (Real.sin θ ^ (2 : ℕ) - s) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle1
        _ = 1 := Real.sqrt_one
  have hmono := intervalIntegral.integral_mono_on hle
    (intervalIntegrable_sqrt_sin_sq_sub s _ _) intervalIntegrable_const hpoint
  have hconst : (∫ _θ in Real.arcsin b..(π / 2), (1 : ℝ)) = π / 2 - Real.arcsin b := by
    simp
  rw [hconst] at hmono
  have harc : π / 2 - Real.arcsin b = Real.arcsin (Real.sqrt (1 - b ^ (2 : ℕ))) := by
    rw [← Real.arccos, Real.arccos_eq_arcsin hb0]
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (1 - b ^ (2 : ℕ)) := Real.sqrt_nonneg _
  have hsq1 : Real.sqrt (1 - b ^ (2 : ℕ)) ≤ 1 := sqrt_le_one (by nlinarith)
  have hbound := arcsin_le_pi_div_two_mul hsq0 hsq1
  rw [harc] at hmono
  linarith

/-- **The band-variable WKB integral is the angular action, up to the endpoint tail.** -/
theorem sub_le_integral_prolateWKB {c s b : ℝ} (hc : 0 ≤ c) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hb0 : Real.sqrt s ≤ b) (hb1 : b < 1) :
    c * prolateAngleAction s - c * (π / 2 * Real.sqrt (1 - b ^ (2 : ℕ)))
      ≤ ∫ y in Real.sqrt s..b, prolateWKB c (-(s * c ^ (2 : ℕ))) y := by
  have hspos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hbnn : (0 : ℝ) ≤ b := le_trans hspos.le hb0
  set t := Real.arcsin (Real.sqrt s) with htdef
  set u := Real.arcsin b with hudef
  have htu : t ≤ u := Real.monotone_arcsin hb0
  have hu2 : u ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hrw : (∫ y in Real.sqrt s..b, prolateWKB c (-(s * c ^ (2 : ℕ))) y)
      = c * ∫ y in Real.sqrt s..b, prolateWKBProfile s y := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun y _ => prolateWKB_eq_mul_profile hc
  rw [hrw, integral_prolateWKBProfile_eq hs0 hs1 hb0 hb1]
  have hsplit : (∫ θ in t..(π / 2), Real.sqrt (Real.sin θ ^ (2 : ℕ) - s))
      = (∫ θ in t..u, Real.sqrt (Real.sin θ ^ (2 : ℕ) - s))
        + ∫ θ in u..(π / 2), Real.sqrt (Real.sin θ ^ (2 : ℕ) - s) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sqrt_sin_sq_sub s t u)
      (intervalIntegrable_sqrt_sin_sq_sub s u (π / 2))).symm
  have htail := angleAction_tail_le (s := s) hs0.le hbnn
  have hact : prolateAngleAction s = (∫ θ in t..u, Real.sqrt (Real.sin θ ^ (2 : ℕ) - s))
      + ∫ θ in u..(π / 2), Real.sqrt (Real.sin θ ^ (2 : ℕ) - s) := by
    rw [prolateAngleAction, ← htdef, hsplit]
  rw [hact, mul_add]
  have hmul : c * ∫ θ in u..(π / 2), Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)
      ≤ c * (π / 2 * Real.sqrt (1 - b ^ (2 : ℕ))) := mul_le_mul_of_nonneg_left htail hc
  linarith

end GaloisForLFunctions.RHTower
