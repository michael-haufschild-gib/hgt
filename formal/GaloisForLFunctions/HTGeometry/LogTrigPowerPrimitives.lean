import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Primitives of `x^(c-1) cos(b log x)` and `x^(c-1) sin(b log x)`

For `x > 0` the two elementary oscillatory power integrands

`x^(c-1) cos(b log x)`,  `x^(c-1) sin(b log x)`

have closed-form primitives

`x^c (c cos(b log x) + b sin(b log x)) / (c^2 + b^2)`,
`x^c (c sin(b log x) - b cos(b log x)) / (c^2 + b^2)`,

valid whenever `c^2 + b^2 ≠ 0`.  Iterating once more raises the exponent by one and produces the
second primitives

`x^(c+1) ((c^2 + c - b^2) cos + (2c+1) b sin) / ((c^2+b^2)((c+1)^2+b^2))`,
`x^(c+1) ((c^2 + c - b^2) sin - (2c+1) b cos) / ((c^2+b^2)((c+1)^2+b^2))`.

Both levels are recorded as `HasDerivAt` statements and as evaluated interval integrals on
segments of the positive ray.
-/

open Real intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- The primitive of `x^(c-1) cos(b log x)`. -/
noncomputable def cosLogPrimitive (c b x : ℝ) : ℝ :=
  x ^ c * (c * Real.cos (b * Real.log x) + b * Real.sin (b * Real.log x)) / (c ^ 2 + b ^ 2)

/-- The primitive of `x^(c-1) sin(b log x)`. -/
noncomputable def sinLogPrimitive (c b x : ℝ) : ℝ :=
  x ^ c * (c * Real.sin (b * Real.log x) - b * Real.cos (b * Real.log x)) / (c ^ 2 + b ^ 2)

/-- The primitive of `cosLogPrimitive c b`. -/
noncomputable def cosLogSecondPrimitive (c b x : ℝ) : ℝ :=
  x ^ (c + 1) * ((c ^ 2 + c - b ^ 2) * Real.cos (b * Real.log x)
      + (2 * c + 1) * b * Real.sin (b * Real.log x))
    / ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2))

/-- The primitive of `sinLogPrimitive c b`. -/
noncomputable def sinLogSecondPrimitive (c b x : ℝ) : ℝ :=
  x ^ (c + 1) * ((c ^ 2 + c - b ^ 2) * Real.sin (b * Real.log x)
      - (2 * c + 1) * b * Real.cos (b * Real.log x))
    / ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2))

theorem hasDerivAt_mul_log {b x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => b * Real.log t) (b / x) x := by
  have h := (Real.hasDerivAt_log hx.ne').const_mul b
  rw [div_eq_mul_inv]
  exact h

theorem hasDerivAt_cos_mul_log {b x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.cos (b * Real.log t))
      (-Real.sin (b * Real.log x) * (b / x)) x := by
  exact (Real.hasDerivAt_cos (b * Real.log x)).comp x (hasDerivAt_mul_log hx)

theorem hasDerivAt_sin_mul_log {b x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.sin (b * Real.log t))
      (Real.cos (b * Real.log x) * (b / x)) x := by
  exact (Real.hasDerivAt_sin (b * Real.log x)).comp x (hasDerivAt_mul_log hx)

/-- `d/dx [x^c (c cos(b log x) + b sin(b log x))/(c²+b²)] = x^(c-1) cos(b log x)`. -/
theorem hasDerivAt_cosLogPrimitive {c b x : ℝ} (hx : 0 < x) (h : c ^ 2 + b ^ 2 ≠ 0) :
    HasDerivAt (cosLogPrimitive c b) (x ^ (c - 1) * Real.cos (b * Real.log x)) x := by
  have hxne : x ≠ 0 := hx.ne'
  have hrpow : HasDerivAt (fun t : ℝ => t ^ c) (c * x ^ (c - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hxne)
  have hc := hasDerivAt_cos_mul_log (b := b) hx
  have hs := hasDerivAt_sin_mul_log (b := b) hx
  have hnum : HasDerivAt
      (fun t : ℝ => t ^ c * (c * Real.cos (b * Real.log t) + b * Real.sin (b * Real.log t)))
      ((c * x ^ (c - 1)) * (c * Real.cos (b * Real.log x) + b * Real.sin (b * Real.log x)) +
        x ^ c * (c * (-Real.sin (b * Real.log x) * (b / x)) +
          b * (Real.cos (b * Real.log x) * (b / x)))) x :=
    hrpow.mul ((hc.const_mul c).add (hs.const_mul b))
  refine (hnum.div_const (c ^ 2 + b ^ 2)).congr_deriv ?_
  have hxc : x ^ c = x ^ (c - 1) * x := by
    rw [← Real.rpow_add_one hxne (c - 1)]
    ring_nf
  rw [hxc]
  field_simp
  ring

/-- `d/dx [x^c (c sin(b log x) - b cos(b log x))/(c²+b²)] = x^(c-1) sin(b log x)`. -/
theorem hasDerivAt_sinLogPrimitive {c b x : ℝ} (hx : 0 < x) (h : c ^ 2 + b ^ 2 ≠ 0) :
    HasDerivAt (sinLogPrimitive c b) (x ^ (c - 1) * Real.sin (b * Real.log x)) x := by
  have hxne : x ≠ 0 := hx.ne'
  have hrpow : HasDerivAt (fun t : ℝ => t ^ c) (c * x ^ (c - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hxne)
  have hc := hasDerivAt_cos_mul_log (b := b) hx
  have hs := hasDerivAt_sin_mul_log (b := b) hx
  have hnum : HasDerivAt
      (fun t : ℝ => t ^ c * (c * Real.sin (b * Real.log t) - b * Real.cos (b * Real.log t)))
      ((c * x ^ (c - 1)) * (c * Real.sin (b * Real.log x) - b * Real.cos (b * Real.log x)) +
        x ^ c * (c * (Real.cos (b * Real.log x) * (b / x)) -
          b * (-Real.sin (b * Real.log x) * (b / x)))) x :=
    hrpow.mul ((hs.const_mul c).sub (hc.const_mul b))
  refine (hnum.div_const (c ^ 2 + b ^ 2)).congr_deriv ?_
  have hxc : x ^ c = x ^ (c - 1) * x := by
    rw [← Real.rpow_add_one hxne (c - 1)]
    ring_nf
  rw [hxc]
  field_simp
  ring

/-- The second primitive differentiates back to `cosLogPrimitive`. -/
theorem hasDerivAt_cosLogSecondPrimitive {c b x : ℝ} (hx : 0 < x)
    (h : c ^ 2 + b ^ 2 ≠ 0) (h' : (c + 1) ^ 2 + b ^ 2 ≠ 0) :
    HasDerivAt (cosLogSecondPrimitive c b) (cosLogPrimitive c b x) x := by
  have hxne : x ≠ 0 := hx.ne'
  have hrpow : HasDerivAt (fun t : ℝ => t ^ (c + 1)) ((c + 1) * x ^ (c + 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hxne)
  have hc := hasDerivAt_cos_mul_log (b := b) hx
  have hs := hasDerivAt_sin_mul_log (b := b) hx
  have hnum : HasDerivAt
      (fun t : ℝ => t ^ (c + 1) * ((c ^ 2 + c - b ^ 2) * Real.cos (b * Real.log t)
        + (2 * c + 1) * b * Real.sin (b * Real.log t)))
      (((c + 1) * x ^ (c + 1 - 1)) * ((c ^ 2 + c - b ^ 2) * Real.cos (b * Real.log x)
          + (2 * c + 1) * b * Real.sin (b * Real.log x)) +
        x ^ (c + 1) * ((c ^ 2 + c - b ^ 2) * (-Real.sin (b * Real.log x) * (b / x)) +
          (2 * c + 1) * b * (Real.cos (b * Real.log x) * (b / x)))) x :=
    hrpow.mul ((hc.const_mul _).add (hs.const_mul _))
  refine (hnum.div_const ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2))).congr_deriv ?_
  have hxc : x ^ (c + 1) = x ^ c * x := by
    rw [← Real.rpow_add_one hxne c]
  have hxc' : x ^ (c + 1 - 1) = x ^ c := by norm_num
  rw [cosLogPrimitive, hxc', hxc]
  field_simp
  ring

/-- The second primitive differentiates back to `sinLogPrimitive`. -/
theorem hasDerivAt_sinLogSecondPrimitive {c b x : ℝ} (hx : 0 < x)
    (h : c ^ 2 + b ^ 2 ≠ 0) (h' : (c + 1) ^ 2 + b ^ 2 ≠ 0) :
    HasDerivAt (sinLogSecondPrimitive c b) (sinLogPrimitive c b x) x := by
  have hxne : x ≠ 0 := hx.ne'
  have hrpow : HasDerivAt (fun t : ℝ => t ^ (c + 1)) ((c + 1) * x ^ (c + 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hxne)
  have hc := hasDerivAt_cos_mul_log (b := b) hx
  have hs := hasDerivAt_sin_mul_log (b := b) hx
  have hnum : HasDerivAt
      (fun t : ℝ => t ^ (c + 1) * ((c ^ 2 + c - b ^ 2) * Real.sin (b * Real.log t)
        - (2 * c + 1) * b * Real.cos (b * Real.log t)))
      (((c + 1) * x ^ (c + 1 - 1)) * ((c ^ 2 + c - b ^ 2) * Real.sin (b * Real.log x)
          - (2 * c + 1) * b * Real.cos (b * Real.log x)) +
        x ^ (c + 1) * ((c ^ 2 + c - b ^ 2) * (Real.cos (b * Real.log x) * (b / x)) -
          (2 * c + 1) * b * (-Real.sin (b * Real.log x) * (b / x)))) x :=
    hrpow.mul ((hs.const_mul _).sub (hc.const_mul _))
  refine (hnum.div_const ((c ^ 2 + b ^ 2) * ((c + 1) ^ 2 + b ^ 2))).congr_deriv ?_
  have hxc : x ^ (c + 1) = x ^ c * x := by
    rw [← Real.rpow_add_one hxne c]
  have hxc' : x ^ (c + 1 - 1) = x ^ c := by norm_num
  rw [sinLogPrimitive, hxc', hxc]
  field_simp
  ring

/-! ## Interval integrals on the positive ray -/

theorem continuousOn_rpow_mul_cos_log (c b : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ c * Real.cos (b * Real.log x)) (Set.Ioi 0) := by
  refine ContinuousOn.mul (ContinuousOn.rpow_const continuousOn_id ?_) ?_
  · intro x hx
    exact Or.inl (ne_of_gt hx)
  · exact Real.continuous_cos.comp_continuousOn
      (continuousOn_const.mul (Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)))

theorem continuousOn_rpow_mul_sin_log (c b : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ c * Real.sin (b * Real.log x)) (Set.Ioi 0) := by
  refine ContinuousOn.mul (ContinuousOn.rpow_const continuousOn_id ?_) ?_
  · intro x hx
    exact Or.inl (ne_of_gt hx)
  · exact Real.continuous_sin.comp_continuousOn
      (continuousOn_const.mul (Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)))

theorem uIcc_subset_Ioi {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : Set.uIcc u v ⊆ Set.Ioi 0 := by
  intro x hx
  exact lt_of_lt_of_le (lt_min hu hv) hx.1

theorem intervalIntegrable_rpow_mul_cos_log {c b u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (fun x : ℝ => x ^ c * Real.cos (b * Real.log x)) MeasureTheory.volume u v :=
  ((continuousOn_rpow_mul_cos_log c b).mono (uIcc_subset_Ioi hu hv)).intervalIntegrable

theorem intervalIntegrable_rpow_mul_sin_log {c b u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (fun x : ℝ => x ^ c * Real.sin (b * Real.log x)) MeasureTheory.volume u v :=
  ((continuousOn_rpow_mul_sin_log c b).mono (uIcc_subset_Ioi hu hv)).intervalIntegrable

/-- The evaluated cosine integral on a segment of the positive ray. -/
theorem integral_rpow_mul_cos_log {c b u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : c ^ 2 + b ^ 2 ≠ 0) :
    (∫ x in u..v, x ^ (c - 1) * Real.cos (b * Real.log x))
      = cosLogPrimitive c b v - cosLogPrimitive c b u :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun _ hx => hasDerivAt_cosLogPrimitive (uIcc_subset_Ioi hu hv hx) h)
    (intervalIntegrable_rpow_mul_cos_log hu hv)

/-- The evaluated sine integral on a segment of the positive ray. -/
theorem integral_rpow_mul_sin_log {c b u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : c ^ 2 + b ^ 2 ≠ 0) :
    (∫ x in u..v, x ^ (c - 1) * Real.sin (b * Real.log x))
      = sinLogPrimitive c b v - sinLogPrimitive c b u :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun _ hx => hasDerivAt_sinLogPrimitive (uIcc_subset_Ioi hu hv hx) h)
    (intervalIntegrable_rpow_mul_sin_log hu hv)

/-! ## The second level: integrating the primitives themselves -/

theorem continuousOn_cosLogPrimitive (c b : ℝ) :
    ContinuousOn (cosLogPrimitive c b) (Set.Ioi 0) := by
  have h : ContinuousOn (fun x : ℝ =>
      (c * (x ^ c * Real.cos (b * Real.log x)) + b * (x ^ c * Real.sin (b * Real.log x)))
        / (c ^ 2 + b ^ 2)) (Set.Ioi 0) :=
    (((continuousOn_rpow_mul_cos_log c b).const_smul c).add
      ((continuousOn_rpow_mul_sin_log c b).const_smul b)).div_const _
  refine h.congr fun x _ => ?_
  rw [cosLogPrimitive]
  ring

theorem continuousOn_sinLogPrimitive (c b : ℝ) :
    ContinuousOn (sinLogPrimitive c b) (Set.Ioi 0) := by
  have h : ContinuousOn (fun x : ℝ =>
      (c * (x ^ c * Real.sin (b * Real.log x)) - b * (x ^ c * Real.cos (b * Real.log x)))
        / (c ^ 2 + b ^ 2)) (Set.Ioi 0) :=
    (((continuousOn_rpow_mul_sin_log c b).const_smul c).sub
      ((continuousOn_rpow_mul_cos_log c b).const_smul b)).div_const _
  refine h.congr fun x _ => ?_
  rw [sinLogPrimitive]
  ring

/-- The evaluated integral of `cosLogPrimitive` on a segment of the positive ray. -/
theorem integral_cosLogPrimitive {c b u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : c ^ 2 + b ^ 2 ≠ 0) (h' : (c + 1) ^ 2 + b ^ 2 ≠ 0) :
    (∫ x in u..v, cosLogPrimitive c b x)
      = cosLogSecondPrimitive c b v - cosLogSecondPrimitive c b u :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun _ hx => hasDerivAt_cosLogSecondPrimitive (uIcc_subset_Ioi hu hv hx) h h')
    (((continuousOn_cosLogPrimitive c b).mono (uIcc_subset_Ioi hu hv)).intervalIntegrable)

/-- The evaluated integral of `sinLogPrimitive` on a segment of the positive ray. -/
theorem integral_sinLogPrimitive {c b u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : c ^ 2 + b ^ 2 ≠ 0) (h' : (c + 1) ^ 2 + b ^ 2 ≠ 0) :
    (∫ x in u..v, sinLogPrimitive c b x)
      = sinLogSecondPrimitive c b v - sinLogSecondPrimitive c b u :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun _ hx => hasDerivAt_sinLogSecondPrimitive (uIcc_subset_Ioi hu hv hx) h h')
    (((continuousOn_sinLogPrimitive c b).mono (uIcc_subset_Ioi hu hv)).intervalIntegrable)

end GaloisForLFunctions.HTGeometry
