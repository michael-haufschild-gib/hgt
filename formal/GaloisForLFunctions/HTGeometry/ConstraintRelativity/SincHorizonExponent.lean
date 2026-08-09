import Mathlib

/-!
# Observer ramification and the sinc horizon exponent

Sharp two-sided Taylor bounds for the sinc defect on the unit interval:

`(19/120) x² ≤ 1 − sin x / x ≤ x²/6`   for `0 < x ≤ 1`.

The upper bound is mathlib's cubic lower bound for `sin`; the lower bound needs the quintic upper
bound `sin x ≤ x − x³/6 + x⁵/120`, which mathlib does not have (its `Real.sin_bound` only gives the
weaker constant `4/100`), so it is built here from the quartic upper bound for `cos`, itself built
from mathlib's cubic lower bound for `sin` by a monotonicity argument.

Inverting the bounds shows the sinc reporter has inverse exponent exactly `1/2` and loses the sign
of its argument, entirely inside one fixed operator algebra.
-/

namespace HTGeometry.ConstraintRelativity

open Real Set

/-! ## Quartic upper bound for the cosine -/

theorem hasDerivAt_cosQuartic (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s)
      (-t + t ^ 3 / 6 + Real.sin t) t := by
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) ((2 * t ^ 1) / 2) t :=
    (hasDerivAt_pow 2 t).div_const 2
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4 / 24) ((4 * t ^ 3) / 24) t :=
    (hasDerivAt_pow 4 t).div_const 24
  have hc : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
  have hsum := (((hasDerivAt_const t (1 : ℝ)).sub h2).add h4).sub hc
  have heq : -t + t ^ 3 / 6 + Real.sin t
      = (0 - 2 * t ^ 1 / 2 + 4 * t ^ 3 / 24) - (-Real.sin t) := by ring
  rw [heq]
  exact hsum

/-- **Quartic upper bound for the cosine.**  `cos x ≤ 1 − x²/2 + x⁴/24` for `x ≥ 0`. -/
theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  set f : ℝ → ℝ := fun s => 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s with hf
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (Continuous.continuousOn (by fun_prop))
    · intro t _
      exact (hasDerivAt_cosQuartic t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hderiv : deriv f t = -t + t ^ 3 / 6 + Real.sin t :=
        (hasDerivAt_cosQuartic t).deriv
      rw [hderiv]
      have hsin : t - t ^ 3 / 6 < Real.sin t := Real.sin_gt_sub_cube ht
      linarith
  have h0 : f 0 ≤ f x := hmono (Set.self_mem_Ici) hx hx
  simp only [hf] at h0
  norm_num at h0
  linarith

/-! ## Quintic upper bound for the sine -/

theorem hasDerivAt_sinQuintic (t : ℝ) :
    HasDerivAt (fun s : ℝ => s - s ^ 3 / 6 + s ^ 5 / 120 - Real.sin s)
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) t := by
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3 / 6) ((3 * t ^ 2) / 6) t :=
    (hasDerivAt_pow 3 t).div_const 6
  have h5 : HasDerivAt (fun s : ℝ => s ^ 5 / 120) ((5 * t ^ 4) / 120) t :=
    (hasDerivAt_pow 5 t).div_const 120
  have hs : HasDerivAt Real.sin (Real.cos t) t := Real.hasDerivAt_sin t
  have hsum := (((hasDerivAt_id t).sub h3).add h5).sub hs
  have heq : 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
      = (1 - 3 * t ^ 2 / 6 + 5 * t ^ 4 / 120) - Real.cos t := by ring
  rw [heq]
  exact hsum

/-- **Quintic upper bound for the sine.**  `sin x ≤ x − x³/6 + x⁵/120` for `x ≥ 0`. -/
theorem sin_le_quintic {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  set g : ℝ → ℝ := fun s => s - s ^ 3 / 6 + s ^ 5 / 120 - Real.sin s with hg
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (Continuous.continuousOn (by fun_prop))
    · intro t _
      exact (hasDerivAt_sinQuintic t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hderiv : deriv g t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t :=
        (hasDerivAt_sinQuintic t).deriv
      rw [hderiv]
      have := cos_le_quartic (le_of_lt ht)
      linarith
  have h0 : g 0 ≤ g x := hmono (Set.self_mem_Ici) hx hx
  simp only [hg] at h0
  norm_num at h0
  linarith

/-! ## The sinc defect on the unit interval -/

/-- **Card `(5)`, upper bound.**  `1 − sin x / x ≤ x²/6`. -/
theorem one_sub_sinc_le {x : ℝ} (hx : 0 < x) : 1 - Real.sin x / x ≤ x ^ 2 / 6 := by
  have hsin : x - x ^ 3 / 6 < Real.sin x := Real.sin_gt_sub_cube hx
  have hkey : 1 - Real.sin x / x = (x - Real.sin x) / x := by field_simp
  rw [hkey, div_le_iff₀ hx]
  nlinarith [hsin]

/-- **Card `(5)`, lower bound.**  `(19/120) x² ≤ 1 − sin x / x` for `0 < x ≤ 1`. -/
theorem le_one_sub_sinc {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (19 / 120) * x ^ 2 ≤ 1 - Real.sin x / x := by
  have hquint : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := sin_le_quintic hx.le
  have hpow : x ^ 4 ≤ x ^ 2 := by
    have h2 : x ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg x]
  have hkey : 1 - Real.sin x / x = (x - Real.sin x) / x := by
    field_simp
  rw [hkey, le_div_iff₀ hx]
  nlinarith [hquint, hpow]

/-! ## Inversion: the sinc reporter has exponent one half -/

/-- **Card `(6)`, lower bound.**  `√(6y)/T ≤ |δ|`. -/
theorem sqrt_le_of_sinc {T delta : ℝ} (hT : 0 < T) (hd : 0 < T * delta) :
    Real.sqrt (6 * (1 - Real.sin (T * delta) / (T * delta))) / T ≤ |delta| := by
  have hup := one_sub_sinc_le hd
  have hsq : 6 * (1 - Real.sin (T * delta) / (T * delta)) ≤ (T * delta) ^ 2 := by
    linarith
  have hle : Real.sqrt (6 * (1 - Real.sin (T * delta) / (T * delta))) ≤ |T * delta| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  rw [div_le_iff₀ hT]
  rw [abs_mul, abs_of_pos hT] at hle
  linarith [hle]

/-- **Card `(6)`, upper bound.**  `|δ| ≤ (1/T)√(120 y/19)`. -/
theorem le_sqrt_of_sinc {T delta : ℝ} (hT : 0 < T) (hd : 0 < T * delta) (hd1 : T * delta ≤ 1) :
    |delta| ≤ Real.sqrt (120 / 19 * (1 - Real.sin (T * delta) / (T * delta))) / T := by
  have hlow := le_one_sub_sinc hd hd1
  have hsq : (T * delta) ^ 2 ≤ 120 / 19 * (1 - Real.sin (T * delta) / (T * delta)) := by
    linarith
  have hle : |T * delta| ≤ Real.sqrt (120 / 19 * (1 - Real.sin (T * delta) / (T * delta))) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  rw [le_div_iff₀ hT]
  rw [abs_mul, abs_of_pos hT] at hle
  linarith [hle]

/-- **The sinc reporter loses the sign.**  The sinc defect is even, so the inversion cannot recover
the sign of its argument. -/
theorem one_sub_sinc_even (x : ℝ) :
    1 - Real.sin (-x) / (-x) = 1 - Real.sin x / x := by
  rw [Real.sin_neg, neg_div_neg_eq]

/-! ## The observer-ramification exponent -/

open Filter Topology

/-- **The abstract exponent limit.**  If the reporter and decoder logarithms are affine in a
divergent scale with vanishing corrections, their ratio converges to the ratio of slopes. -/
theorem exponent_ratio_tendsto {ι : Type*} {l : Filter ι} (A B m beta : ℝ) (hm : 0 < m)
    (L p q : ι → ℝ) (hL : Filter.Tendsto L l Filter.atBot)
    (hp : Filter.Tendsto p l (nhds 0)) (hq : Filter.Tendsto q l (nhds 0)) :
    Filter.Tendsto (fun n => (B - beta * L n + q n) / (-(A + m * L n + p n))) l
      (nhds (beta / m)) := by
  have hinv : Filter.Tendsto (fun n => (L n)⁻¹) l (nhds 0) := hL.inv_tendsto_atBot
  have hLne : ∀ᶠ n in l, L n ≠ 0 := by
    filter_upwards [hL.eventually_lt_atBot 0] with n hn using ne_of_lt hn
  have heq : ∀ᶠ n in l, (B / L n - beta + q n / L n) / (-(A / L n + m + p n / L n))
      = (B - beta * L n + q n) / (-(A + m * L n + p n)) := by
    filter_upwards [hLne] with n hn
    have h1 : B / L n - beta + q n / L n = (B - beta * L n + q n) / L n := by
      field_simp
    have h2 : -(A / L n + m + p n / L n) = (-(A + m * L n + p n)) / L n := by
      field_simp
    rcases eq_or_ne (-(A + m * L n + p n)) 0 with hz | hz
    · rw [h1, h2, hz]
      simp
    · rw [h1, h2]
      field_simp
  refine Filter.Tendsto.congr' heq ?_
  have h1 : Filter.Tendsto (fun n => B / L n - beta + q n / L n) l (nhds (0 - beta + 0)) := by
    refine ((?_ : Filter.Tendsto (fun n => B / L n) l (nhds 0)).sub tendsto_const_nhds).add ?_
    · simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := B) (f := l)).mul hinv
    · simpa [div_eq_mul_inv] using hq.mul hinv
  have h2 : Filter.Tendsto (fun n => -(A / L n + m + p n / L n)) l (nhds (-(0 + m + 0))) := by
    refine Filter.Tendsto.neg ?_
    refine ((?_ : Filter.Tendsto (fun n => A / L n) l (nhds 0)).add tendsto_const_nhds).add ?_
    · simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := A) (f := l)).mul hinv
    · simpa [div_eq_mul_inv] using hp.mul hinv
  have hne : -(0 + m + 0) ≠ 0 := by
    simp only [add_zero, zero_add, ne_eq, neg_eq_zero]
    exact ne_of_gt hm
  have hdiv := h1.div h2 hne
  have hval : (0 - beta + 0) / (-(0 + m + 0)) = beta / m := by
    field_simp
    ring
  rwa [hval] at hdiv

/-- The logarithm of the observing scale diverges. -/
theorem tendsto_log_abs_atBot :
    Filter.Tendsto (fun t : ℝ => Real.log |t|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) Filter.atBot := by
  have habs : Filter.Tendsto (fun t : ℝ => |t|) (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact abs_pos.2 ht
  exact Real.tendsto_log_nhdsGT_zero.comp habs

/-- **Card `(1)`–`(2)`.**  For a reporter of vanishing order `m` and a decoder of blow-up order `β`,
the observed exponent is exactly `β/m`. -/
theorem observed_exponent_tendsto (a b m beta : ℝ) (hm : 0 < m) (u v : ℝ → ℝ)
    (hu : Filter.Tendsto (fun t => Real.log (1 + u t)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hv : Filter.Tendsto (fun t => Real.log (1 + v t)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) :
    Filter.Tendsto
      (fun t : ℝ => (Real.log b - beta * Real.log |t| + Real.log (1 + v t))
        / (-(Real.log a + m * Real.log |t| + Real.log (1 + u t))))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (beta / m)) :=
  exponent_ratio_tendsto (Real.log a) (Real.log b) m beta hm _ _ _ tendsto_log_abs_atBot hu hv

/-- **Card `(3)`.**  Composing the reporter with a power `r` rescales the observed exponent to
`β/(m r)`: the raw exponent is not intrinsic until normalized by the reporter ramification
order. -/
theorem observed_exponent_reporter_tendsto (a b c m beta r : ℝ)
    (hm : 0 < m) (hr : 0 < r) (u v : ℝ → ℝ)
    (hu : Filter.Tendsto (fun t => Real.log (1 + u t)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hv : Filter.Tendsto (fun t => Real.log (1 + v t)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) :
    Filter.Tendsto
      (fun t : ℝ => (Real.log b - beta * Real.log |t| + Real.log (1 + v t))
        / (-(Real.log c + r * Real.log a + (m * r) * Real.log |t| + r * Real.log (1 + u t))))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (beta / (m * r))) := by
  have hmr : 0 < m * r := mul_pos hm hr
  have hscaled : Filter.Tendsto (fun t => r * Real.log (1 + u t))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    simpa using hu.const_mul r
  have hmain := exponent_ratio_tendsto (Real.log c + r * Real.log a) (Real.log b) (m * r) beta
    hmr _ _ _ tendsto_log_abs_atBot hscaled hv
  refine hmain.congr fun t => ?_
  congr 2

end HTGeometry.ConstraintRelativity
