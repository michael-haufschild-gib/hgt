import Mathlib

/-!
# The cosine Laplace transform on the positive ray

`∫_0^∞ e^{-a s} cos(b s) ds = a/(a² + b²)` for `a > 0`, by exhibiting the primitive and taking its
limit at infinity.  mathlib carries the exponential integral but not this one.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The primitive of `e^{-a s} cos(b s)`. -/
noncomputable def cosLaplacePrimitive (a b s : ℝ) : ℝ :=
  Real.exp (-(a * s)) * (-a * Real.cos (b * s) + b * Real.sin (b * s)) / (a ^ 2 + b ^ 2)

theorem hasDerivAt_cosLaplacePrimitive {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (s : ℝ) :
    HasDerivAt (cosLaplacePrimitive a b) (Real.exp (-(a * s)) * Real.cos (b * s)) s := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-(a * s))) (Real.exp (-(a * s)) * -a) s := by
    have h1 : HasDerivAt (fun s : ℝ => -(a * s)) (-a) s := by
      have h0 : HasDerivAt (fun s : ℝ => (-a) * s) ((-a) * 1) s :=
        HasDerivAt.const_mul (-a) (hasDerivAt_id s)
      simpa [neg_mul] using h0
    simpa using h1.exp
  have hc : HasDerivAt (fun s : ℝ => Real.cos (b * s)) (-Real.sin (b * s) * b) s := by
    have h1 : HasDerivAt (fun s : ℝ => b * s) b s := by
      simpa using HasDerivAt.const_mul b (hasDerivAt_id s)
    simpa using h1.cos
  have hs : HasDerivAt (fun s : ℝ => Real.sin (b * s)) (Real.cos (b * s) * b) s := by
    have h1 : HasDerivAt (fun s : ℝ => b * s) b s := by
      simpa using HasDerivAt.const_mul b (hasDerivAt_id s)
    simpa using h1.sin
  have hnum : HasDerivAt (fun s : ℝ => -a * Real.cos (b * s) + b * Real.sin (b * s))
      (-a * (-Real.sin (b * s) * b) + b * (Real.cos (b * s) * b)) s :=
    (hc.const_mul (-a)).add (hs.const_mul b)
  have hmul := he.mul hnum
  have hdiv := hmul.div_const (a ^ 2 + b ^ 2)
  refine hdiv.congr_deriv ?_
  field_simp
  ring

theorem integrableOn_cosLaplace {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => Real.exp (-(a * s)) * Real.cos (b * s)) (Ioi 0) := by
  have hexp : IntegrableOn (fun s : ℝ => Real.exp (-(a * s))) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0 : ℝ) ha
    simpa [mul_comm] using this
  refine Integrable.mono' hexp ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_).restrict
    fun_prop
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have : |Real.cos (b * s)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [Real.exp_pos (-(a * s))]

theorem tendsto_cosLaplacePrimitive_atTop {a b : ℝ} (ha : 0 < a) :
    Tendsto (cosLaplacePrimitive a b) atTop (𝓝 0) := by
  have hbound : ∀ s : ℝ, |cosLaplacePrimitive a b s|
      ≤ (|a| + |b|) / (a ^ 2 + b ^ 2) * Real.exp (-(a * s)) := by
    intro s
    have hden : (0 : ℝ) < a ^ 2 + b ^ 2 := by positivity
    rw [cosLaplacePrimitive, abs_div, abs_of_pos hden, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have hnum : |-a * Real.cos (b * s) + b * Real.sin (b * s)| ≤ |a| + |b| := by
      calc |-a * Real.cos (b * s) + b * Real.sin (b * s)|
          ≤ |-a * Real.cos (b * s)| + |b * Real.sin (b * s)| := abs_add_le _ _
        _ ≤ |a| * 1 + |b| * 1 := by
            rw [abs_mul, abs_mul, abs_neg]
            exact add_le_add (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg a))
              (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg b))
        _ = |a| + |b| := by ring
    rw [div_le_iff₀ hden]
    have hpos : (0 : ℝ) < Real.exp (-(a * s)) := Real.exp_pos _
    calc Real.exp (-(a * s)) * |-a * Real.cos (b * s) + b * Real.sin (b * s)|
        ≤ Real.exp (-(a * s)) * (|a| + |b|) := by gcongr
      _ = (|a| + |b|) / (a ^ 2 + b ^ 2) * Real.exp (-(a * s)) * (a ^ 2 + b ^ 2) := by
          field_simp
  have hzero : Tendsto (fun s : ℝ => (|a| + |b|) / (a ^ 2 + b ^ 2) * Real.exp (-(a * s)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.exp (-(a * s))) atTop (𝓝 0) := by
      have h3 : Tendsto (fun s : ℝ => a * s) atTop atTop :=
        Filter.Tendsto.const_mul_atTop ha tendsto_id
      have h2 : Tendsto (fun s : ℝ => -(a * s)) atTop atBot := tendsto_neg_atTop_atBot.comp h3
      simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp h2
    simpa using h1.const_mul ((|a| + |b|) / (a ^ 2 + b ^ 2))
  refine squeeze_zero_norm ?_ hzero
  intro s
  rw [Real.norm_eq_abs]
  exact hbound s

/-- **The cosine Laplace transform.** -/
theorem integral_cosLaplace {a b : ℝ} (ha : 0 < a) :
    (∫ s in Ioi (0 : ℝ), Real.exp (-(a * s)) * Real.cos (b * s)) = a / (a ^ 2 + b ^ 2) := by
  have hab : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hderiv : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivAt (cosLaplacePrimitive a b) (Real.exp (-(a * s)) * Real.cos (b * s)) s :=
    fun s _ => hasDerivAt_cosLaplacePrimitive hab s
  have hint := integrableOn_cosLaplace (a := a) (b := b) ha
  have hlim := tendsto_cosLaplacePrimitive_atTop (a := a) (b := b) ha
  have hcont : ContinuousWithinAt (cosLaplacePrimitive a b) (Ici (0 : ℝ)) 0 :=
    (hasDerivAt_cosLaplacePrimitive hab 0).continuousAt.continuousWithinAt
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [h, cosLaplacePrimitive]
  simp
  ring

end GaloisForLFunctions.HTGeometry
