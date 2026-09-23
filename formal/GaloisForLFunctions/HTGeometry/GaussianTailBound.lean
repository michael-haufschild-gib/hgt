import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# An explicit exponential bound for the Gaussian tail

The `L²` mass of the Gaussian outside an aperture is what a truncated Gaussian loses, so a
concentration estimate for a prolate trial space needs it quantitatively rather than merely as a
vanishing quantity.

The bound is elementary and sharp enough for the purpose.  On `x ≥ a > 0` one has `1 ≤ x/a`, so

```text
∫_a^∞ e^(−2πx²) dx ≤ (1/a) ∫_a^∞ x e^(−2πx²) dx = e^(−2πa²)/(4πa),
```

the last integral being exact because `x e^(−2πx²)` has the elementary antiderivative
`−e^(−2πx²)/(4π)`, which vanishes at infinity.  In particular the tail decays like the square of
the Gaussian itself — the exponential rate that a polynomially decaying trial function could
never provide.
-/

open MeasureTheory Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions

/-- The squared Gaussian, whose integral is the `L²` mass of the Gaussian. -/
theorem hasDerivAt_gaussPrimitive (x : ℝ) :
    HasDerivAt (fun y : ℝ => -Real.exp (-(2 * π * y ^ (2 : ℕ))) / (4 * π))
      (x * Real.exp (-(2 * π * x ^ (2 : ℕ)))) x := by
  have hinner : HasDerivAt (fun y : ℝ => -(2 * π * y ^ (2 : ℕ))) (-(2 * π * (2 * x))) x := by
    have hinnerRaw := ((hasDerivAt_pow 2 x).const_mul (2 * π)).neg
    have hfun :
        -(fun y : ℝ => 2 * π * y ^ (2 : ℕ)) =
          (fun y : ℝ => -(2 * π * y ^ (2 : ℕ))) := by
      funext y
      rfl
    rw [hfun] at hinnerRaw
    apply hinnerRaw.congr_deriv
    norm_num
  have hexp := hinner.exp
  have hpi : (4 : ℝ) * π ≠ 0 := by positivity
  have hneg := hexp.neg
  have hfun :
      -(fun y : ℝ => Real.exp (-(2 * π * y ^ (2 : ℕ)))) =
        (fun y : ℝ => -Real.exp (-(2 * π * y ^ (2 : ℕ)))) := by
    funext y
    rfl
  rw [hfun] at hneg
  have h := hneg.div_const (4 * π)
  apply h.congr_deriv
  field_simp [hpi]
  ring

/-- The Gaussian vanishes at infinity. -/
theorem tendsto_gaussExp_atTop :
    Filter.Tendsto (fun y : ℝ => Real.exp (-(2 * π * y ^ (2 : ℕ)))) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun y : ℝ => 2 * π * y ^ (2 : ℕ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) (Filter.tendsto_pow_atTop (by norm_num))
  have h2 : Filter.Tendsto (fun y : ℝ => -(2 * π * y ^ (2 : ℕ))) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp h1
  exact Real.tendsto_exp_atBot.comp h2

theorem tendsto_gaussPrimitive :
    Filter.Tendsto (fun y : ℝ => -Real.exp (-(2 * π * y ^ (2 : ℕ))) / (4 * π))
      Filter.atTop (nhds 0) := by
  have h2 := (tendsto_gaussExp_atTop.neg).div_const (4 * π)
  simpa using h2

/-- The exact first moment of the Gaussian tail. -/
theorem integral_Ioi_id_mul_gauss {a : ℝ} :
    ∫ x in Ioi a, x * Real.exp (-(2 * π * x ^ (2 : ℕ)))
      = Real.exp (-(2 * π * a ^ (2 : ℕ))) / (4 * π) := by
  have hcont : ContinuousWithinAt
      (fun y : ℝ => -Real.exp (-(2 * π * y ^ (2 : ℕ))) / (4 * π)) (Ici a) a := by
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hderiv : ∀ x ∈ Ioi a, HasDerivAt
      (fun y : ℝ => -Real.exp (-(2 * π * y ^ (2 : ℕ))) / (4 * π))
      (x * Real.exp (-(2 * π * x ^ (2 : ℕ)))) x := fun x _ => hasDerivAt_gaussPrimitive x
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-(2 * π * x ^ (2 : ℕ)))) (Ioi a) volume := by
    have hb : (0 : ℝ) < 2 * π := by positivity
    have hgi : Integrable (fun x : ℝ => x * Real.exp (-(2 * π) * x ^ (2 : ℕ))) volume := by
      simpa using integrable_mul_exp_neg_mul_sq hb
    have : Integrable (fun x : ℝ => x * Real.exp (-(2 * π * x ^ (2 : ℕ)))) volume := by
      refine hgi.congr ?_
      filter_upwards with x
      ring_nf
    exact this.integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint tendsto_gaussPrimitive
  rw [h]
  ring

/-- **The Gaussian tail bound.**  Outside an aperture `a > 0` the squared Gaussian has mass at
most `e^(−2πa²)/(4πa)`: exponentially small in `a²`. -/
theorem integral_Ioi_gauss_sq_le {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi a, Real.exp (-(2 * π * x ^ (2 : ℕ)))
      ≤ Real.exp (-(2 * π * a ^ (2 : ℕ))) / (4 * π * a) := by
  have hb : (0 : ℝ) < 2 * π := by positivity
  have hint1 : IntegrableOn (fun x : ℝ => Real.exp (-(2 * π * x ^ (2 : ℕ)))) (Ioi a) volume := by
    have hgi : Integrable (fun x : ℝ => Real.exp (-(2 * π) * x ^ (2 : ℕ))) volume :=
      integrable_exp_neg_mul_sq hb
    have : Integrable (fun x : ℝ => Real.exp (-(2 * π * x ^ (2 : ℕ)))) volume := by
      refine hgi.congr ?_
      filter_upwards with x
      ring_nf
    exact this.integrableOn
  have hint2 : IntegrableOn (fun x : ℝ => a⁻¹ * (x * Real.exp (-(2 * π * x ^ (2 : ℕ)))))
      (Ioi a) volume := by
    have hgi : Integrable (fun x : ℝ => x * Real.exp (-(2 * π) * x ^ (2 : ℕ))) volume := by
      simpa using integrable_mul_exp_neg_mul_sq hb
    have : Integrable (fun x : ℝ => a⁻¹ * (x * Real.exp (-(2 * π * x ^ (2 : ℕ))))) volume := by
      refine (hgi.const_mul a⁻¹).congr ?_
      filter_upwards with x
      ring_nf
    exact this.integrableOn
  have hmono : ∀ x ∈ Ioi a, Real.exp (-(2 * π * x ^ (2 : ℕ)))
      ≤ a⁻¹ * (x * Real.exp (-(2 * π * x ^ (2 : ℕ)))) := by
    intro x hx
    have hxa : a < x := hx
    have hxpos : (0 : ℝ) < x := lt_trans ha hxa
    have hone : (1 : ℝ) ≤ a⁻¹ * x := by
      rw [le_inv_mul_iff₀ ha]
      linarith
    have hE : (0 : ℝ) < Real.exp (-(2 * π * x ^ (2 : ℕ))) := Real.exp_pos _
    calc Real.exp (-(2 * π * x ^ (2 : ℕ))) = 1 * Real.exp (-(2 * π * x ^ (2 : ℕ))) := (one_mul _).symm
      _ ≤ (a⁻¹ * x) * Real.exp (-(2 * π * x ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_right hone hE.le
      _ = a⁻¹ * (x * Real.exp (-(2 * π * x ^ (2 : ℕ)))) := by ring
  have hcmp := setIntegral_mono_on hint1 hint2 measurableSet_Ioi hmono
  have hval : ∫ x in Ioi a, a⁻¹ * (x * Real.exp (-(2 * π * x ^ (2 : ℕ))))
      = a⁻¹ * (Real.exp (-(2 * π * a ^ (2 : ℕ))) / (4 * π)) := by
    rw [integral_const_mul, integral_Ioi_id_mul_gauss]
  rw [hval] at hcmp
  have heq : a⁻¹ * (Real.exp (-(2 * π * a ^ (2 : ℕ))) / (4 * π))
      = Real.exp (-(2 * π * a ^ (2 : ℕ))) / (4 * π * a) := by
    field_simp
  rw [heq] at hcmp
  exact hcmp

/-- The tail mass vanishes as the aperture grows. -/
theorem tendsto_integral_Ioi_gauss_sq :
    Filter.Tendsto (fun a : ℝ => ∫ x in Ioi a, Real.exp (-(2 * π * x ^ (2 : ℕ))))
      Filter.atTop (nhds 0) := by
  have hb : (0 : ℝ) < 2 * π := by positivity
  have hbound : Filter.Tendsto
      (fun a : ℝ => Real.exp (-(2 * π * a ^ (2 : ℕ))) / (4 * π * a)) Filter.atTop (nhds 0) := by
    have h := tendsto_gaussExp_atTop
    have hinv : Filter.Tendsto (fun a : ℝ => (4 * π * a)⁻¹) Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun a : ℝ => 4 * π * a) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
      exact this.inv_tendsto_atTop
    have hmul := h.mul hinv
    simp only [mul_zero] at hmul
    refine hmul.congr fun a => ?_
    rw [div_eq_mul_inv]
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a _
    apply setIntegral_nonneg measurableSet_Ioi
    intro x _
    exact (Real.exp_pos _).le
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
    exact integral_Ioi_gauss_sq_le ha

end GaloisForLFunctions
