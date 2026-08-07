import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The horizontal segments of the truncated Perron contour

Perron's lemma bounds the truncated vertical integral of `y^s/s` against the indicator of `y > 1`, and its
proof shifts the contour to `Re s = -A` and lets `A → ∞`.  The cost of the shift is the two horizontal
segments at height `±T`, and on those the kernel is elementary: `‖y^s‖ = y^{Re s}` while `‖s‖ ≥ T`, so

`‖∫_{-A}^{σ} y^{u+iT}/(u+iT) du‖ ≤ (1/T) ∫_{-A}^{σ} y^u du ≤ y^σ/(T log y)`   for `y > 1`,

uniformly in `A`.  This is the estimate that produces Perron's `min(1, 1/(T|log y|))` factor, the factor
that makes truncated Perron the only device whose error is a *global* Dirichlet-series sum rather than a
short-interval divisor estimate.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Complex MeasureTheory intervalIntegral

/-- The exponential integral in the form the Perron contour needs. -/
theorem integral_exp_mul_const (L : ℝ) (hL : L ≠ 0) (a b : ℝ) :
    (∫ u in a..b, Real.exp (u * L)) = (Real.exp (b * L) - Real.exp (a * L)) / L := by
  rw [intervalIntegral.integral_comp_mul_right (f := Real.exp) (c := L) hL, integral_exp,
    smul_eq_mul]
  field_simp

/-- **The horizontal segment of the Perron contour.**  On the line `Im s = T` the kernel `y^s/s` has
norm at most `y^{Re s}/T`, so the segment integral is at most `y^σ/(T log y)`. -/
theorem norm_integral_horizontal_le {y : ℝ} (hy : 1 < y) {σ A T : ℝ} (hT : T ≠ 0)
    (hAσ : -A ≤ σ) :
    ‖∫ u in (-A)..σ, ((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I))
        / ((u : ℂ) + (T : ℝ) * Complex.I)‖
      ≤ y ^ σ / (|T| * Real.log y) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hL : (0 : ℝ) < Real.log y := Real.log_pos hy
  have hTabs : (0 : ℝ) < |T| := abs_pos.mpr hT
  set L : ℝ := Real.log y with hLdef
  have hrpow : ∀ u : ℝ, y ^ u = Real.exp (u * L) := by
    intro u
    rw [hLdef, Real.rpow_def_of_pos hy0, mul_comm]
  have hcont : ContinuousOn (fun u : ℝ => ((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I))
      / ((u : ℂ) + (T : ℝ) * Complex.I)) (Set.uIcc (-A) σ) := by
    refine ContinuousOn.div ?_ (Continuous.continuousOn (by fun_prop)) ?_
    · refine Continuous.continuousOn ?_
      refine Continuous.const_cpow (by fun_prop) ?_
      exact Or.inl (by exact_mod_cast hy0.ne')
    · intro u _ hzero
      have him : ((u : ℂ) + (T : ℝ) * Complex.I).im = T := by simp
      rw [hzero] at him
      simp at him
      exact absurd him.symm hT
  have hmaj : Continuous fun u : ℝ => Real.exp (u * L) / |T| := by fun_prop
  have hnorm : ∀ u ∈ Set.Icc (-A) σ,
      ‖((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I)) / ((u : ℂ) + (T : ℝ) * Complex.I)‖
        ≤ Real.exp (u * L) / |T| := by
    intro u _
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : ((u : ℂ) + (T : ℝ) * Complex.I).re = u := by simp
    rw [hre, ← hrpow u]
    have hden : |T| ≤ ‖(u : ℂ) + (T : ℝ) * Complex.I‖ := by
      have him : ((u : ℂ) + (T : ℝ) * Complex.I).im = T := by simp
      calc |T| = |((u : ℂ) + (T : ℝ) * Complex.I).im| := by rw [him]
        _ ≤ ‖(u : ℂ) + (T : ℝ) * Complex.I‖ := Complex.abs_im_le_norm _
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le u) hTabs hden
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hAσ) ?_
  have hmono : (∫ u in (-A)..σ, ‖((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I))
        / ((u : ℂ) + (T : ℝ) * Complex.I)‖)
      ≤ ∫ u in (-A)..σ, Real.exp (u * L) / |T| :=
    intervalIntegral.integral_mono_on hAσ hcont.norm.intervalIntegrable
      hmaj.continuousOn.intervalIntegrable hnorm
  refine le_trans hmono ?_
  have hval : (∫ u in (-A)..σ, Real.exp (u * L) / |T|)
      = (Real.exp (σ * L) - Real.exp (-A * L)) / (L * |T|) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, integral_exp_mul_const L hL.ne' (-A) σ]
    field_simp
  rw [hval]
  have hpos : (0 : ℝ) < Real.exp (-A * L) := Real.exp_pos _
  have hden : (0 : ℝ) < L * |T| := by positivity
  rw [div_le_div_iff₀ hden (by positivity : (0:ℝ) < |T| * L)]
  have hyσ : y ^ σ = Real.exp (σ * L) := hrpow σ
  rw [hyσ]
  nlinarith [hpos, Real.exp_pos (σ * L), hden, hL, hTabs]

/-- **The vertical edge of the shifted Perron contour.**  On the line `Re s = a` the kernel `y^s/s` has
norm at most `y^a/|a|`, so the truncated edge is at most `2T·y^a/|a|`.  For `y > 1` and `a = -A` this
tends to zero as `A → ∞`, which is what licenses the contour shift. -/
theorem norm_integral_vertical_edge_cpow_le {y : ℝ} (hy : 0 < y) {a T : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, ((y : ℂ) ^ ((a : ℂ) + (t : ℝ) * Complex.I))
        / ((a : ℂ) + (t : ℝ) * Complex.I)‖
      ≤ 2 * T * (y ^ a / |a|) := by
  have habs : (0 : ℝ) < |a| := abs_pos.mpr ha
  have hbound : ∀ t ∈ Set.uIoc (-T) T,
      ‖((y : ℂ) ^ ((a : ℂ) + (t : ℝ) * Complex.I))
        / ((a : ℂ) + (t : ℝ) * Complex.I)‖ ≤ y ^ a / |a| := by
    intro t _
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : ((a : ℂ) + (t : ℝ) * Complex.I).re = a := by simp
    rw [hre]
    have hden : |a| ≤ ‖(a : ℂ) + (t : ℝ) * Complex.I‖ := by
      calc |a| = |((a : ℂ) + (t : ℝ) * Complex.I).re| := by rw [hre]
        _ ≤ ‖(a : ℂ) + (t : ℝ) * Complex.I‖ := Complex.abs_re_le_norm _
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le a) habs hden
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbound) ?_
  have hlen : |T - -T| = 2 * T := by
    rw [show T - -T = 2 * T by ring, abs_of_nonneg (by linarith)]
  rw [hlen]
  exact le_of_eq (by ring)

/-- **The horizontal segment for `y < 1`.**  Shifting to the right instead, the same elementary estimate
gives `y^σ/(T|log y|)`, uniformly in the right endpoint. -/
theorem norm_integral_horizontal_le' {y : ℝ} (hy0 : 0 < y) (hy : y < 1) {σ A T : ℝ}
    (hT : T ≠ 0) (hσA : σ ≤ A) :
    ‖∫ u in σ..A, ((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I))
        / ((u : ℂ) + (T : ℝ) * Complex.I)‖
      ≤ y ^ σ / (|T| * |Real.log y|) := by
  have hL : Real.log y < 0 := Real.log_neg hy0 hy
  have hTabs : (0 : ℝ) < |T| := abs_pos.mpr hT
  set L : ℝ := Real.log y with hLdef
  have habsL : |L| = -L := abs_of_neg hL
  have hrpow : ∀ u : ℝ, y ^ u = Real.exp (u * L) := by
    intro u
    rw [hLdef, Real.rpow_def_of_pos hy0, mul_comm]
  have hcont : ContinuousOn (fun u : ℝ => ((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I))
      / ((u : ℂ) + (T : ℝ) * Complex.I)) (Set.uIcc σ A) := by
    refine ContinuousOn.div ?_ (Continuous.continuousOn (by fun_prop)) ?_
    · refine Continuous.continuousOn ?_
      refine Continuous.const_cpow (by fun_prop) ?_
      exact Or.inl (by exact_mod_cast hy0.ne')
    · intro u _ hzero
      have him : ((u : ℂ) + (T : ℝ) * Complex.I).im = T := by simp
      rw [hzero] at him
      simp at him
      exact absurd him.symm hT
  have hmaj : Continuous fun u : ℝ => Real.exp (u * L) / |T| := by fun_prop
  have hnorm : ∀ u ∈ Set.Icc σ A,
      ‖((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I)) / ((u : ℂ) + (T : ℝ) * Complex.I)‖
        ≤ Real.exp (u * L) / |T| := by
    intro u _
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : ((u : ℂ) + (T : ℝ) * Complex.I).re = u := by simp
    rw [hre, ← hrpow u]
    have hden : |T| ≤ ‖(u : ℂ) + (T : ℝ) * Complex.I‖ := by
      have him : ((u : ℂ) + (T : ℝ) * Complex.I).im = T := by simp
      calc |T| = |((u : ℂ) + (T : ℝ) * Complex.I).im| := by rw [him]
        _ ≤ ‖(u : ℂ) + (T : ℝ) * Complex.I‖ := Complex.abs_im_le_norm _
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le u) hTabs hden
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hσA) ?_
  have hmono : (∫ u in σ..A, ‖((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I))
        / ((u : ℂ) + (T : ℝ) * Complex.I)‖)
      ≤ ∫ u in σ..A, Real.exp (u * L) / |T| :=
    intervalIntegral.integral_mono_on hσA hcont.norm.intervalIntegrable
      hmaj.continuousOn.intervalIntegrable hnorm
  refine le_trans hmono ?_
  have hval : (∫ u in σ..A, Real.exp (u * L) / |T|)
      = (Real.exp (A * L) - Real.exp (σ * L)) / (L * |T|) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, integral_exp_mul_const L hL.ne σ A]
    field_simp
  rw [hval, habsL]
  have hApos : (0 : ℝ) < Real.exp (A * L) := Real.exp_pos _
  have hyσ : y ^ σ = Real.exp (σ * L) := hrpow σ
  rw [hyσ]
  have hden : (0 : ℝ) < -L * |T| := by nlinarith [hTabs, hL]
  have hid : (Real.exp (A * L) - Real.exp (σ * L)) / (L * |T|)
      = (Real.exp (σ * L) - Real.exp (A * L)) / (-L * |T|) := by
    rw [neg_mul, div_neg, neg_div', neg_sub]
  have hnum : Real.exp (σ * L) - Real.exp (A * L) ≤ Real.exp (σ * L) := by
    linarith [hApos]
  calc (Real.exp (A * L) - Real.exp (σ * L)) / (L * |T|)
      = (Real.exp (σ * L) - Real.exp (A * L)) / (-L * |T|) := hid
    _ ≤ Real.exp (σ * L) / (-L * |T|) := by gcongr
    _ = Real.exp (σ * L) / (|T| * -L) := by ring

end GaloisForLFunctions.HTGeometry
end
