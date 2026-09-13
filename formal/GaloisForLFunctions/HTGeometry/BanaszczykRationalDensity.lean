import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The rational density in the cube-density argument

Lemma 2.4 of Guo--Fang--Lu, *Vector Balancing via Directional Total Variation*,
uses the probability density

`2 / (π (1 + t²)²)`.

This file isolates its deterministic analytic content.  In particular, the
kernel is normalized, even, centered, and has second moment one.  The proof of
the squared Cauchy-kernel integral is closed by differentiating
`x / (1 + x²)` over the whole real line.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- The one-dimensional rational density appearing after the tangent change
of variables in the paper's cosine-squared cube density. -/
def banaszczykRationalDensity (t : ℝ) : ℝ :=
  2 / (Real.pi * (1 + t ^ 2) ^ 2)

@[simp]
theorem banaszczykRationalDensity_neg (t : ℝ) :
    banaszczykRationalDensity (-t) = banaszczykRationalDensity t := by
  simp [banaszczykRationalDensity]

theorem banaszczykRationalDensity_pos (t : ℝ) :
    0 < banaszczykRationalDensity t := by
  unfold banaszczykRationalDensity
  positivity

theorem banaszczykRationalDensity_nonneg (t : ℝ) :
    0 ≤ banaszczykRationalDensity t :=
  (banaszczykRationalDensity_pos t).le

theorem continuous_banaszczykRationalDensity :
    Continuous banaszczykRationalDensity := by
  unfold banaszczykRationalDensity
  exact (continuous_const : Continuous fun _ : ℝ => (2 : ℝ)).div
    ((continuous_const : Continuous fun _ : ℝ => Real.pi).mul
      ((continuous_const.add (continuous_id.pow 2)).pow 2))
    (fun t => mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 (by positivity)))

/-- Integrability of the squared Cauchy kernel.  A weaker version already
appears in `SchwartzWeightedHolder`; it is reproved here under a small import
surface so this density module remains cheap to compile. -/
theorem integrable_inv_one_add_sq_sq_banaszczyk :
    Integrable (fun t : ℝ => ((1 + t ^ 2)⁻¹) ^ 2) := by
  refine Integrable.mono' integrable_inv_one_add_sq ?_ ?_
  · fun_prop
  · filter_upwards with t
    have ht : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hi : (1 + t ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ ht]
      exact le_add_of_nonneg_right (sq_nonneg t)
    nlinarith [inv_nonneg.mpr ht.le]

private def cauchyPrimitive (t : ℝ) : ℝ :=
  t / (1 + t ^ 2)

private theorem hasDerivAt_cauchyPrimitive (t : ℝ) :
    HasDerivAt cauchyPrimitive ((1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
  have ht : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id' (𝕜 := ℝ) t
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) (0 : ℝ) t :=
    hasDerivAt_const (𝕜 := ℝ) (c := (1 : ℝ)) (x := t)
  have h := hid.div (hone.add (hid.pow 2)) ht
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · dsimp only [Pi.add_apply, Pi.pow_apply]
    ring
  · filter_upwards with x
    unfold cauchyPrimitive
    rfl

private theorem tendsto_cauchyPrimitive_atTop :
    Tendsto cauchyPrimitive atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hcont : Tendsto (fun y : ℝ => y / (1 + y ^ 2)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun y : ℝ => y / (1 + y ^ 2)) :=
      continuous_id.div
        ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).add (continuous_id.pow 2))
        (fun y : ℝ => by positivity)
    simpa [ContinuousAt] using
      (hc.continuousAt : ContinuousAt (fun y : ℝ => y / (1 + y ^ 2)) 0)
  apply (hcont.comp hinv).congr'
  filter_upwards with x
  unfold cauchyPrimitive
  change x⁻¹ / (1 + x⁻¹ ^ 2) = x / (1 + x ^ 2)
  by_cases hx : x = 0
  · simp [hx]
  · field_simp [hx, show (1 + x ^ 2 : ℝ) ≠ 0 by positivity,
      show (1 + x⁻¹ ^ 2 : ℝ) ≠ 0 by positivity]
    ring

private theorem tendsto_cauchyPrimitive_atBot :
    Tendsto cauchyPrimitive atBot (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
  have hcont : Tendsto (fun y : ℝ => y / (1 + y ^ 2)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun y : ℝ => y / (1 + y ^ 2)) :=
      continuous_id.div
        ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).add (continuous_id.pow 2))
        (fun y : ℝ => by positivity)
    simpa [ContinuousAt] using
      (hc.continuousAt : ContinuousAt (fun y : ℝ => y / (1 + y ^ 2)) 0)
  apply (hcont.comp hinv).congr'
  filter_upwards with x
  unfold cauchyPrimitive
  change x⁻¹ / (1 + x⁻¹ ^ 2) = x / (1 + x ^ 2)
  by_cases hx : x = 0
  · simp [hx]
  · field_simp [hx, show (1 + x ^ 2 : ℝ) ≠ 0 by positivity,
      show (1 + x⁻¹ ^ 2 : ℝ) ≠ 0 by positivity]
    ring

private theorem integrable_cauchyPrimitive_deriv :
    Integrable (fun t : ℝ => (1 - t ^ 2) / (1 + t ^ 2) ^ 2) := by
  have h := (integrable_inv_one_add_sq_sq_banaszczyk.const_mul 2).sub
    integrable_inv_one_add_sq
  apply h.congr
  filter_upwards with t
  have ht : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  simp only [Pi.sub_apply]
  field_simp [ht]
  ring

/-- Exact squared Cauchy-kernel mass. -/
@[simp]
theorem integral_univ_inv_one_add_sq_sq :
    (∫ t : ℝ, ((1 + t ^ 2)⁻¹) ^ 2) = Real.pi / 2 := by
  have hzero : (∫ t : ℝ, (1 - t ^ 2) / (1 + t ^ 2) ^ 2) = 0 := by
    simpa using integral_of_hasDerivAt_of_tendsto hasDerivAt_cauchyPrimitive
      integrable_cauchyPrimitive_deriv tendsto_cauchyPrimitive_atBot
      tendsto_cauchyPrimitive_atTop
  have hrewrite : (fun t : ℝ => (1 - t ^ 2) / (1 + t ^ 2) ^ 2) =
      fun t : ℝ => 2 * ((1 + t ^ 2)⁻¹) ^ 2 - (1 + t ^ 2)⁻¹ := by
    funext t
    have ht : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp [ht]
    ring
  rw [hrewrite,
    integral_sub (integrable_inv_one_add_sq_sq_banaszczyk.const_mul 2)
      integrable_inv_one_add_sq,
    integral_const_mul, integral_univ_inv_one_add_sq] at hzero
  linarith

theorem integrable_banaszczykRationalDensity :
    Integrable banaszczykRationalDensity := by
  have hfun : banaszczykRationalDensity =
      fun t : ℝ => (2 / Real.pi) * ((1 + t ^ 2)⁻¹) ^ 2 := by
    funext t
    unfold banaszczykRationalDensity
    field_simp [Real.pi_ne_zero, show (1 + t ^ 2 : ℝ) ≠ 0 by positivity]
  rw [hfun]
  exact integrable_inv_one_add_sq_sq_banaszczyk.const_mul _

/-- The rational kernel is a probability density. -/
@[simp]
theorem integral_banaszczykRationalDensity :
    ∫ t : ℝ, banaszczykRationalDensity t = 1 := by
  have hfun : banaszczykRationalDensity =
      fun t : ℝ => (2 / Real.pi) * ((1 + t ^ 2)⁻¹) ^ 2 := by
    funext t
    unfold banaszczykRationalDensity
    field_simp [Real.pi_ne_zero, show (1 + t ^ 2 : ℝ) ≠ 0 by positivity]
  rw [hfun, integral_const_mul, integral_univ_inv_one_add_sq_sq]
  field_simp [Real.pi_ne_zero]

theorem integrable_sq_mul_banaszczykRationalDensity :
    Integrable (fun t : ℝ => t ^ 2 * banaszczykRationalDensity t) := by
  have hbase : Integrable
      (fun t : ℝ => (1 + t ^ 2)⁻¹ - ((1 + t ^ 2)⁻¹) ^ 2) :=
    integrable_inv_one_add_sq.sub integrable_inv_one_add_sq_sq_banaszczyk
  have hscaled := hbase.const_mul (2 / Real.pi)
  apply hscaled.congr
  filter_upwards with t
  unfold banaszczykRationalDensity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have ht : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hpi, ht]
  ring

/-- The paper's rational random variable has variance one. -/
@[simp]
theorem integral_sq_mul_banaszczykRationalDensity :
    ∫ t : ℝ, t ^ 2 * banaszczykRationalDensity t = 1 := by
  have hrewrite : (fun t : ℝ => t ^ 2 * banaszczykRationalDensity t) =
      fun t : ℝ => (2 / Real.pi) *
        ((1 + t ^ 2)⁻¹ - ((1 + t ^ 2)⁻¹) ^ 2) := by
    funext t
    unfold banaszczykRationalDensity
    have ht : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp [Real.pi_ne_zero, ht]
    ring
  rw [hrewrite, integral_const_mul,
    integral_sub integrable_inv_one_add_sq integrable_inv_one_add_sq_sq_banaszczyk,
    integral_univ_inv_one_add_sq, integral_univ_inv_one_add_sq_sq]
  field_simp [Real.pi_ne_zero]
  ring

theorem integrable_id_mul_banaszczykRationalDensity :
    Integrable (fun t : ℝ => t * banaszczykRationalDensity t) := by
  have hmajor := integrable_banaszczykRationalDensity.add
    integrable_sq_mul_banaszczykRationalDensity
  refine Integrable.mono' hmajor ?_ ?_
  · exact (continuous_id.mul continuous_banaszczykRationalDensity).aestronglyMeasurable
  · filter_upwards with t
    have hρ := banaszczykRationalDensity_nonneg t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ]
    have ht : |t| ≤ 1 + t ^ 2 := by
      nlinarith [sq_nonneg (|t| - 1), sq_abs t]
    change |t| * banaszczykRationalDensity t ≤
      banaszczykRationalDensity t + t ^ 2 * banaszczykRationalDensity t
    nlinarith

/-- Evenness centers the rational density exactly. -/
@[simp]
theorem integral_id_mul_banaszczykRationalDensity :
    ∫ t : ℝ, t * banaszczykRationalDensity t = 0 := by
  have hreflect := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    measurableEmbedding_neg (fun t : ℝ => t * banaszczykRationalDensity t)
  have hodd : (fun t : ℝ => (-t) * banaszczykRationalDensity (-t)) =
      fun t : ℝ => -(t * banaszczykRationalDensity t) := by
    funext t
    rw [banaszczykRationalDensity_neg]
    ring
  rw [hodd, integral_neg] at hreflect
  linarith

end GaloisForLFunctions.HTGeometry
