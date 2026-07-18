import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Explicit tail bounds for `e^(−bx²)` at an arbitrary rate

A trial-space estimate turns into a rate only when the mass a function loses outside an aperture
is known explicitly.  For the Gaussian family the bound is elementary: on `x ≥ a > 0` one has
`1 ≤ x/a`, so

```text
∫_a^∞ e^(−bx²) dx ≤ (1/a) ∫_a^∞ x e^(−bx²) dx = e^(−ba²)/(2ba),
```

the last integral being exact, `−e^(−bx²)/(2b)` being an antiderivative that vanishes at
infinity.  Doubling by reflection gives the two-sided bound outside `[−a, a]`.

The rate `b` is left free because different objects in the same argument carry different ones:
the `L²` mass of `e^(−πx²)` involves `e^(−2πx²)`, while absorbing a polynomial factor costs one
Gaussian and leaves `e^(−πx²)`.  Anything dominated by a constant multiple of `e^(−bx²)`
inherits the bound, which is the form the Hermite tails are consumed in.
-/

open MeasureTheory Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions

variable {b : ℝ}

theorem integrable_expNegSq (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-(b * x ^ 2))) volume := by
  refine (integrable_exp_neg_mul_sq hb).congr ?_
  filter_upwards with x
  ring_nf

/-- `−e^(−bx²)/(2b)` is an antiderivative of `x e^(−bx²)`. -/
theorem hasDerivAt_expNegSqPrimitive (hb : 0 < b) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -Real.exp (-(b * y ^ 2)) / (2 * b))
      (x * Real.exp (-(b * x ^ 2))) x := by
  have hinner : HasDerivAt (fun y : ℝ => -(b * y ^ 2)) (-(b * (2 * x))) x := by
    simpa using ((hasDerivAt_pow 2 x).const_mul b).neg
  have hexp := hinner.exp
  have hbne : (2 : ℝ) * b ≠ 0 := by positivity
  have h := (hexp.neg).div_const (2 * b)
  convert h using 1
  field_simp

theorem tendsto_expNegSq_atTop (hb : 0 < b) :
    Filter.Tendsto (fun y : ℝ => Real.exp (-(b * y ^ 2))) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun y : ℝ => b * y ^ 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hb (Filter.tendsto_pow_atTop (by norm_num))
  have h2 : Filter.Tendsto (fun y : ℝ => -(b * y ^ 2)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp h1
  exact Real.tendsto_exp_atBot.comp h2

theorem tendsto_expNegSqPrimitive (hb : 0 < b) :
    Filter.Tendsto (fun y : ℝ => -Real.exp (-(b * y ^ 2)) / (2 * b)) Filter.atTop (nhds 0) := by
  have h2 := ((tendsto_expNegSq_atTop hb).neg).div_const (2 * b)
  simpa using h2

/-- The exact first moment of the tail. -/
theorem integral_Ioi_id_mul_expNegSq (hb : 0 < b) {a : ℝ} :
    ∫ x in Ioi a, x * Real.exp (-(b * x ^ 2)) = Real.exp (-(b * a ^ 2)) / (2 * b) := by
  have hcont : ContinuousWithinAt
      (fun y : ℝ => -Real.exp (-(b * y ^ 2)) / (2 * b)) (Ici a) a := by
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hderiv : ∀ x ∈ Ioi a, HasDerivAt
      (fun y : ℝ => -Real.exp (-(b * y ^ 2)) / (2 * b))
      (x * Real.exp (-(b * x ^ 2))) x := fun x _ => hasDerivAt_expNegSqPrimitive hb x
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-(b * x ^ 2))) (Ioi a) volume := by
    have hgi : Integrable (fun x : ℝ => x * Real.exp (-b * x ^ 2)) volume :=
      integrable_mul_exp_neg_mul_sq hb
    have hcong : Integrable (fun x : ℝ => x * Real.exp (-(b * x ^ 2))) volume := by
      refine hgi.congr ?_
      filter_upwards with x
      ring_nf
    exact hcong.integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint (tendsto_expNegSqPrimitive hb)
  rw [h]
  ring

/-- **The one-sided tail bound.** -/
theorem integral_Ioi_expNegSq_le (hb : 0 < b) {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi a, Real.exp (-(b * x ^ 2)) ≤ Real.exp (-(b * a ^ 2)) / (2 * b * a) := by
  have hint1 : IntegrableOn (fun x : ℝ => Real.exp (-(b * x ^ 2))) (Ioi a) volume :=
    (integrable_expNegSq hb).integrableOn
  have hint2 : IntegrableOn (fun x : ℝ => a⁻¹ * (x * Real.exp (-(b * x ^ 2))))
      (Ioi a) volume := by
    have hgi : Integrable (fun x : ℝ => x * Real.exp (-b * x ^ 2)) volume :=
      integrable_mul_exp_neg_mul_sq hb
    have hcong : Integrable (fun x : ℝ => a⁻¹ * (x * Real.exp (-(b * x ^ 2)))) volume := by
      refine (hgi.const_mul a⁻¹).congr ?_
      filter_upwards with x
      ring_nf
    exact hcong.integrableOn
  have hmono : ∀ x ∈ Ioi a, Real.exp (-(b * x ^ 2))
      ≤ a⁻¹ * (x * Real.exp (-(b * x ^ 2))) := by
    intro x hx
    have hxa : a < x := hx
    have hone : (1 : ℝ) ≤ a⁻¹ * x := by
      rw [le_inv_mul_iff₀ ha]
      linarith
    have hE : (0 : ℝ) < Real.exp (-(b * x ^ 2)) := Real.exp_pos _
    calc Real.exp (-(b * x ^ 2)) = 1 * Real.exp (-(b * x ^ 2)) := (one_mul _).symm
      _ ≤ (a⁻¹ * x) * Real.exp (-(b * x ^ 2)) := mul_le_mul_of_nonneg_right hone hE.le
      _ = a⁻¹ * (x * Real.exp (-(b * x ^ 2))) := by ring
  have hcmp := setIntegral_mono_on hint1 hint2 measurableSet_Ioi hmono
  have hval : ∫ x in Ioi a, a⁻¹ * (x * Real.exp (-(b * x ^ 2)))
      = a⁻¹ * (Real.exp (-(b * a ^ 2)) / (2 * b)) := by
    rw [integral_const_mul, integral_Ioi_id_mul_expNegSq hb]
  rw [hval] at hcmp
  have heq : a⁻¹ * (Real.exp (-(b * a ^ 2)) / (2 * b))
      = Real.exp (-(b * a ^ 2)) / (2 * b * a) := by
    field_simp
  rw [heq] at hcmp
  exact hcmp

/-- **The two-sided tail bound**, by reflecting the left ray onto the right one. -/
theorem integral_compl_Icc_expNegSq_le (hb : 0 < b) {a : ℝ} (ha : 0 < a) :
    ∫ x in (Icc (-a) a)ᶜ, Real.exp (-(b * x ^ 2)) ≤ Real.exp (-(b * a ^ 2)) / (b * a) := by
  have hgi := integrable_expNegSq hb
  have hsplit : (Icc (-a) a)ᶜ = Iio (-a) ∪ Ioi a := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      not_and_or, not_le]
  have hdisj : Disjoint (Iio (-a)) (Ioi a) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_Ioi] at hx'
    linarith
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hgi.integrableOn hgi.integrableOn]
  have hIioIic : ∫ x in Iio (-a), Real.exp (-(b * x ^ 2))
      = ∫ x in Iic (-a), Real.exp (-(b * x ^ 2)) :=
    setIntegral_congr_set Iio_ae_eq_Iic
  have hrefl : ∫ x in Iic (-a), Real.exp (-(b * x ^ 2))
      = ∫ x in Ioi a, Real.exp (-(b * x ^ 2)) := by
    rw [← integral_comp_neg_Ioi a (fun x : ℝ => Real.exp (-(b * x ^ 2)))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp
  rw [hIioIic, hrefl]
  have hray := integral_Ioi_expNegSq_le hb ha
  have hba : (0 : ℝ) < b * a := mul_pos hb ha
  have hhalf : Real.exp (-(b * a ^ 2)) / (2 * b * a) + Real.exp (-(b * a ^ 2)) / (2 * b * a)
      = Real.exp (-(b * a ^ 2)) / (b * a) := by
    field_simp
    ring
  linarith

/-- **Anything dominated by a multiple of `e^(−bx²)` inherits the two-sided tail bound.** -/
theorem setIntegral_compl_Icc_le_of_le_expNegSq (hb : 0 < b) {a C : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) {f : ℝ → ℝ} (hfint : IntegrableOn f ((Icc (-a) a)ᶜ) volume)
    (hf : ∀ x, f x ≤ C * Real.exp (-(b * x ^ 2))) :
    ∫ x in (Icc (-a) a)ᶜ, f x ≤ C * (Real.exp (-(b * a ^ 2)) / (b * a)) := by
  have hdom : IntegrableOn (fun x : ℝ => C * Real.exp (-(b * x ^ 2))) ((Icc (-a) a)ᶜ) volume :=
    ((integrable_expNegSq hb).const_mul C).integrableOn
  have hmono := setIntegral_mono_on hfint hdom measurableSet_Icc.compl (fun x _ => hf x)
  have hval : ∫ x in (Icc (-a) a)ᶜ, C * Real.exp (-(b * x ^ 2))
      = C * ∫ x in (Icc (-a) a)ᶜ, Real.exp (-(b * x ^ 2)) := integral_const_mul _ _
  rw [hval] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left (integral_compl_Icc_expNegSq_le hb ha) hC)

end GaloisForLFunctions

end
