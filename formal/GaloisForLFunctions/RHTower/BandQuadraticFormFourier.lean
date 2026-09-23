import GaloisForLFunctions.RHTower.CCMEndpointResponseIdentity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The band quadratic form is a Fourier energy

The smoothed sinc kernel is an average of cosines over the band,

```text
sinc_c(x - y) = (c/(2 pi)) ∫_(-1)^(1 : ℕ) cos(c t (x - y)) dt,
```

and the cosine factorisation turns each cosine double integral into the squared modulus of a
finite-Fourier transform.  Averaging in `t` therefore expresses the band quadratic form of a
continuous test function as an energy,

```text
∫∫ sinc_c(x-y) psi(x) psi(y) dx dy = (c/(2 pi)) ∫_(-1)^(1 : ℕ) ‖F_(c t) psi‖² dt,
```

which in particular is nonnegative: the band form is positive semidefinite.  The identity is the
operator-level reading of the kernel identity `(6)`, and the positivity is what makes the largest band
eigenvalue a maximum of a nonnegative Rayleigh quotient.

The only analytic step is Fubini on the box `[-1,1]² × [-1,1]`, where the integrand is continuous and
bounded, so integrability comes from a product of an integrable function of the separate variables
with a bounded measurable factor.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

open _root_.RHTower

/-- `∫_(-1)^(1 : ℕ) cos (a t) dt` in closed form. -/
theorem integral_cos_mul_unit (a : ℝ) (ha : a ≠ 0) :
    (∫ t in (-1 : ℝ)..1, Real.cos (a * t)) = 2 * Real.sin a / a := by
  have halg : (a : ℝ)⁻¹ * (Real.sin a + Real.sin a) = 2 * Real.sin a / a := by
    rw [div_eq_inv_mul]
    ring
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) ha, integral_cos,
    mul_neg_one, mul_one, Real.sin_neg, smul_eq_mul, sub_neg_eq_add, halg]

/-- **The real cosine form of the smoothed sinc kernel.**  The kernel is the average of the cosine
characters over the band. -/
theorem sincKernelSmooth_eq_cos_integral (c x y : ℝ) :
    sincKernelSmooth c x y
      = (c / (2 * Real.pi)) * ∫ t in (-1 : ℝ)..1, Real.cos (c * (x - y) * t) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases eq_or_ne (c * (x - y)) 0 with ha | ha
  · -- degenerate frequency: both sides are the value at the removable singularity
    rw [ha]
    simp only [zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul]
    rcases eq_or_ne c 0 with hc | hc
    · subst hc
      have hz : sincSmooth 0 (x - y) = 0 := by
        have : (fun u : ℝ => Real.sin (0 * u) / Real.pi) = fun _ : ℝ => 0 := by
          funext u
          simp
        have hzero : dslope (fun _ : ℝ => (0 : ℝ)) 0 = fun _ => 0 := by
          funext u
          rcases eq_or_ne u 0 with rfl | hu
          · rw [dslope_same]
            simp
          · rw [dslope_of_ne _ hu, slope_def_field]
            simp
        rw [sincSmooth, this, hzero]
      rw [sincKernelSmooth, hz]
      ring
    · have hxy : x - y = 0 := by
        rcases mul_eq_zero.mp ha with h | h
        · exact absurd h hc
        · exact h
      rw [sincKernelSmooth, hxy, sincSmooth_zero]
      ring
  · have hxy : x - y ≠ 0 := by
      intro h
      rw [h, mul_zero] at ha
      exact ha rfl
    have hc : c ≠ 0 := by
      intro h
      rw [h, zero_mul] at ha
      exact ha rfl
    rw [sincKernelSmooth, sincSmooth_eq_off hxy, sincScalar,
      integral_cos_mul_unit (c * (x - y)) ha]
    field_simp

/-! ## Integrability on the box -/

/-- The cosine integrand of the band form is integrable on the product of the band with itself. -/
theorem integrable_cos_box (c t : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) (a b : ℝ) :
    Integrable (Function.uncurry fun x y : ℝ => Real.cos (c * (x - y) * t) * (ψ x * ψ y))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
  have hψint : Integrable ψ (volume.restrict (Ioc a b)) := by
    exact hψ.integrableOn_Ioc
  have hprod : Integrable (fun z : ℝ × ℝ => ψ z.1 * ψ z.2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := hψint.mul_prod hψint
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => Real.cos (c * (z.1 - z.2) * t))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have hbdd : Integrable (fun z : ℝ × ℝ =>
      Real.cos (c * (z.1 - z.2) * t) * (ψ z.1 * ψ z.2))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) :=
    hprod.bdd_mul (c := 1) hmeas
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _)
  exact hbdd

/-! ## The band form as an energy -/

/-- The inner double integral of the cosine form, evaluated by the cosine factorisation. -/
theorem double_integral_cos_scaled (c t : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, Real.cos (c * (x - y) * t) * (ψ x * ψ y))
      = ‖bandFourier (c * t) ψ‖ ^ (2 : ℕ) := by
  have hcongr : (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      Real.cos (c * (x - y) * t) * (ψ x * ψ y))
      = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * t * (x - y)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    refine intervalIntegral.integral_congr fun y _ => ?_
    have hfreq : c * (x - y) * t = c * t * (x - y) := by ring
    rw [hfreq]
    ring
  rw [hcongr, double_integral_cos_eq_norm_sq (c * t) hψ]

/-- Fubini for a jointly continuous integrand on a box, in interval-integral form. -/
theorem swap_interval_integral {F : ℝ → ℝ → ℝ}
    (hF : Continuous fun z : ℝ × ℝ => F z.1 z.2)
    {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v) :
    (∫ y in a..b, ∫ t in u..v, F y t) = ∫ t in u..v, ∫ y in a..b, F y t := by
  have hcompact : IsCompact (Icc a b ×ˢ Icc u v) := isCompact_Icc.prod isCompact_Icc
  have hFu : Continuous (Function.uncurry F) := hF
  have hint0 : IntegrableOn (Function.uncurry F) (Icc a b ×ˢ Icc u v)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (hFu.continuousOn).integrableOn_compact hcompact
  have hsub : Ioc a b ×ˢ Ioc u v ⊆ Icc a b ×ˢ Icc u v := by
    intro z hz
    exact ⟨Ioc_subset_Icc_self hz.1, Ioc_subset_Icc_self hz.2⟩
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc u v))) := by
    rw [Measure.prod_restrict]
    exact hint0.mono_set hsub
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le huv]
  exact integral_integral_swap hint

/-- **The band quadratic form is a Fourier energy.**  Averaging the cosine factorisation over the band
turns the sinc double integral into an average of squared finite-Fourier moduli. -/
theorem double_integral_sincKernel_eq_energy (c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * (ψ x * ψ y))
      = (c / (2 * Real.pi)) * ∫ t in (-1 : ℝ)..1, ‖bandFourier (c * t) ψ‖ ^ (2 : ℕ) := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have hinner : ∀ x y : ℝ, sincKernelSmooth c x y * (ψ x * ψ y)
      = (c / (2 * Real.pi)) * ∫ t in (-1 : ℝ)..1, Real.cos (c * (x - y) * t) * (ψ x * ψ y) := by
    intro x y
    rw [sincKernelSmooth_eq_cos_integral c x y, intervalIntegral.integral_mul_const]
    ring
  have hcontH : Continuous fun z : ℝ × ℝ =>
      ∫ y in Icc (-1 : ℝ) 1, Real.cos (c * (z.1 - y) * z.2) * (ψ z.1 * ψ y) := by
    refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
    have hc : Continuous fun w : (ℝ × ℝ) × ℝ => Real.cos (c * (w.1.1 - w.2) * w.1.2) := by
      fun_prop
    have hp : Continuous fun w : (ℝ × ℝ) × ℝ => ψ w.1.1 * ψ w.2 := by fun_prop
    exact hc.mul hp
  have hIcc : ∀ x t : ℝ, (∫ y in (-1 : ℝ)..1, Real.cos (c * (x - y) * t) * (ψ x * ψ y))
      = ∫ y in Icc (-1 : ℝ) 1, Real.cos (c * (x - y) * t) * (ψ x * ψ y) := by
    intro x t
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  calc (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * (ψ x * ψ y))
      = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, (c / (2 * Real.pi)) *
          ∫ t in (-1 : ℝ)..1, Real.cos (c * (x - y) * t) * (ψ x * ψ y) := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        refine intervalIntegral.integral_congr fun y _ => ?_
        exact hinner x y
    _ = (c / (2 * Real.pi)) * ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
          ∫ t in (-1 : ℝ)..1, Real.cos (c * (x - y) * t) * (ψ x * ψ y) := by
        simp only [intervalIntegral.integral_const_mul]
    _ = (c / (2 * Real.pi)) * ∫ x in (-1 : ℝ)..1, ∫ t in (-1 : ℝ)..1,
          ∫ y in (-1 : ℝ)..1, Real.cos (c * (x - y) * t) * (ψ x * ψ y) := by
        congr 1
        refine intervalIntegral.integral_congr fun x _ => ?_
        refine swap_interval_integral ?_ hle hle
        have hc : Continuous fun z : ℝ × ℝ => Real.cos (c * (x - z.1) * z.2) := by fun_prop
        have hp : Continuous fun z : ℝ × ℝ => ψ x * ψ z.1 := by fun_prop
        exact hc.mul hp
    _ = (c / (2 * Real.pi)) * ∫ t in (-1 : ℝ)..1, ∫ x in (-1 : ℝ)..1,
          ∫ y in (-1 : ℝ)..1, Real.cos (c * (x - y) * t) * (ψ x * ψ y) := by
        congr 1
        have hrewrite : ∀ x t : ℝ, (∫ y in (-1 : ℝ)..1, Real.cos (c * (x - y) * t) * (ψ x * ψ y))
            = (fun z : ℝ × ℝ => ∫ y in Icc (-1 : ℝ) 1,
                Real.cos (c * (z.1 - y) * z.2) * (ψ z.1 * ψ y)) (x, t) := fun x t => hIcc x t
        simp only [hrewrite]
        exact swap_interval_integral hcontH hle hle
    _ = (c / (2 * Real.pi)) * ∫ t in (-1 : ℝ)..1, ‖bandFourier (c * t) ψ‖ ^ (2 : ℕ) := by
        congr 1
        refine intervalIntegral.integral_congr fun t _ => ?_
        exact double_integral_cos_scaled c t hψ

/-- **The band quadratic form is nonnegative** for every nonnegative aperture. -/
theorem double_integral_sincKernel_nonneg {c : ℝ} (hc : 0 ≤ c) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    0 ≤ ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * (ψ x * ψ y) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [double_integral_sincKernel_eq_energy c hψ]
  have hnonneg : 0 ≤ ∫ t in (-1 : ℝ)..1, ‖bandFourier (c * t) ψ‖ ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun t _ => ?_
    positivity
  positivity

end GaloisForLFunctions.RHTower

end
