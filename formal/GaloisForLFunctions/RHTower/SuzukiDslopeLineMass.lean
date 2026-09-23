import GaloisForLFunctions.RHTower.SuzukiDslopeLineMajorant
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

/-!
# The mass of `F_γ` on horizontal lines

Integrating the uniform Cauchy profile gives, for every horizontal line in the closed upper
half-plane, both square-integrability of `F_γ` along the line and the height-free bound

```text
∫ ‖dslope (A/E) γ (x + iy)‖² dx ≤ 2C²π.
```

These are exactly the two analytic hypotheses of the corpus's Hardy-space predicate for a
half-plane; holomorphy is already available.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

theorem continuous_dslope_line (hRH : RiemannHypothesis) {γ : ℂ} (hγ : XiC γ = 0)
    {y : ℝ} (hy : 0 ≤ y) :
    Continuous fun x : ℝ => dslope suzukiHalfInner γ ((x : ℂ) + (y : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hz : (0 : ℝ) ≤ (((x : ℂ) + (y : ℂ) * I)).im := by simpa using hy
  have hd := differentiableAt_dslope_suzukiHalfInner_of_rh hRH hγ hz
  have hc : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) :=
    Complex.continuous_ofReal.add continuous_const
  exact ContinuousAt.comp (g := dslope suzukiHalfInner γ)
    (f := fun x : ℝ => (x : ℂ) + (y : ℂ) * I) hd.continuousAt hc.continuousAt

theorem integrable_lineMajorant (a : ℝ) (D : ℝ) :
    Integrable (fun x : ℝ => D / (1 + (x - a) ^ (2 : ℕ))) volume := by
  have hbase : Integrable (fun x : ℝ => (1 + (x - a) ^ (2 : ℕ))⁻¹) volume :=
    integrable_inv_one_add_sq.comp_sub_right a
  refine (hbase.const_mul D).congr ?_
  filter_upwards with x
  rw [div_eq_mul_inv]

theorem integral_lineMajorant (a : ℝ) (D : ℝ) :
    (∫ x : ℝ, D / (1 + (x - a) ^ (2 : ℕ))) = D * Real.pi := by
  have hfun : (fun x : ℝ => D / (1 + (x - a) ^ (2 : ℕ)))
      = fun x : ℝ => D * (1 + (x - a) ^ (2 : ℕ))⁻¹ := by
    funext x
    rw [div_eq_mul_inv]
  rw [hfun, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self (fun x : ℝ => (1 + x ^ (2 : ℕ))⁻¹) a,
    integral_univ_inv_one_add_sq]

theorem memLp_dslope_line (hRH : RiemannHypothesis) {γ : ℂ} (hγ : XiC γ = 0) {C : ℝ}
    (hC1 : 1 ≤ C) (hCb : ∀ z : ℂ, 0 ≤ z.im → ‖dslope suzukiHalfInner γ z‖ ≤ C)
    {y : ℝ} (hy : 0 ≤ y) :
    MemLp (fun x : ℝ => dslope suzukiHalfInner γ ((x : ℂ) + (y : ℂ) * I)) 2
      (volume : Measure ℝ) := by
  refine (memLp_two_iff_integrable_sq_norm
    (continuous_dslope_line hRH hγ hy).aestronglyMeasurable).mpr ?_
  refine Integrable.mono' (integrable_lineMajorant γ.re (2 * C ^ (2 : ℕ)))
    ((continuous_dslope_line hRH hγ hy).aestronglyMeasurable.norm.pow 2) ?_
  filter_upwards with x
  have hz : (0 : ℝ) ≤ (((x : ℂ) + (y : ℂ) * I)).im := by simpa using hy
  have hb := norm_sq_dslope_le_lineMajorant hRH hγ hC1 hCb hz
  have hre : (((x : ℂ) + (y : ℂ) * I)).re = x := by simp
  rw [hre] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hb

/-- **The mass of `F_γ` on every horizontal line is uniformly bounded.** -/
theorem integral_norm_sq_dslope_line_le (hRH : RiemannHypothesis) {γ : ℂ} (hγ : XiC γ = 0)
    {C : ℝ} (hC1 : 1 ≤ C)
    (hCb : ∀ z : ℂ, 0 ≤ z.im → ‖dslope suzukiHalfInner γ z‖ ≤ C) {y : ℝ} (hy : 0 ≤ y) :
    (∫ x : ℝ, ‖dslope suzukiHalfInner γ ((x : ℂ) + (y : ℂ) * I)‖ ^ (2 : ℕ))
      ≤ 2 * C ^ (2 : ℕ) * Real.pi := by
  have hint : Integrable
      (fun x : ℝ => ‖dslope suzukiHalfInner γ ((x : ℂ) + (y : ℂ) * I)‖ ^ (2 : ℕ)) volume :=
    (memLp_two_iff_integrable_sq_norm
      (continuous_dslope_line hRH hγ hy).aestronglyMeasurable).mp
        (memLp_dslope_line hRH hγ hC1 hCb hy)
  have hmono : ∀ x : ℝ,
      ‖dslope suzukiHalfInner γ ((x : ℂ) + (y : ℂ) * I)‖ ^ (2 : ℕ)
        ≤ 2 * C ^ (2 : ℕ) / (1 + (x - γ.re) ^ (2 : ℕ)) := by
    intro x
    have hz : (0 : ℝ) ≤ (((x : ℂ) + (y : ℂ) * I)).im := by simpa using hy
    have hb := norm_sq_dslope_le_lineMajorant hRH hγ hC1 hCb hz
    have hre : (((x : ℂ) + (y : ℂ) * I)).re = x := by simp
    rwa [hre] at hb
  refine le_trans (MeasureTheory.integral_mono hint
    (integrable_lineMajorant γ.re (2 * C ^ (2 : ℕ))) hmono) ?_
  rw [integral_lineMajorant]

end RHTower
