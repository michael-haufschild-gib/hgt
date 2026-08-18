import Mathlib
import GaloisForLFunctions.HTGeometry.HalfPlaneCauchyRepresentation

/-!
# The Mellin representation of a decaying half-plane function

A function analytic on `Re s ≥ 1` with `‖φ s‖ ≤ C/‖s‖²` there is the Mellin transform of a bounded
density that vanishes at infinity:

```text
φ(s) = ∫_1^∞ q(x) x^{-s} dx ,      q(x) = (1/2π) ∫_R φ(1 + i t) x^{i t} dt ,
```

with `‖q‖ ≤ C/2` and `q(x) → 0` as `x → ∞`.  The identity is Fubini plus the half-plane Cauchy
representation; the decay is the Riemann--Lebesgue lemma.

This is the half of Andersson's Lemma 1 that follows once the Arakelyan step has produced the
entire approximant.
-/

noncomputable section

open Complex MeasureTheory Filter Set

namespace GaloisForLFunctions.HTGeometry

/-- The boundary density of the Mellin representation. -/
def mellinDensity (φ : ℂ → ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ (t : ℝ), Complex.exp ((t : ℂ) * I * (Real.log x : ℂ)) * φ ((1 : ℂ) + (t : ℂ) * I)

theorem cpow_ofReal_mul_I {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x : ℂ) ^ ((t : ℂ) * I) = Complex.exp ((t : ℂ) * I * (Real.log x : ℂ)) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hx
  rw [Complex.cpow_def_of_ne_zero hxne, ← Complex.ofReal_log hx.le, mul_comm]

theorem continuous_boundary {φ : ℂ → ℂ} (hφ : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z) :
    Continuous fun t : ℝ => φ ((1 : ℂ) + (t : ℂ) * I) :=
  (continuousOn_of_analyticOn_halfPlane hφ).comp_continuous continuous_lineParam
    (fun t => by simp [Set.mem_setOf_eq])

theorem norm_boundary_le {φ : ℂ → ℂ} {C : ℝ}
    (hbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ C / ‖z‖ ^ 2) (t : ℝ) :
    ‖φ ((1 : ℂ) + (t : ℂ) * I)‖ ≤ C / (1 + t ^ 2) := by
  have h := hbound ((1 : ℂ) + (t : ℂ) * I) (by rw [re_one_add_mul_I])
  rwa [norm_one_add_mul_I_sq] at h

theorem integrable_boundary {φ : ℂ → ℂ} {C : ℝ}
    (hφ : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z)
    (hbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ C / ‖z‖ ^ 2) :
    Integrable fun t : ℝ => φ ((1 : ℂ) + (t : ℂ) * I) := by
  have henv : Integrable fun t : ℝ => C / (1 + t ^ 2) := by
    have heq : (fun t : ℝ => C / (1 + t ^ 2)) = fun t : ℝ => C * (1 + t ^ 2)⁻¹ := by
      funext t
      field_simp
    rw [heq]
    exact integrable_inv_one_add_sq.const_mul C
  refine Integrable.mono' henv (continuous_boundary hφ).aestronglyMeasurable ?_
  filter_upwards with t
  exact norm_boundary_le hbound t

theorem mellinDensity_mul_cpow {φ : ℂ → ℂ} {x : ℝ} (hx : 0 < x) (s : ℂ) :
    mellinDensity φ x * (x : ℂ) ^ (-s)
      = (1 / (2 * Real.pi) : ℂ) *
        ∫ (t : ℝ), φ ((1 : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((t : ℂ) * I - s) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hx
  have hterm : ∀ t : ℝ,
      Complex.exp ((t : ℂ) * I * (Real.log x : ℂ)) * φ ((1 : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ (-s)
        = φ ((1 : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((t : ℂ) * I - s) := by
    intro t
    rw [← cpow_ofReal_mul_I hx t, Complex.cpow_sub _ _ hxne, Complex.cpow_neg, div_eq_mul_inv]
    ring
  rw [mellinDensity, mul_assoc]
  congr 1
  rw [← MeasureTheory.integral_mul_const]
  exact integral_congr_ae (Filter.Eventually.of_forall hterm)

theorem continuousOn_mellinIntegrand (φ : ℂ → ℂ) (hφ : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z)
    (s : ℂ) :
    ContinuousOn
      (Function.uncurry fun (x : ℝ) (t : ℝ) =>
        φ ((1 : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((t : ℂ) * I - s))
      (Ioi (1:ℝ) ×ˢ (univ : Set ℝ)) := by
  have hnum : ContinuousOn
      (fun z : ℝ × ℝ => φ ((1 : ℂ) + (z.2 : ℂ) * I)) (Ioi (1:ℝ) ×ˢ (univ : Set ℝ)) :=
    ((continuous_boundary hφ).comp continuous_snd).continuousOn
  have hlog : ContinuousOn (fun z : ℝ × ℝ => Complex.log ((z.1 : ℝ) : ℂ))
      (Ioi (1:ℝ) ×ˢ (univ : Set ℝ)) := by
    intro z hz
    have hz1 : (1:ℝ) < z.1 := by
      rw [Set.mem_prod] at hz
      exact hz.1
    have hslit : ((z.1 : ℝ) : ℂ) ∈ Complex.slitPlane := by
      refine Or.inl ?_
      simpa using by linarith
    exact ((Complex.continuousAt_log hslit).comp
      (Complex.continuous_ofReal.continuousAt.comp continuousAt_fst)).continuousWithinAt
  have hexp : ContinuousOn
      (fun z : ℝ × ℝ => Complex.exp (Complex.log ((z.1 : ℝ) : ℂ) * ((z.2 : ℂ) * I - s)))
      (Ioi (1:ℝ) ×ˢ (univ : Set ℝ)) := by
    refine Complex.continuous_exp.comp_continuousOn (hlog.mul ?_)
    exact ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const).continuousOn.sub
      continuousOn_const
  refine (hnum.mul hexp).congr ?_
  intro z hz
  have hz1 : (1:ℝ) < z.1 := by
    rw [Set.mem_prod] at hz
    exact hz.1
  have hxne : ((z.1 : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt (by linarith : (0:ℝ) < z.1)
  simp only [Function.uncurry]
  rw [Complex.cpow_def_of_ne_zero hxne]

end GaloisForLFunctions.HTGeometry

end
