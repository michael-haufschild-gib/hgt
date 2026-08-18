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
    have h1 : ContinuousAt (fun w : ℝ × ℝ => ((w.1 : ℝ) : ℂ)) z :=
      (Complex.continuous_ofReal.comp continuous_fst).continuousAt
    exact (h1.clog hslit).continuousWithinAt
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
  simp only [Function.uncurry, Pi.mul_apply]
  rw [Complex.cpow_def_of_ne_zero hxne]

theorem integrable_mellinIntegrand {φ : ℂ → ℂ} {C : ℝ}
    (hφ : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z)
    (hbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ C / ‖z‖ ^ 2)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (Function.uncurry fun (x : ℝ) (t : ℝ) =>
        φ ((1 : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ ((t : ℂ) * I - s))
      ((volume.restrict (Ioi (1:ℝ))).prod volume) := by
  have hms : (volume.restrict (Ioi (1:ℝ))).prod (volume : Measure ℝ)
      = (volume.prod volume).restrict (Ioi (1:ℝ) ×ˢ (univ : Set ℝ)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have henv : Integrable fun t : ℝ => C / (1 + t ^ 2) := by
    have heq : (fun t : ℝ => C / (1 + t ^ 2)) = fun t : ℝ => C * (1 + t ^ 2)⁻¹ := by
      funext t
      field_simp
    rw [heq]
    exact integrable_inv_one_add_sq.const_mul C
  rw [hms]
  refine Integrable.mono'
    (g := fun z : ℝ × ℝ => z.1 ^ (-s.re) * (C / (1 + z.2 ^ 2))) ?_ ?_ ?_
  · rw [← hms]
    exact Integrable.mul_prod (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) henv
  · exact (continuousOn_mellinIntegrand φ hφ s).aestronglyMeasurable
      (measurableSet_Ioi.prod MeasurableSet.univ)
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with z hz
    have hz1 : (1:ℝ) < z.1 := by
      rw [Set.mem_prod] at hz
      exact hz.1
    have hzpos : (0:ℝ) < z.1 := by linarith
    have hre : ((z.2 : ℂ) * I - s).re = -s.re := by simp
    simp only [Function.uncurry]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hzpos, hre, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_boundary_le hbound z.2)
      (Real.rpow_nonneg hzpos.le _)

/-- **The Mellin representation.** -/
theorem integral_mellinDensity_eq {φ : ℂ → ℂ} {C : ℝ}
    (hφ : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z)
    (hbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ C / ‖z‖ ^ 2)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1:ℝ), mellinDensity φ x * (x : ℂ) ^ (-s)) = φ s := by
  have hrw : (∫ x in Ioi (1:ℝ), mellinDensity φ x * (x : ℂ) ^ (-s))
      = (1 / (2 * Real.pi) : ℂ) *
        ∫ x in Ioi (1:ℝ), ∫ (t : ℝ), φ ((1:ℂ) + (t:ℂ) * I) * (x : ℂ) ^ ((t : ℂ) * I - s) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hxpos : (0:ℝ) < x := lt_trans one_pos hx
    exact mellinDensity_mul_cpow hxpos s
  have hswap := MeasureTheory.integral_integral_swap (integrable_mellinIntegrand hφ hbound hs)
  have hinner : ∀ t : ℝ,
      (∫ x in Ioi (1:ℝ), φ ((1:ℂ) + (t:ℂ) * I) * (x : ℂ) ^ ((t : ℂ) * I - s))
        = -(lineKernel φ s t) := by
    intro t
    have hlt : ((t : ℂ) * I - s).re < -1 := by
      have : ((t : ℂ) * I - s).re = -s.re := by simp
      rw [this]
      linarith
    rw [MeasureTheory.integral_const_mul, integral_Ioi_cpow_of_lt hlt one_pos]
    have hone : ((1:ℝ) : ℂ) ^ ((t : ℂ) * I - s + 1) = 1 := by
      rw [Complex.ofReal_one, Complex.one_cpow]
    rw [hone]
    have hden : (t : ℂ) * I - s + 1 = ((1:ℂ) + (t:ℂ) * I) - s := by ring
    rw [hden, lineKernel]
    ring
  rw [hrw, hswap]
  simp_rw [hinner]
  rw [MeasureTheory.integral_neg, halfPlane_cauchy_representation hφ hbound hs]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp

theorem norm_exp_mul_I_mul_real (t u : ℝ) : ‖Complex.exp ((t : ℂ) * I * (u : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : ((t : ℂ) * I * (u : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

/-- The density is bounded, uniformly in `x`. -/
theorem norm_mellinDensity_le (φ : ℂ → ℂ) (x : ℝ) :
    ‖mellinDensity φ x‖ ≤ (1 / (2 * Real.pi)) * ∫ (t : ℝ), ‖φ ((1 : ℂ) + (t : ℂ) * I)‖ := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [mellinDensity, norm_mul, hc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_))
  simp only [norm_mul, norm_exp_mul_I_mul_real, one_mul]

/-- **Riemann–Lebesgue: the density vanishes at infinity.** -/
theorem tendsto_mellinDensity_atTop (φ : ℂ → ℂ) :
    Tendsto (fun x : ℝ => mellinDensity φ x) atTop (nhds 0) := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hRL := Real.tendsto_integral_exp_smul_cocompact (fun v : ℝ => φ ((1 : ℂ) + (v : ℂ) * I))
  have hlog : Tendsto (fun x : ℝ => -(Real.log x)) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp Real.tendsto_log_atTop
  have hw : Tendsto (fun x : ℝ => -(Real.log x) / (2 * Real.pi)) atTop atBot :=
    hlog.atBot_div_const hpi
  have hw' : Tendsto (fun x : ℝ => -(Real.log x) / (2 * Real.pi)) atTop (Filter.cocompact ℝ) :=
    hw.mono_right atBot_le_cocompact
  have hcomp := hRL.comp hw'
  have heq : ∀ x : ℝ,
      (∫ (v : ℝ), (Real.fourierChar (-(v * (-(Real.log x) / (2 * Real.pi))))) •
          φ ((1 : ℂ) + (v : ℂ) * I))
        = ∫ (v : ℝ), Complex.exp ((v : ℂ) * I * (Real.log x : ℂ)) * φ ((1 : ℂ) + (v : ℂ) * I) := by
    intro x
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    congr 2
    push_cast
    field_simp
  have hcomp' : Tendsto (fun x : ℝ =>
      ∫ (v : ℝ), Complex.exp ((v : ℂ) * I * (Real.log x : ℂ)) * φ ((1 : ℂ) + (v : ℂ) * I))
      atTop (nhds 0) := by
    refine hcomp.congr fun x => ?_
    exact heq x
  have := hcomp'.const_mul (1 / (2 * Real.pi) : ℂ)
  simpa [mellinDensity] using this

end GaloisForLFunctions.HTGeometry

end
