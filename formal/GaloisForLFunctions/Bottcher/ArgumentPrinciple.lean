/-
# The argument principle on a disk (built on our own Cauchy machinery)

`Period.lean` already gives our Cauchy theorem on a disk — `period_point_inside`
(`∮ (z−w)⁻¹ = 2πi`) and the `DiffContOnCl.circleIntegral_eq_zero` route of `period_point_outside`.
The argument principle is assembled from exactly these:

* `circleIntegral_logDeriv_eq_zero` — a nonvanishing holomorphic `h` has winding number `0`;
* `circleIntegral_logDeriv_simple_zero` — a single simple zero inside gives winding number `1`
  (`∮ h'/h = 2πi`), the degree-1 / winding-number count.

These are the disk-level core of the `λ`-univalence degree count (applied to `h = λ − w`, whose
zeros are simple because `λ' ≠ 0`).
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import GaloisForLFunctions.Bottcher.Period
import Mathlib.Analysis.Complex.RemovableSingularity
open Complex Metric

namespace Bottcher

/-- **Argument principle, no-zeros case.** `h` analytic on a neighbourhood of `closedBall c R` and
nonvanishing there ⟹ `∮_{C(c,R)} h'/h = 0`. Reuses our Cauchy theorem `DiffContOnCl.circleIntegral_eq_zero`
exactly as `period_point_outside` does. -/
theorem circleIntegral_logDeriv_eq_zero {h : ℂ → ℂ} {c : ℂ} {R : ℝ} {U : Set ℂ}
    (hR : 0 ≤ R) (_hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    (hh : AnalyticOnNhd ℂ h U) (hne : ∀ z ∈ closedBall c R, h z ≠ 0) :
    (∮ z in C(c, R), deriv h z / h z) = 0 := by
  apply DiffContOnCl.circleIntegral_eq_zero hR
  apply DifferentiableOn.diffContOnCl
  intro z hz
  have hz' : z ∈ closedBall c R := closure_ball_subset_closedBall hz
  have hzU : z ∈ U := hsub hz'
  have hda : AnalyticAt ℂ (fun w => deriv h w / h w) z :=
    ((hh.deriv z hzU).div (hh z hzU) (hne z hz'))
  exact hda.differentiableAt.differentiableWithinAt

end Bottcher

namespace Bottcher

/-- **Argument principle, single simple zero = winding number 1 (degree-1 count).** If `h = (·−z₀)·u`
on a neighbourhood `U ⊇ closedBall c R`, with `u` analytic and nonvanishing and `z₀ ∈ ball c R`, then
`∮_{C(c,R)} h'/h = 2πi`: `h` has exactly one (simple) zero inside, so the winding number is `1`. -/
theorem circleIntegral_logDeriv_simple_zero {h u : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ} {U : Set ℂ}
    (hR : 0 ≤ R) (hU : IsOpen U) (hsub : closedBall c R ⊆ U) (hz₀ : z₀ ∈ ball c R)
    (hu : AnalyticOnNhd ℂ u U) (huh : ∀ z ∈ U, h z = (z - z₀) * u z)
    (hune : ∀ z ∈ closedBall c R, u z ≠ 0) :
    (∮ z in C(c, R), deriv h z / h z) = 2 * (Real.pi : ℂ) * Complex.I := by
  have hz₀cb : z₀ ∈ closedBall c R := ball_subset_closedBall hz₀
  -- product rule: deriv h = u + (·-z₀)·u' on U
  have hderiv_h : ∀ z ∈ U, deriv h z = u z + (z - z₀) * deriv u z := by
    intro z hz
    have hee : h =ᶠ[nhds z] fun w => (w - z₀) * u w := by
      filter_upwards [hU.mem_nhds hz] with w hw using huh w hw
    rw [hee.deriv_eq]
    have h1 : HasDerivAt (fun w => (w - z₀) * u w)
        (1 * u z + (z - z₀) * deriv u z) z :=
      ((hasDerivAt_id z).sub_const z₀).mul ((hu z hz).differentiableAt.hasDerivAt)
    rw [h1.deriv]; ring
  -- on the sphere, h'/h = (z-z₀)⁻¹ + u'/u
  have key : ∀ z ∈ sphere c R, deriv h z / h z = (z - z₀)⁻¹ + deriv u z / u z := by
    intro z hz
    have hzcb : z ∈ closedBall c R := sphere_subset_closedBall hz
    have hzU : z ∈ U := hsub hzcb
    have hzz₀ : z - z₀ ≠ 0 := by
      rw [sub_ne_zero]; rintro rfl
      exact absurd (Metric.mem_sphere.mp hz) (Metric.mem_ball.mp hz₀).ne
    have huz : u z ≠ 0 := hune z hzcb
    rw [hderiv_h z hzU, huh z hzU]
    field_simp
  rw [circleIntegral.integral_congr hR key]
  -- split the integral
  have hci1 : CircleIntegrable (fun z : ℂ => (z - z₀)⁻¹) c R := by
    apply ContinuousOn.circleIntegrable hR
    apply ((continuous_sub_right z₀).continuousOn).inv₀
    intro z hz
    rw [sub_ne_zero]; rintro rfl
    exact absurd (Metric.mem_sphere.mp hz) (Metric.mem_ball.mp hz₀).ne
  have hci2 : CircleIntegrable (fun z : ℂ => deriv u z / u z) c R := by
    apply ContinuousOn.circleIntegrable hR
    intro z hz
    have hzU : z ∈ U := hsub (sphere_subset_closedBall hz)
    exact (((hu.deriv z hzU).div (hu z hzU) (hune z (sphere_subset_closedBall hz))
      ).continuousAt).continuousWithinAt
  rw [circleIntegral.integral_add hci1 hci2, period_point_inside hz₀,
    circleIntegral_logDeriv_eq_zero hR hU hsub hu hune, add_zero]

end Bottcher


namespace Bottcher

/-- **Simple-zero factoring** (divided difference). Analytic `h` with `h z₀ = 0` factors globally as
`h z = (z − z₀) · (dslope h z₀ z)`, with `dslope h z₀` analytic at `z₀` and value `h'(z₀)` there. -/
theorem analyticAt_simple_factor {h : ℂ → ℂ} {z₀ : ℂ} (hh : AnalyticAt ℂ h z₀) (h0 : h z₀ = 0) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ (∀ z, h z = (z - z₀) * u z) ∧ u z₀ = deriv h z₀ := by
  have hso : IsOpen {z | AnalyticAt ℂ h z} := isOpen_analyticAt ℂ h
  have hz₀s : z₀ ∈ {z | AnalyticAt ℂ h z} := hh
  have hdiff : DifferentiableOn ℂ h {z | AnalyticAt ℂ h z} :=
    fun z hz => hz.differentiableAt.differentiableWithinAt
  have hdslope : DifferentiableOn ℂ (dslope h z₀) {z | AnalyticAt ℂ h z} :=
    (differentiableOn_dslope (hso.mem_nhds hz₀s)).mpr hdiff
  refine ⟨dslope h z₀, hdslope.analyticAt (hso.mem_nhds hz₀s), fun z => ?_, dslope_same h z₀⟩
  have hs := sub_smul_dslope h z₀ z
  rw [h0, sub_zero, smul_eq_mul] at hs
  exact hs.symm

/-- **Argument principle, single simple zero (directly applicable form).** `h` analytic on an open
`U ⊇ closedBall c R`, with a simple zero at `z₀ ∈ ball c R` (`h z₀ = 0`, `h' z₀ ≠ 0`) and no other
zero in `closedBall c R`, has `∮_{C(c,R)} h'/h = 2πi`. -/
theorem circleIntegral_logDeriv_eq_two_pi_I {h : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ} {U : Set ℂ}
    (hR : 0 ≤ R) (hU : IsOpen U) (hsub : closedBall c R ⊆ U) (hz₀ : z₀ ∈ ball c R) (hz₀U : z₀ ∈ U)
    (hh : AnalyticOnNhd ℂ h U) (hz₀zero : h z₀ = 0) (hsimple : deriv h z₀ ≠ 0)
    (hne : ∀ z ∈ closedBall c R, z ≠ z₀ → h z ≠ 0) :
    (∮ z in C(c, R), deriv h z / h z) = 2 * (Real.pi : ℂ) * Complex.I := by
  have hdiffU : DifferentiableOn ℂ h U :=
    fun z hz => (hh z hz).differentiableAt.differentiableWithinAt
  have huU : AnalyticOnNhd ℂ (dslope h z₀) U :=
    fun z hz => ((differentiableOn_dslope (hU.mem_nhds hz₀U)).mpr hdiffU).analyticAt (hU.mem_nhds hz)
  have hfact : ∀ z ∈ U, h z = (z - z₀) * dslope h z₀ z := by
    intro z _
    have hs := sub_smul_dslope h z₀ z
    rw [hz₀zero, sub_zero, smul_eq_mul] at hs
    exact hs.symm
  have hune : ∀ z ∈ closedBall c R, dslope h z₀ z ≠ 0 := by
    intro z hz
    rcases eq_or_ne z z₀ with rfl | hz'
    · rw [dslope_same]; exact hsimple
    · rw [dslope_of_ne _ hz', slope_def_field, hz₀zero, sub_zero]
      exact div_ne_zero (hne z hz hz') (sub_ne_zero.mpr hz')
  exact circleIntegral_logDeriv_simple_zero hR hU hsub hz₀ huU hfact hune

end Bottcher
