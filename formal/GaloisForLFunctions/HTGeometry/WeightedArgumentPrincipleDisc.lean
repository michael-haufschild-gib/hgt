import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The argument principle on a disc, with a polynomial weight

For a function presented on a neighbourhood of a closed disc as a finite product of powers of
linear factors times a nowhere vanishing factor, the weighted logarithmic-derivative integral

`∮_{|ζ|=t} ζ^p (f'/f)(ζ) dζ = 2πi ∑_u m_u u^p`

picks out exactly the `p`-th power sums of the zeros, counted with multiplicity.  The nonvanishing
factor contributes nothing by Cauchy's theorem, and each linear factor contributes by Cauchy's
integral formula applied to `z ↦ z^p`.

This is the residue computation behind Weierstrass' preparation theorem: with `p` ranging over the
nonnegative integers it identifies the parameter-holomorphic moments with the power sums of the
roots of a slice.

* `HTGeometry.logDeriv_sub_pow`;
* `HTGeometry.circleIntegral_finset_sum`;
* `HTGeometry.circleIntegral_weighted_logDeriv_prod`.
-/

open Complex Metric
open scoped Real

namespace HTGeometry

/-- The logarithmic derivative of a power of a linear factor. -/
theorem logDeriv_sub_pow (u : ℂ) (k : ℕ) (x : ℂ) :
    logDeriv (fun z : ℂ => (z - u) ^ k) x = (k : ℂ) / (x - u) := by
  have hcomp : (fun z : ℂ => (z - u) ^ k) = (fun w : ℂ => w ^ k) ∘ (fun z : ℂ => z - u) := rfl
  rw [hcomp, logDeriv_comp (by fun_prop) (by fun_prop)]
  simp [logDeriv_pow]

/-- A finite sum of circle-integrable functions is circle integrable. -/
theorem circleIntegrable_finset_sum {ι : Type*} (F : ι → ℂ → ℂ) (c : ℂ) (R : ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, CircleIntegrable (F i) c R) →
      CircleIntegrable (fun z => ∑ i ∈ s, F i z) c R := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | insert a w hw ihw =>
      intro hint
      have h1 : CircleIntegrable (F a) c R := hint a (Finset.mem_insert_self a w)
      have h2 : CircleIntegrable (fun z => ∑ i ∈ w, F i z) c R :=
        ihw fun i hi => hint i (Finset.mem_insert_of_mem hi)
      have hfun : (fun z => ∑ i ∈ insert a w, F i z) = fun z => F a z + ∑ i ∈ w, F i z := by
        funext z
        rw [Finset.sum_insert hw]
      rw [hfun]
      exact h1.add h2

/-- A circle integral of a finite sum is the sum of the circle integrals. -/
theorem circleIntegral_finset_sum {ι : Type*} (F : ι → ℂ → ℂ) (c : ℂ) (R : ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, CircleIntegrable (F i) c R) →
      (∮ z in C(c, R), ∑ i ∈ s, F i z) = ∑ i ∈ s, ∮ z in C(c, R), F i z := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp [circleIntegral]
  | insert a w hw ihw =>
      intro hint
      have h1 : CircleIntegrable (F a) c R := hint a (Finset.mem_insert_self a w)
      have hsub : ∀ i ∈ w, CircleIntegrable (F i) c R :=
        fun i hi => hint i (Finset.mem_insert_of_mem hi)
      have h2 : CircleIntegrable (fun z => ∑ i ∈ w, F i z) c R :=
        circleIntegrable_finset_sum F c R w hsub
      have hfun : (fun z => ∑ i ∈ insert a w, F i z) = fun z => F a z + ∑ i ∈ w, F i z := by
        funext z
        rw [Finset.sum_insert hw]
      rw [Finset.sum_insert hw, hfun, circleIntegral.integral_add h1 h2, ihw hsub]

/-- **The weighted argument principle on a disc.**  A function presented as a finite product of
powers of linear factors, with all the base points inside the circle, times a factor holomorphic
and nowhere vanishing on a neighbourhood of the closed disc, has weighted logarithmic-derivative
integral equal to `2πi` times the `p`-th power sum of its zeros. -/
theorem circleIntegral_weighted_logDeriv_prod
    {t : ℝ} (ht : 0 < t) {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall (0 : ℂ) t ⊆ U)
    (s : Finset ℂ) (m : ℂ → ℕ) {g : ℂ → ℂ}
    (hs : ∀ u ∈ s, u ∈ ball (0 : ℂ) t)
    (hg : DifferentiableOn ℂ g U) (hgne : ∀ z ∈ U, g z ≠ 0) (p : ℕ) :
    (∮ ζ in C(0, t), ζ ^ p * logDeriv (fun z => (∏ u ∈ s, (z - u) ^ m u) * g z) ζ)
      = (2 * (Real.pi : ℂ) * Complex.I) * ∑ u ∈ s, (m u : ℂ) * u ^ p := by
  classical
  have hgan : AnalyticOnNhd ℂ g U := hg.analyticOnNhd hU
  have hderivan : AnalyticOnNhd ℂ (deriv g) U := hgan.deriv
  -- the logarithmic derivative of `g` is holomorphic on `U`
  have hlogan : ∀ z ∈ U, AnalyticAt ℂ (logDeriv g) z := by
    intro z hz
    have : logDeriv g = fun w => deriv g w / g w := by
      funext w
      rw [logDeriv_apply]
    rw [this]
    exact (hderivan z hz).div (hgan z hz) (hgne z hz)
  -- the integrand splits on the circle
  have hsplit : ∀ ζ ∈ sphere (0 : ℂ) t,
      ζ ^ p * logDeriv (fun z => (∏ u ∈ s, (z - u) ^ m u) * g z) ζ
        = (∑ u ∈ s, (m u : ℂ) * ((ζ - u)⁻¹ * ζ ^ p)) + ζ ^ p * logDeriv g ζ := by
    intro ζ hζ
    have hζt : ‖ζ‖ = t := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 hζ
    have hζU : ζ ∈ U := hsub (by simp [mem_closedBall, hζt])
    have hne : ∀ u ∈ s, ζ - u ≠ 0 := by
      intro u hu
      have hlt : ‖u‖ < t := by simpa [Complex.dist_eq] using mem_ball_zero_iff.1 (hs u hu)
      intro hcon
      rw [sub_eq_zero] at hcon
      rw [hcon] at hζt
      exact absurd hζt (ne_of_lt hlt)
    have hprodne : (∏ u ∈ s, (ζ - u) ^ m u) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (hne u hu)
    have hprodd : DifferentiableAt ℂ (fun z : ℂ => ∏ u ∈ s, (z - u) ^ m u) ζ := by
      have heq : (fun z : ℂ => ∏ u ∈ s, (z - u) ^ m u)
          = ∏ u ∈ s, (fun z : ℂ => (z - u) ^ m u) := by
        funext z
        simp
      rw [heq]
      exact DifferentiableAt.finsetProd fun u _ => by fun_prop
    have hgd : DifferentiableAt ℂ g ζ := hg.differentiableAt (hU.mem_nhds hζU)
    rw [logDeriv_mul ζ hprodne (hgne ζ hζU) hprodd hgd]
    have hlp : logDeriv (fun z : ℂ => ∏ u ∈ s, (z - u) ^ m u) ζ
        = ∑ u ∈ s, (m u : ℂ) / (ζ - u) := by
      rw [logDeriv_prod (𝕜 := ℂ) (𝕜' := ℂ) (f := fun u (z : ℂ) => (z - u) ^ m u)
        (fun u hu => pow_ne_zero _ (hne u hu)) (fun u _ => by fun_prop)]
      exact Finset.sum_congr rfl fun u _ => logDeriv_sub_pow u (m u) ζ
    rw [hlp, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    field_simp
  rw [circleIntegral.integral_congr ht.le hsplit]
  -- integrability of each piece
  have hcontpow : ContinuousOn (fun ζ : ℂ => ζ ^ p) (sphere (0 : ℂ) t) := by fun_prop
  have hintlin : ∀ u ∈ s, CircleIntegrable (fun ζ : ℂ => (m u : ℂ) * ((ζ - u)⁻¹ * ζ ^ p))
      (0 : ℂ) t := by
    intro u hu
    refine ContinuousOn.circleIntegrable ht.le ?_
    have hne : ∀ ζ ∈ sphere (0 : ℂ) t, ζ - u ≠ 0 := by
      intro ζ hζ
      have hζt : ‖ζ‖ = t := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 hζ
      have hlt : ‖u‖ < t := by simpa [Complex.dist_eq] using mem_ball_zero_iff.1 (hs u hu)
      intro hcon
      rw [sub_eq_zero] at hcon
      rw [hcon] at hζt
      exact absurd hζt (ne_of_lt hlt)
    refine continuousOn_const.mul (ContinuousOn.mul ?_ hcontpow)
    exact ContinuousOn.inv₀ (by fun_prop) hne
  have hintlog : CircleIntegrable (fun ζ : ℂ => ζ ^ p * logDeriv g ζ) (0 : ℂ) t := by
    refine ContinuousOn.circleIntegrable ht.le ?_
    refine hcontpow.mul ?_
    intro ζ hζ
    have hζt : ‖ζ‖ = t := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 hζ
    have hζU : ζ ∈ U := hsub (by simp [mem_closedBall, hζt])
    exact ((hlogan ζ hζU).continuousAt).continuousWithinAt
  have hintsum : CircleIntegrable
      (fun ζ : ℂ => ∑ u ∈ s, (m u : ℂ) * ((ζ - u)⁻¹ * ζ ^ p)) (0 : ℂ) t :=
    circleIntegrable_finset_sum (fun u ζ => (m u : ℂ) * ((ζ - u)⁻¹ * ζ ^ p)) 0 t s hintlin
  rw [circleIntegral.integral_add hintsum hintlog]
  -- the nonvanishing factor contributes nothing
  have hzero : (∮ ζ in C(0, t), ζ ^ p * logDeriv g ζ) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable ht.le
      Set.countable_empty ?_ ?_
    · intro ζ hζ
      have hζU : ζ ∈ U := hsub hζ
      exact (((continuousAt_id.pow p).mul (hlogan ζ hζU).continuousAt)).continuousWithinAt
    · intro ζ hζ
      have hζU : ζ ∈ U := hsub (ball_subset_closedBall hζ.1)
      exact (differentiableAt_id.pow p).mul (hlogan ζ hζU).differentiableAt
  rw [hzero, add_zero]
  -- each linear factor contributes by Cauchy's formula
  rw [circleIntegral_finset_sum (fun u ζ => (m u : ℂ) * ((ζ - u)⁻¹ * ζ ^ p)) 0 t s hintlin]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hcauchy : (∮ ζ in C(0, t), (ζ - u)⁻¹ • (ζ ^ p))
      = (2 * (Real.pi : ℂ) * Complex.I) • (u ^ p) := by
    refine Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty (hs u hu) (by fun_prop) ?_
    intro ζ _
    exact differentiableAt_id.pow p
  have hrw : (∮ ζ in C(0, t), (m u : ℂ) * ((ζ - u)⁻¹ * ζ ^ p))
      = (m u : ℂ) * ∮ ζ in C(0, t), (ζ - u)⁻¹ * ζ ^ p := by
    simp
  rw [hrw]
  have hsmul : (∮ ζ in C(0, t), (ζ - u)⁻¹ * ζ ^ p)
      = (2 * (Real.pi : ℂ) * Complex.I) * u ^ p := by
    simp [smul_eq_mul] at hcauchy
    exact hcauchy
  rw [hsmul]
  ring

end HTGeometry
