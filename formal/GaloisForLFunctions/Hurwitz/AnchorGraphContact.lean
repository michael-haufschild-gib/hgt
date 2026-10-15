import GaloisForLFunctions.Hurwitz.AnchorLevelGraph
import Mathlib.Analysis.Meromorphic.Order

/-!
# Contact order of the actual Hurwitz zero graph

Strict differentiability identifies the nonzero limit of the quotient of
the anchor slice by the graph displacement. Removing that quotient's
singularity shows that the displacement has exactly the zeta zero order.
-/

open Complex Filter Metric Set Asymptotics
open scoped Topology

namespace HurwitzZetaContinuation

private theorem analyticOrderAt_eq_of_quotient_limit
    {f g : ℂ → ℂ} {x c : ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (hgn : ∀ᶠ z in 𝓝[≠] x, g z ≠ 0) (hc : c ≠ 0)
    (hlim : Tendsto (fun z => f z / g z) (𝓝[≠] x) (𝓝 c)) :
    analyticOrderAt f x = analyticOrderAt g x := by
  have hm : MeromorphicAt (fun z => f z / g z) x := hf.meromorphicAt.div hg.meromorphicAt
  have hnonneg := (tendsto_nhds_iff_meromorphicOrderAt_nonneg hm).mp ⟨c, hlim⟩
  obtain ⟨u, hu, heq⟩ := hm.meromorphicOrderAt_nonneg_iff.mp hnonneg
  have huc : u x = c := tendsto_nhds_unique
    (hu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (hlim.congr' heq)
  have hune : u x ≠ 0 := by rwa [huc]
  have hfg : f =ᶠ[𝓝[≠] x] fun z => g z * u z := by
    filter_upwards [heq, hgn] with z hz hgz
    calc
      f z = (f z / g z) * g z := (div_mul_cancel₀ _ hgz).symm
      _ = u z * g z := by rw [hz]
      _ = g z * u z := mul_comm _ _
  have hfg' : f =ᶠ[𝓝 x] fun z => g z * u z :=
    (hf.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (hg.fun_mul hu).continuousAt).mp hfg
  rw [analyticOrderAt_congr hfg']
  change analyticOrderAt (g * u) x = analyticOrderAt g x
  rw [analyticOrderAt_mul hg hu, hu.analyticOrderAt_eq_zero.mpr hune, add_zero]

/-- The displacement of an actual local Hurwitz zero graph has exactly zeta's order. -/
theorem analyticOrderAt_anchor_zero_graph_contact
    {rho : ℂ} (hrho : 0 < rho.re) (hrho1 : rho ≠ 1)
    {A : ℂ → ℂ} (hA : A rho = 1) (hAa : AnalyticAt ℂ A rho)
    (hgraph : ∀ᶠ s in 𝓝 rho, continuedHzeta s (A s) = 0) :
    analyticOrderAt (fun s => 1 - A s) rho = analyticOrderAt riemannZeta rho := by
  have hg : AnalyticAt ℂ (fun s => 1 - A s) rho := analyticAt_const.fun_sub hAa
  have hz : AnalyticAt ℂ riemannZeta rho := analyticOn_riemannZeta rho hrho1
  rcases hg.eventually_eq_zero_or_eventually_ne_zero with hloc | hgn
  · have hzloc : ∀ᶠ s in 𝓝 rho, riemannZeta s = 0 := by
      filter_upwards [hloc, hgraph] with s hs hsg
      have ha : A s = 1 := (sub_eq_zero.mp hs).symm
      simpa only [ha, continuedHzeta_at_one] using hsg
    rw [analyticOrderAt_eq_top.mpr hloc, analyticOrderAt_eq_top.mpr hzloc]
  · let F : ℂ × ℂ → ℂ := fun p => continuedHzeta p.1 p.2
    let D := fderiv ℂ F (rho, 1)
    let c : ℂ := -rho * riemannZeta (rho + 1)
    have hc : c ≠ 0 := by
      have hrho0 : rho ≠ 0 := by
        intro h
        simp [h] at hrho
      exact mul_ne_zero (neg_ne_zero.mpr hrho0)
        (riemannZeta_ne_zero_of_one_lt_re (by simpa using hrho))
    have hD : ∀ w : ℂ, D (0, w) = w * c := by
      intro w
      have h := congrArg (fun L : ℂ →L[ℂ] ℂ => L w)
        (fderiv_continuedHzeta_joint_comp_inr hrho hrho1)
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using h
    have hc1 := contDiffAt_one_continuedHzeta_joint hrho hrho1 (a := 1) (by norm_num)
    have hpath : Tendsto (fun s : ℂ => ((s, (1 : ℂ)), (s, A s)))
        (𝓝 rho) (𝓝 ((rho, 1), (rho, 1))) := by
      simpa only [hA, id_eq] using
        ((continuousAt_id.prodMk continuousAt_const).prodMk
          (continuousAt_id.prodMk hAa.continuousAt)).tendsto
    have hlo := (hc1.hasStrictFDerivAt (by norm_num)).isLittleO.comp_tendsto hpath
    have hpair (s : ℂ) : (s, (1 : ℂ)) - (s, A s) = (0, 1 - A s) := by
      ext <;> simp
    have hnorm : (fun s => continuedHzeta s 1 - continuedHzeta s (A s) - D (0, 1 - A s))
        =o[𝓝 rho] (fun s => ‖1 - A s‖) := by
      simpa only [Function.comp_def, hpair, Prod.norm_def, norm_zero,
        max_eq_right (norm_nonneg _), D, F] using hlo.norm_right
    have hsmall : (fun s => riemannZeta s - (1 - A s) * c)
        =o[𝓝 rho] (fun s => 1 - A s) := by
      apply hnorm.of_norm_right.congr' ?_ (Filter.EventuallyEq.refl _ _)
      filter_upwards [hgraph] with s hs
      rw [continuedHzeta_at_one, hs, sub_zero, hD]
    have hlim0 := ((hsmall.mono (l := 𝓝[≠] rho)
      nhdsWithin_le_nhds).tendsto_div_nhds_zero).add_const c
    have hlim : Tendsto (fun s => riemannZeta s / (1 - A s)) (𝓝[≠] rho) (𝓝 c) := by
      have heq : (fun s => (riemannZeta s - (1 - A s) * c) / (1 - A s) + c)
          =ᶠ[𝓝[≠] rho] (fun s => riemannZeta s / (1 - A s)) := by
        filter_upwards [hgn] with s hs
        field_simp
        exact sub_add_cancel _ _
      simpa only [zero_add] using hlim0.congr' heq
    exact (analyticOrderAt_eq_of_quotient_limit hz hg hgn hc hlim).symm

end HurwitzZetaContinuation
