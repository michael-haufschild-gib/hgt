import GaloisForLFunctions.RHTower.MobiusDivisorCriticalSourceCurrentNonconstancy
import Mathlib.Analysis.Analytic.Order

noncomputable section
open Filter Topology Set Complex
namespace RHTower

private theorem centeredCurrent_analyticAt_real {t : ℝ} (ht : 1 ≤ t) :
    AnalyticAt ℂ centeredPrimeTailCurrentContinuation (t : ℂ) := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    simpa using analyticAt_centeredPrimeTailCurrentContinuation_one
  · have hs : 1 < ((t : ℂ)).re := by simpa using h
    have hs1 : (t : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt h)
    have hZana : AnalyticAt ℂ zetaResidueUnit (t : ℂ) :=
      analyticAt_zetaResidueUnit _
    have hZne : zetaResidueUnit (t : ℂ) ≠ 0 := by
      rw [zetaResidueUnit, Function.update_of_ne hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1)
        (riemannZeta_ne_zero_of_one_lt_re hs)
    have hlog : AnalyticAt ℂ (logDeriv zetaResidueUnit) (t : ℂ) := by
      simpa [logDeriv_apply] using! hZana.deriv.div hZana hZne
    have hslope : AnalyticAt ℂ (dslope zetaResidueUnit 1) (t : ℂ) :=
      analyticAt_dslope_of_analyticAt zetaResidueUnit_analyticAt hZana
    exact (hlog.add hslope).sub analyticAt_const

private theorem centeredCurrent_not_eventually_const_at_one :
    ¬ ∀ᶠ s in 𝓝 (1 : ℂ),
      centeredPrimeTailCurrentContinuation s =
        centeredPrimeTailCurrentContinuation 1 := by
  let U : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Set.Ici 1
  have hUpre : IsPreconnected U := by
    exact isPreconnected_Ici.image _
      (by fun_prop : Continuous fun t : ℝ => (t : ℂ)).continuousOn
  have hCU : AnalyticOnNhd ℂ centeredPrimeTailCurrentContinuation U := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact centeredCurrent_analyticAt_real ht
  have h1U : (1 : ℂ) ∈ U := by
    exact ⟨1, by simp, by simp⟩
  intro hlocal
  have hEqOn := hCU.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hUpre h1U hlocal
  have hRay : ∀ N : ℕ, 1 ≤ N →
      centeredPrimeTailCurrentContinuation (N : ℂ) =
        centeredPrimeTailCurrentContinuation 1 := by
    intro N hN
    apply hEqOn
    exact ⟨(N : ℝ), by simpa using (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN),
      by norm_cast⟩
  have hconstlim : Tendsto (fun _ : ℕ => centeredPrimeTailCurrentContinuation 1)
      atTop (𝓝 0) :=
    centeredCurrent_farRight_zero.congr' (by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
      exact hRay N hN)
  have hval : centeredPrimeTailCurrentContinuation 1 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstlim
  have hγ : (0 : ℝ) < 2 * Real.eulerMascheroniConstant - 1 := by
    have := Real.one_half_lt_eulerMascheroniConstant
    linarith
  have hne : centeredPrimeTailCurrentContinuation 1 ≠ 0 := by
    rw [centeredPrimeTailCurrentContinuation_one]
    exact_mod_cast (ne_of_gt hγ)
  exact hne hval

theorem criticalSourceCurrentGap_finite_order :
    analyticOrderAt
      (fun s : ℂ => centeredPrimeTailCurrentContinuation 1 -
        centeredPrimeTailCurrentContinuation s) 1 ≠ ⊤ := by
  intro htop
  have hlocal := analyticOrderAt_eq_top.mp htop
  apply centeredCurrent_not_eventually_const_at_one
  filter_upwards [hlocal] with s hs
  exact (sub_eq_zero.mp hs).symm

theorem criticalSourceCurrentGap_finiteJet :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
      (fun s : ℂ => centeredPrimeTailCurrentContinuation 1 -
        centeredPrimeTailCurrentContinuation s) =ᶠ[𝓝 1]
          (fun s => (s - 1) ^ r * g s) := by
  let gap : ℂ → ℂ := fun s => centeredPrimeTailCurrentContinuation 1 -
    centeredPrimeTailCurrentContinuation s
  have hana : AnalyticAt ℂ gap 1 :=
    analyticAt_const.sub analyticAt_centeredPrimeTailCurrentContinuation_one
  have hfin : analyticOrderAt gap 1 ≠ ⊤ :=
    criticalSourceCurrentGap_finite_order
  obtain ⟨g, hga, hg0, hfac⟩ := hana.analyticOrderAt_ne_top.mp hfin
  let r := analyticOrderNatAt gap 1
  have hr : 1 ≤ r := by
    by_contra hn
    have hr0 : r = 0 := by omega
    have heq := hfac.self_of_nhds
    have hzero : g 1 = 0 := by
      simpa [gap, r, hr0] using heq.symm
    exact hg0 hzero
  refine ⟨r, hr, g, hga, hg0, ?_⟩
  simpa only [gap, smul_eq_mul] using hfac

end RHTower
