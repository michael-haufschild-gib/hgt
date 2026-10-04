import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceCofinalSignOscillation

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

private def routePSourceLogDerivFromExtension (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  -(s * ((s + 1 / 2) * L (s - 1 / 2) + 2 / 3)) - 1

private theorem analyticOnNhd_routePSourceLogDerivFromExtension
    {L : ℂ → ℂ} {c : ℝ}
    (hL : AnalyticOnNhd ℂ L {z : ℂ | c < z.re}) :
    AnalyticOnNhd ℂ (routePSourceLogDerivFromExtension L)
      {s : ℂ | c + 1 / 2 < s.re} := by
  intro s hs
  change c + 1 / 2 < s.re at hs
  have hshiftRe : c < (s - 1 / 2).re := by
    norm_num [Complex.sub_re]
    linarith
  have hLAt : AnalyticAt ℂ L (s - 1 / 2) := hL _ hshiftRe
  have hshift : AnalyticAt ℂ (fun w : ℂ => w - 1 / 2) s := by fun_prop
  have hcomp : AnalyticAt ℂ (fun w : ℂ => L (w - 1 / 2)) s :=
    AnalyticAt.comp (f := fun w : ℂ => w - 1 / 2) hLAt hshift
  change AnalyticAt ℂ
    (fun w : ℂ => -(w * ((w + 1 / 2) * L (w - 1 / 2) + 2 / 3)) - 1) s
  exact ((analyticAt_id.mul
    (((analyticAt_id.add analyticAt_const).mul hcomp).add analyticAt_const)).neg).sub
      analyticAt_const

private theorem routePSourceLogDerivFromExtension_eq_logDeriv
    {L : ℂ → ℂ}
    (hagree : ∀ z : ℂ, 1 / 2 < z.re → L z = routePSourceLaplaceContinuation z)
    {s : ℂ} (hs : 1 < s.re) :
    routePSourceLogDerivFromExtension L s = logDeriv regularizedRiemannZeta s := by
  have hz : 1 / 2 < (s - 1 / 2).re := by
    norm_num [Complex.sub_re]
    linarith
  rw [routePSourceLogDerivFromExtension, hagree _ hz,
    routePSourceLaplaceContinuation, criticalNormalizedChebyshevErrorContinuation]
  have hfun : zetaResidueUnit = regularizedRiemannZeta := by
    funext w
    rfl
  rw [hfun]
  have hcoord1 : s - 1 / 2 + 1 / 2 = s := by ring
  have hcoord2 : s - 1 / 2 + 1 = s + 1 / 2 := by ring
  rw [hcoord1, hcoord2]
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hsHalf : s + 1 / 2 ≠ 0 := by
    apply ne_zero_of_re_pos
    norm_num [Complex.add_re]
    linarith
  have hmiddle :
      (s + 1 / 2) *
          ((-(logDeriv regularizedRiemannZeta s + 1) / s - 2 / 3) / (s + 1 / 2)) +
          2 / 3 =
        -(logDeriv regularizedRiemannZeta s + 1) / s := by
    rw [mul_comm (s + 1 / 2), div_mul_cancel₀ _ hsHalf]
    ring
  rw [hmiddle]
  field_simp [hs0]
  ring

/-- Every strictly negative abscissa is obstructed by a native Hardy zero.
Agreement is required only on the unconditional convergence half-plane. -/
theorem no_routePSourceLaplace_analytic_extension_negative_abscissa
    {c : ℝ} (hc : c < 0) (L : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {z : ℂ | c < z.re})
    (hagree : ∀ z : ℂ, 1 / 2 < z.re → L z = routePSourceLaplaceContinuation z) : False := by
  let U : Set ℂ := {w : ℂ | c + 1 / 2 < w.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U :=
    (convex_halfSpace_re_gt (c + 1 / 2)).isPreconnected
  let A : ℂ → ℂ := routePSourceLogDerivFromExtension L
  have hA : AnalyticOnNhd ℂ A U :=
    analyticOnNhd_routePSourceLogDerivFromExtension hL
  have hregAn : ∀ w : ℂ, AnalyticAt ℂ regularizedRiemannZeta w :=
    fun w => differentiable_regularizedRiemannZeta.analyticAt w
  let H : ℂ → ℂ := fun w =>
    deriv regularizedRiemannZeta w - A w * regularizedRiemannZeta w
  have hHan : AnalyticOnNhd ℂ H U := by
    intro w hw
    exact (hregAn w).deriv.sub ((hA w hw).mul (hregAn w))
  have htwo : (2 : ℂ) ∈ U := by
    change c + 1 / 2 < 2
    linarith
  have hHev : H =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hright : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hright] with w hw
    have hw1 : w ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith
    have hregNe : regularizedRiemannZeta w ≠ 0 := by
      rw [regularizedRiemannZeta_of_ne_one hw1]
      exact mul_ne_zero (sub_ne_zero.mpr hw1)
        (riemannZeta_ne_zero_of_one_lt_re hw)
    have hag : A w = logDeriv regularizedRiemannZeta w :=
      routePSourceLogDerivFromExtension_eq_logDeriv hagree hw
    dsimp only [H]
    rw [hag, logDeriv_apply]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hregNe).symm
  have hHzero : EqOn H 0 U :=
    hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUpre htwo hHev
  obtain ⟨T0, hT0, hzeros⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨tau, htau, hzeta⟩ := hzeros T0 le_rfl
  have htau0 : 0 < tau := lt_of_lt_of_le hT0 htau.1
  let rho : ℂ := linePt tau
  have hrhore : rho.re = 1 / 2 := by
    dsimp only [rho]
    exact linePt_re tau
  have hrhoU : rho ∈ U := by
    change c + 1 / 2 < rho.re
    rw [hrhore]
    linarith
  have hrho1 : rho ≠ 1 := by
    intro heq
    have him := congrArg Complex.im heq
    dsimp only [rho] at him
    rw [linePt_im, Complex.one_im] at him
    linarith
  have hzero : regularizedRiemannZeta rho = 0 := by
    rw [regularizedRiemannZeta_of_ne_one hrho1]
    have hzeta' : riemannZeta rho = 0 := hzeta
    rw [hzeta', mul_zero]
  have hPunct : ∀ᶠ w in 𝓝[≠] rho, regularizedRiemannZeta w ≠ 0 :=
    (hregAn rho).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hlocal =>
        analyticOrderAt_regularizedRiemannZeta_ne_top rho
          (analyticOrderAt_eq_top.mpr hlocal))
  have hUevent : ∀ᶠ w in 𝓝[≠] rho, w ∈ U :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hUopen.mem_nhds hrhoU)
  have heq : logDeriv regularizedRiemannZeta =ᶠ[𝓝[≠] rho] A := by
    filter_upwards [hPunct, hUevent] with w hwNe hwU
    rw [logDeriv_apply]
    apply (div_eq_iff hwNe).2
    have hh : deriv regularizedRiemannZeta w -
        A w * regularizedRiemannZeta w = 0 := hHzero hwU
    exact sub_eq_zero.mp hh
  have horder :=
    meromorphicOrderAt_logDeriv_regularizedRiemannZeta_eq_neg_one hzero
  have hcongr := meromorphicOrderAt_congr heq
  have hnonneg : (0 : WithTop ℤ) ≤
      meromorphicOrderAt (logDeriv regularizedRiemannZeta) rho := by
    rw [hcongr]
    exact (hA rho hrhoU).meromorphicOrderAt_nonneg
  rw [horder] at hnonneg
  exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
    exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg

/-- The original fixed-width obstruction, retained as a specialization. -/
theorem no_routePSourceLaplace_analytic_extension_past_axis
    (L : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {z : ℂ | -(1 / 8 : ℝ) < z.re})
    (hagree : ∀ z : ℂ, 1 / 2 < z.re → L z = routePSourceLaplaceContinuation z) : False :=
  no_routePSourceLaplace_analytic_extension_negative_abscissa (by norm_num) L hL hagree

end
end RHTower
