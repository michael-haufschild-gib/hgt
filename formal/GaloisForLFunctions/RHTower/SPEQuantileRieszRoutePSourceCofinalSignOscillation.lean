import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceLandauExtension

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

private def routePSourceReconstructedLogDeriv (epsilon T : ℝ) (s : ℂ) : ℂ :=
  -(s * ((s + 1 / 2) * routePSourceLaplaceUnderSign epsilon T (s - 1 / 2) + 2 / 3)) - 1

private theorem analyticOnNhd_routePSourceReconstructedLogDeriv
    {epsilon T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t)
    (hepsilon : epsilon ≠ 0) :
    AnalyticOnNhd ℂ (routePSourceReconstructedLogDeriv epsilon T)
      {s : ℂ | 3 / 8 < s.re} := by
  intro s hs
  change 3 / 8 < s.re at hs
  have hshiftRe : -(1 / 8 : ℝ) < (s - 1 / 2).re := by
    norm_num [Complex.sub_re]
    linarith
  have hL : AnalyticAt ℂ (routePSourceLaplaceUnderSign epsilon T) (s - 1 / 2) :=
    analyticOnNhd_routePSourceLaplaceUnderSign hT hpos hepsilon _ hshiftRe
  have hshift : AnalyticAt ℂ (fun w : ℂ => w - 1 / 2) s := by fun_prop
  have hcomp : AnalyticAt ℂ
      (fun w : ℂ => routePSourceLaplaceUnderSign epsilon T (w - 1 / 2)) s :=
    AnalyticAt.comp (f := fun w : ℂ => w - 1 / 2) hL hshift
  change AnalyticAt ℂ
    (fun w : ℂ => -(w * ((w + 1 / 2) *
      routePSourceLaplaceUnderSign epsilon T (w - 1 / 2) + 2 / 3)) - 1) s
  exact ((analyticAt_id.mul
    (((analyticAt_id.add analyticAt_const).mul hcomp).add analyticAt_const)).neg).sub
      analyticAt_const

private theorem routePSourceReconstructedLogDeriv_eq_logDeriv
    {epsilon T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t)
    (hepsilon : epsilon ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    routePSourceReconstructedLogDeriv epsilon T s =
      logDeriv regularizedRiemannZeta s := by
  have hz : 1 / 2 < (s - 1 / 2).re := by
    norm_num [Complex.sub_re]
    linarith
  rw [routePSourceReconstructedLogDeriv,
    routePSourceLaplaceUnderSign_eq_continuation hT hpos hepsilon hz,
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

private theorem regularizedRiemannZeta_ne_zero_of_eventual_routeP_source_sign
    {epsilon T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t)
    (hepsilon : epsilon ≠ 0)
    {s : ℂ} (hs : 3 / 8 < s.re) :
    regularizedRiemannZeta s ≠ 0 := by
  let U : Set ℂ := {w : ℂ | 3 / 8 < w.re}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U :=
    (convex_halfSpace_re_gt (3 / 8 : ℝ)).isPreconnected
  let A : ℂ → ℂ := routePSourceReconstructedLogDeriv epsilon T
  have hA : AnalyticOnNhd ℂ A U :=
    analyticOnNhd_routePSourceReconstructedLogDeriv hT hpos hepsilon
  have hregAn : ∀ w : ℂ, AnalyticAt ℂ regularizedRiemannZeta w :=
    fun w => differentiable_regularizedRiemannZeta.analyticAt w
  let H : ℂ → ℂ := fun w =>
    deriv regularizedRiemannZeta w - A w * regularizedRiemannZeta w
  have hHan : AnalyticOnNhd ℂ H U := by
    intro w hw
    exact (hregAn w).deriv.sub ((hA w hw).mul (hregAn w))
  have htwo : (2 : ℂ) ∈ U := by
    change (3 / 8 : ℝ) < (2 : ℂ).re
    norm_num
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
    have hagree : A w = logDeriv regularizedRiemannZeta w :=
      routePSourceReconstructedLogDeriv_eq_logDeriv hT hpos hepsilon hw
    dsimp only [H]
    rw [hagree, logDeriv_apply]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hregNe).symm
  have hHzero : EqOn H 0 U :=
    hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUpre htwo hHev
  intro hzero
  have hPunct : ∀ᶠ w in 𝓝[≠] s, regularizedRiemannZeta w ≠ 0 :=
    (hregAn s).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hlocal =>
        analyticOrderAt_regularizedRiemannZeta_ne_top s
          (analyticOrderAt_eq_top.mpr hlocal))
  have hUevent : ∀ᶠ w in 𝓝[≠] s, w ∈ U :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hUopen.mem_nhds hs)
  have heq : logDeriv regularizedRiemannZeta =ᶠ[𝓝[≠] s] A := by
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
      meromorphicOrderAt (logDeriv regularizedRiemannZeta) s := by
    rw [hcongr]
    exact (hA s hs).meromorphicOrderAt_nonneg
  rw [horder] at hnonneg
  exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
    exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg

/-- Hardy's critical-line zero rules out every eventual fixed sign of the literal source. -/
theorem not_eventually_fixed_sign_routePSource
    {epsilon T : ℝ} (hT : 0 ≤ T) (hepsilon : epsilon ≠ 0) :
    ¬ (∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t) := by
  intro hpos
  obtain ⟨T0, hT0, hzeros⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨tau, htau, hzeta⟩ := hzeros T0 le_rfl
  have htau0 : 0 < tau := lt_of_lt_of_le hT0 htau.1
  let rho : ℂ := linePt tau
  have hrhore : rho.re = 1 / 2 := by
    dsimp only [rho]
    exact linePt_re tau
  have hrho1 : rho ≠ 1 := by
    intro heq
    have him := congrArg Complex.im heq
    dsimp only [rho] at him
    rw [linePt_im, Complex.one_im] at him
    linarith
  have hregZero : regularizedRiemannZeta rho = 0 := by
    rw [regularizedRiemannZeta_of_ne_one hrho1]
    have hzeta' : riemannZeta rho = 0 := hzeta
    rw [hzeta', mul_zero]
  have hnozero : regularizedRiemannZeta rho ≠ 0 :=
    regularizedRiemannZeta_ne_zero_of_eventual_routeP_source_sign
      hT hpos hepsilon (s := rho) (by rw [hrhore]; norm_num)
  exact hnozero hregZero

/-- The literal P/SP-E source has both signs arbitrarily far out on the logarithmic ray. -/
theorem routePSource_cofinal_positive_and_negative (T : ℝ) :
    (∃ t : ℝ, T < t ∧
      0 < GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t) ∧
    (∃ t : ℝ, T < t ∧
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t < 0) := by
  let U : ℝ := max T 0
  have hU : 0 ≤ U := le_max_right T 0
  have hTU : T ≤ U := le_max_left T 0
  have hneg : ∃ t : ℝ, U < t ∧
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t < 0 := by
    by_contra h
    have hnonneg : ∀ t, U < t →
        0 ≤ GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t := by
      intro t ht
      by_contra hn
      exact h ⟨t, ht, lt_of_not_ge hn⟩
    exact not_eventually_fixed_sign_routePSource (epsilon := 1) hU (by norm_num)
      (by simpa using hnonneg)
  have hpos : ∃ t : ℝ, U < t ∧
      0 < GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t := by
    by_contra h
    have hnonpos : ∀ t, U < t →
        0 ≤ (-1 : ℝ) *
          GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t := by
      intro t ht
      have hle : GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t ≤ 0 :=
        le_of_not_gt (fun hgt => h ⟨t, ht, hgt⟩)
      nlinarith
    exact not_eventually_fixed_sign_routePSource (epsilon := -1) hU (by norm_num)
      hnonpos
  exact ⟨⟨hpos.choose, lt_of_le_of_lt hTU hpos.choose_spec.1,
      hpos.choose_spec.2⟩,
    ⟨hneg.choose, lt_of_le_of_lt hTU hneg.choose_spec.1,
      hneg.choose_spec.2⟩⟩

end
end RHTower
