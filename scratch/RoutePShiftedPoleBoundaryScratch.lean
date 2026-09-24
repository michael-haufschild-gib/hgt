import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePShiftedPositiveCarrier
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceCofinalSignOscillation

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

private theorem logDeriv_regularizedZeta_eq_analytic_extension
    (A : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A {s : ℂ | 1 / 2 < s.re})
    (hEq : ∀ s : ℂ, 1 < s.re → A s = logDeriv regularizedRiemannZeta s) :
    ∀ s : ℂ, 1 / 2 < s.re →
      A s = logDeriv regularizedRiemannZeta s := by
  let U : Set ℂ := {w : ℂ | 1 / 2 < w.re}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U :=
    (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected
  have hregAn : ∀ w : ℂ, AnalyticAt ℂ regularizedRiemannZeta w :=
    fun w => differentiable_regularizedRiemannZeta.analyticAt w
  let H : ℂ → ℂ := fun w =>
    deriv regularizedRiemannZeta w - A w * regularizedRiemannZeta w
  have hHan : AnalyticOnNhd ℂ H U := by
    intro w hw
    exact (hregAn w).deriv.sub ((hA w hw).mul (hregAn w))
  have htwo : (2 : ℂ) ∈ U := by
    change (1 / 2 : ℝ) < (2 : ℂ).re
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
    have hagree : A w = logDeriv regularizedRiemannZeta w := hEq w hw
    dsimp only [H]
    rw [hagree, logDeriv_apply]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hregNe).symm
  have hHzero : EqOn H 0 U :=
    hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUpre htwo hHev
  intro s hs
  have hsU : s ∈ U := hs
  have hregNe : regularizedRiemannZeta s ≠ 0 := by
    intro hzero
    have hPunct : ∀ᶠ w in 𝓝[≠] s, regularizedRiemannZeta w ≠ 0 :=
      (hregAn s).eventually_eq_zero_or_eventually_ne_zero.resolve_left
        (fun hlocal =>
          analyticOrderAt_regularizedRiemannZeta_ne_top s
            (analyticOrderAt_eq_top.mpr hlocal))
    have hUevent : ∀ᶠ w in 𝓝[≠] s, w ∈ U :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (hUopen.mem_nhds hsU)
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
      exact (hA s hsU).meromorphicOrderAt_nonneg
    rw [horder] at hnonneg
    exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg
  have hh : deriv regularizedRiemannZeta s -
      A s * regularizedRiemannZeta s = 0 := hHzero hsU
  rw [logDeriv_apply]
  apply (eq_div_iff hregNe).2
  exact (sub_eq_zero.mp hh).symm

private def routePShiftedReconstructedLogDeriv
    (epsilon B T : ℝ) (s : ℂ) : ℂ :=
  -(s * ((s + 1 / 2) *
    routePSourceLaplaceUnderShift epsilon B T (s - 1 / 2) + 2 / 3)) - 1

private theorem analyticOnNhd_routePShiftedReconstructedLogDeriv
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hepsilon : epsilon ≠ 0) :
    AnalyticOnNhd ℂ (routePShiftedReconstructedLogDeriv epsilon B T)
      {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  change 1 / 2 < s.re at hs
  have hshiftRe : 0 < (s - 1 / 2).re := by
    norm_num [Complex.sub_re]
    linarith
  have hL : AnalyticAt ℂ (routePSourceLaplaceUnderShift epsilon B T)
      (s - 1 / 2) :=
    analyticOnNhd_routePSourceLaplaceUnderShift hT hpos hepsilon _ hshiftRe
  have hshift : AnalyticAt ℂ (fun w : ℂ => w - 1 / 2) s := by fun_prop
  have hcomp : AnalyticAt ℂ
      (fun w : ℂ => routePSourceLaplaceUnderShift epsilon B T (w - 1 / 2)) s :=
    AnalyticAt.comp (f := fun w : ℂ => w - 1 / 2) hL hshift
  change AnalyticAt ℂ
    (fun w : ℂ => -(w * ((w + 1 / 2) *
      routePSourceLaplaceUnderShift epsilon B T (w - 1 / 2) + 2 / 3)) - 1) s
  exact ((analyticAt_id.mul
    (((analyticAt_id.add analyticAt_const).mul hcomp).add analyticAt_const)).neg).sub
      analyticAt_const

private theorem routePShiftedReconstructedLogDeriv_eq_logDeriv
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hepsilon : epsilon ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    routePShiftedReconstructedLogDeriv epsilon B T s =
      logDeriv regularizedRiemannZeta s := by
  have hz : 1 / 2 < (s - 1 / 2).re := by
    norm_num [Complex.sub_re]
    linarith
  rw [routePShiftedReconstructedLogDeriv,
    routePSourceLaplaceUnderShift_eq_continuation hT hpos hepsilon hz,
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

private theorem routePShiftedReconstructedLogDeriv_eq_logDeriv_rightHalf
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hepsilon : epsilon ≠ 0) :
    ∀ s : ℂ, 1 / 2 < s.re →
      routePShiftedReconstructedLogDeriv epsilon B T s =
        logDeriv regularizedRiemannZeta s := by
  exact logDeriv_regularizedZeta_eq_analytic_extension
    (routePShiftedReconstructedLogDeriv epsilon B T)
    (analyticOnNhd_routePShiftedReconstructedLogDeriv hT hpos hepsilon)
    (fun s hs => routePShiftedReconstructedLogDeriv_eq_logDeriv hT hpos hepsilon hs)

private theorem routePSourceLaplaceUnderShift_eq_continuation_of_re_pos
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hepsilon : epsilon ≠ 0)
    {z : ℂ} (hz : 0 < z.re) :
    routePSourceLaplaceUnderShift epsilon B T z =
      routePSourceLaplaceContinuation z := by
  let s : ℂ := z + 1 / 2
  have hs : 1 / 2 < s.re := by
    dsimp [s]
    norm_num [Complex.add_re]
    linarith
  have hLog := routePShiftedReconstructedLogDeriv_eq_logDeriv_rightHalf
    hT hpos hepsilon s hs
  have hcoord1 : s - 1 / 2 = z := by dsimp [s]; ring
  have hcoord2 : s + 1 / 2 = z + 1 := by dsimp [s]; ring
  rw [routePShiftedReconstructedLogDeriv, hcoord1, hcoord2] at hLog
  have hfun : zetaResidueUnit = regularizedRiemannZeta := by
    funext w
    rfl
  rw [routePSourceLaplaceContinuation,
    criticalNormalizedChebyshevErrorContinuation, hfun]
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hzplus : z + 1 ≠ 0 := ne_zero_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hcore : ((z + 1) * routePSourceLaplaceUnderShift epsilon B T z + 2 / 3) * s =
      -(logDeriv regularizedRiemannZeta s + 1) := by
    linear_combination -hLog
  have hratio :
      (z + 1) * routePSourceLaplaceUnderShift epsilon B T z + 2 / 3 =
        -(logDeriv regularizedRiemannZeta s + 1) / s :=
    (eq_div_iff hs0).2 hcore
  have htarget : (z + 1) * routePSourceLaplaceUnderShift epsilon B T z =
      -(logDeriv regularizedRiemannZeta s + 1) / s - 2 / 3 := by
    linear_combination hratio
  apply (eq_div_iff hzplus).2
  calc
    routePSourceLaplaceUnderShift epsilon B T z * (z + 1) =
        (z + 1) * routePSourceLaplaceUnderShift epsilon B T z := mul_comm _ _
    _ = _ := by simpa only [s] using htarget

end
end RHTower
