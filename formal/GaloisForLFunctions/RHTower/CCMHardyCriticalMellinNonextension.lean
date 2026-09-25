import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeAbelCompleteness
import GaloisForLFunctions.RHTower.CCMCriticalMellinDivisorTomography
import GaloisForLFunctions.RHTower.XiWeilHardyReferenceLorentzianPlane

open Complex Filter Set Topology

namespace RHTower

noncomputable section

theorem no_analytic_extension_regularizedCriticalMellinDefect_pastHardy
    {c : ℝ} (hcLow : -1 < c) (hcHigh : c < -1 / 2)
    (A : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A {s : ℂ | c < s.re})
    (hagree : ∀ s : ℂ, 0 < s.re → A s = regularizedCriticalMellinDefect s) : False := by
  let U : Set ℂ := {s : ℂ | c < s.re}
  let g : ℂ → ℂ := fun s => regularizedRiemannZeta (s + 1)
  let E : ℂ → ℂ := fun s =>
    g s * (A s - 1 / (s + 1)) - deriv regularizedRiemannZeta (s + 1)
  have hE : AnalyticOnNhd ℂ E U := by
    intro s hs
    have hs1 : s + 1 ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      change c < s.re at hs
      norm_num [Complex.add_re] at hre
      linarith
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
    have hregBase : AnalyticAt ℂ regularizedRiemannZeta (s + 1) :=
      (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
        isOpen_univ) (s + 1) (Set.mem_univ _)
    have hreg : AnalyticAt ℂ g s :=
      AnalyticAt.comp (f := fun z : ℂ => z + 1) hregBase hshift
    have hderiv : AnalyticAt ℂ
        (fun z : ℂ => deriv regularizedRiemannZeta (z + 1)) s :=
      AnalyticAt.comp (f := fun z : ℂ => z + 1) hregBase.deriv hshift
    have hrat : AnalyticAt ℂ (fun z : ℂ => 1 / (z + 1)) s :=
      analyticAt_const.div hshift hs1
    change AnalyticAt ℂ
      (fun z => g z * (A z - 1 / (z + 1)) -
        deriv regularizedRiemannZeta (z + 1)) s
    exact hreg.mul ((hA s hs).sub hrat) |>.sub hderiv
  have hEzero (s : ℂ) (hs : 0 < s.re) : E s = 0 := by
    have hs1 : s + 1 ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      norm_num [Complex.add_re] at hre
      linarith
    have hgne : g s ≠ 0 := by
      change regularizedRiemannZeta (s + 1) ≠ 0
      exact (analyticAt_regularizedCriticalMellinDefect_iff_regularizedZeta_ne_zero
        (u := s) (by linarith)).1
        (analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane s hs)
    dsimp only [E]
    rw [hagree s hs]
    dsimp only [regularizedCriticalMellinDefect]
    rw [logDeriv_apply]
    dsimp only [g] at hgne ⊢
    field_simp [hs1, hgne]
    ring
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt c).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by
    change c < (2 : ℂ).re
    norm_num
    linarith
  have hev : E =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hright : {s : ℂ | 0 < s.re} ∈ 𝓝 (2 : ℂ) := by
      apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      norm_num
    filter_upwards [hright] with s hs
    exact hEzero s hs
  have hEall : EqOn E 0 U :=
    hE.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUpre htwo hev
  obtain ⟨rho, hrho⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  let p : ℂ := criticalMellinXiPole rho
  have hp : p ∈ U := by
    change c < p.re
    dsimp only [p, criticalMellinXiPole]
    rw [Complex.sub_re]
    norm_num at hrho ⊢
    linarith
  have hm : (inverseTiltedXiMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (inverseTiltedXiMultiplicity_pos rho)
  have hres : Tendsto
      (fun u : ℂ => (u - p) * logDeriv regularizedRiemannZeta (u + 1))
      (𝓝[≠] p) (𝓝 (inverseTiltedXiMultiplicity rho : ℂ)) := by
    simpa only [p] using tendsto_criticalMellin_shiftedLogDeriv_residue rho
  have hgne : ∀ᶠ s : ℂ in 𝓝[≠] p, g s ≠ 0 := by
    have hprod := hres.eventually_ne hm
    filter_upwards [hprod] with s hs
    intro hzero
    have hlog : logDeriv regularizedRiemannZeta (s + 1) = 0 := by
      rw [logDeriv_apply]
      simp [g] at hzero
      simp [hzero]
    exact hs (by simp [hlog])
  have hUev : ∀ᶠ s : ℂ in 𝓝[≠] p, s ∈ U :=
    Filter.Eventually.filter_mono inf_le_left (hUopen.mem_nhds hp)
  have hAg : A =ᶠ[𝓝[≠] p] regularizedCriticalMellinDefect := by
    filter_upwards [hgne, hUev] with s hs hsu
    have hEq : g s * (A s - 1 / (s + 1)) =
        deriv regularizedRiemannZeta (s + 1) := by
      have hzero := hEall hsu
      dsimp only [E] at hzero
      exact sub_eq_zero.mp hzero
    have hsub : A s - 1 / (s + 1) =
        deriv regularizedRiemannZeta (s + 1) / g s := by
      apply (eq_div_iff hs).2
      simpa only [mul_comm] using hEq
    dsimp only [regularizedCriticalMellinDefect]
    rw [logDeriv_apply]
    dsimp only [g] at hsub
    linear_combination hsub
  have horder : meromorphicOrderAt A p =
      meromorphicOrderAt regularizedCriticalMellinDefect p :=
    meromorphicOrderAt_congr hAg
  have hnonneg := (hA p hp).meromorphicOrderAt_nonneg
  rw [horder, show p = criticalMellinXiPole rho from rfl,
    meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one rho] at hnonneg
  exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
    exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg

end

end RHTower
