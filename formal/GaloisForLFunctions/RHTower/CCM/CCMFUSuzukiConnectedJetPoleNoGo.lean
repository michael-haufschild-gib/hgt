import GaloisForLFunctions.RHTower.CCM.CCMHardyHorizontalEndpointZero
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinDivisorTomography

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- The actual regularized completed Mellin defect in the Abel spectral coordinate. -/
def ccmSuzukiConnectedShiftedMellinDefect (u : ℂ) : ℂ :=
  regularizedCriticalMellinDefect (u - 1 / 2)

/-- Finite endpoint-shift jet forced by six spectral derivatives of the connected clock. -/
def ccmSuzukiConnectedSixthJetDefect (ω : ℝ) (u : ℂ) : ℂ :=
  ccmSuzukiConnectedShiftedMellinDefect (u - ω) - ccmSuzukiConnectedShiftedMellinDefect (u + ω) +
    (2 * ω : ℂ) * deriv ccmSuzukiConnectedShiftedMellinDefect u

private theorem analyticAt_regularizedCriticalMellinDefect_rightOfXiEndpoint
    {ρ : ℂ} (hzero : xi ρ = 0)
    (hray : ∀ t : ℝ, 0 < t → xi (ρ + t) ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℂ regularizedCriticalMellinDefect (ρ + t - 1) := by
  have hreρ : 0 < ρ.re := (xi_zero_re_mem_open_unit hzero).1
  have hs : -1 < (ρ + t - 1).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  apply analyticAt_regularizedCriticalMellinDefect_of_regularizedZeta_ne_zero hs
  intro hreg
  obtain ⟨q, hq⟩ :=
    exists_xiDivisorSupport_of_criticalMellin_regularizedZeta_zero hs hreg
  have hqval : (q : ℂ) = ρ + t := by
    rw [criticalMellinXiPole] at hq
    linear_combination hq
  have hxi : xi (ρ + t) = 0 := by
    rw [← hqval]
    exact xi_eq_zero_of_mem_divisor_support q
  exact hray t ht hxi

private theorem not_analyticAt_regularizedCriticalMellinDefect_xiPole
    {ρ : ℂ} (hzero : xi ρ = 0) :
    ¬ AnalyticAt ℂ regularizedCriticalMellinDefect (ρ - 1) := by
  let q : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hzero⟩
  intro han
  have hnonneg := han.meromorphicOrderAt_nonneg
  have hp : ρ - 1 = criticalMellinXiPole q := rfl
  rw [hp, meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one q] at hnonneg
  exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
    exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg

/-- Every fixed positive connected clock moves an actual Xi-divisor pole into the
positive Abel half-plane; its opposite shift and local derivative cannot cancel it. -/
theorem exists_nonanalytic_ccmSuzukiConnectedSixthJetDefect (ω : ℝ) (hω : 0 < ω) :
    ∃ u : ℂ, 0 < u.re ∧ ¬ AnalyticAt ℂ (ccmSuzukiConnectedSixthJetDefect ω) u := by
  obtain ⟨ρ, hzero, hreρ, hray⟩ := exists_rightmost_hardy_height_xi_zero
  let p : ℂ := ρ - 1 / 2 + ω
  have hpPos : 0 < p.re := by
    have hpRe : p.re = ρ.re - 1 / 2 + ω := by
      dsimp only [p]
      norm_num [Complex.add_re, Complex.sub_re]
    rw [hpRe]
    linarith
  refine ⟨p, hpPos, ?_⟩
  have hD1 : AnalyticAt ℂ ccmSuzukiConnectedShiftedMellinDefect p := by
    have h := analyticAt_regularizedCriticalMellinDefect_rightOfXiEndpoint hzero hray hω
    have heq : p - 1 / 2 = ρ + ω - 1 := by dsimp only [p]; ring
    rw [← heq] at h
    have hshift : AnalyticAt ℂ (fun u : ℂ => u - 1 / 2) p := by fun_prop
    exact AnalyticAt.comp (f := fun u : ℂ => u - 1 / 2) h hshift
  have hD2 : AnalyticAt ℂ ccmSuzukiConnectedShiftedMellinDefect (p + ω) := by
    have h := analyticAt_regularizedCriticalMellinDefect_rightOfXiEndpoint hzero hray (by linarith : 0 < 2 * ω)
    have heq : p + ω - 1 / 2 = ρ + (2 * ω : ℝ) - 1 := by dsimp only [p]; push_cast; ring
    rw [← heq] at h
    have hshift : AnalyticAt ℂ (fun u : ℂ => u - 1 / 2) (p + ω) := by fun_prop
    exact AnalyticAt.comp (f := fun u : ℂ => u - 1 / 2) h hshift
  intro hJ
  have hplus : AnalyticAt ℂ (fun u : ℂ => ccmSuzukiConnectedShiftedMellinDefect (u + ω)) p := by
    have hshift : AnalyticAt ℂ (fun u : ℂ => u + ω) p := by fun_prop
    exact AnalyticAt.comp (f := fun u : ℂ => u + ω) hD2 hshift
  have hderiv : AnalyticAt ℂ (fun u : ℂ => (2 * ω : ℂ) * deriv ccmSuzukiConnectedShiftedMellinDefect u) p :=
    analyticAt_const.mul hD1.deriv
  have hminus : AnalyticAt ℂ (fun u : ℂ => ccmSuzukiConnectedShiftedMellinDefect (u - ω)) p := by
    have hfun : (fun u : ℂ => ccmSuzukiConnectedShiftedMellinDefect (u - ω)) =
        (fun u => ccmSuzukiConnectedSixthJetDefect ω u + ccmSuzukiConnectedShiftedMellinDefect (u + ω) -
          (2 * ω : ℂ) * deriv ccmSuzukiConnectedShiftedMellinDefect u) := by
      funext u
      simp only [ccmSuzukiConnectedSixthJetDefect]
      ring
    rw [hfun]
    exact (hJ.add hplus).sub hderiv
  have hinv : AnalyticAt ℂ (fun s : ℂ => s + 1 / 2 + ω) (ρ - 1) := by fun_prop
  have hD0 : AnalyticAt ℂ regularizedCriticalMellinDefect (ρ - 1) := by
    have heq : ρ - 1 + 1 / 2 + ω = p := by dsimp only [p]; ring
    rw [← heq] at hminus
    have hcomp := AnalyticAt.comp
      (f := fun s : ℂ => s + 1 / 2 + ω) hminus hinv
    convert hcomp using 1
    funext s
    simp only [ccmSuzukiConnectedShiftedMellinDefect, Function.comp_def]
    congr 1
    ring
  exact not_analyticAt_regularizedCriticalMellinDefect_xiPole hzero hD0

/-- No fixed positive connected-clock sixth jet is holomorphic throughout the
positive Abel half-plane. This uses the actual Xi divisor, not a model pole. -/
theorem not_analyticOnNhd_ccmSuzukiConnectedSixthJetDefect_rightHalfPlane
    (ω : ℝ) (hω : 0 < ω) :
    ¬ AnalyticOnNhd ℂ (ccmSuzukiConnectedSixthJetDefect ω)
        {u : ℂ | 0 < u.re} := by
  intro h
  obtain ⟨u, hu, hnot⟩ := exists_nonanalytic_ccmSuzukiConnectedSixthJetDefect ω hω
  exact hnot (h u hu)

end

end RHTower
