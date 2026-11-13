import GaloisForLFunctions.ConjugateDiagonalGeometry.TheLogarithmicDerivativeIsSmallOutsideTheZeroStrip
import GaloisForLFunctions.RHTower.ZetaSquareStirlingCarrier
import GaloisForLFunctions.RHTower.CompletedSplitRightHalfPlane
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Boundary asymptotics of the residue unit

For `G(s)=(s-1)ζ(s)`, the logarithmic derivative is `o(log |t|)` on each
fixed line between seven eighths and one. Reflection and Stirling give
`G'/G(σ+it)=-log |t|+o(log |t|)` on each fixed line between zero and one eighth.
Both estimates hold at either sign of the height.
-/

noncomputable section

open Complex Filter Topology

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open _root_.RHTower
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

private theorem exists_constant_le_epsilon_log {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∃ T : ℝ, 8 ≤ T ∧ ∀ t : ℝ, T ≤ |t| → C ≤ ε * Real.log |t| := by
  refine ⟨max 8 (Real.exp (C / ε)), le_max_left _ _, ?_⟩
  intro t ht
  have he : Real.exp (C / ε) ≤ |t| := (le_max_right _ _).trans ht
  have hl := Real.log_le_log (Real.exp_pos (C / ε)) he
  rw [Real.log_exp] at hl
  have h := (div_le_iff₀ hε).mp hl
  simpa only [mul_comm] using h

private theorem norm_line_pole_inv_le_one (σ t : ℝ) (ht : 1 ≤ |t|) :
    ‖(((σ : ℂ) + (t : ℂ) * I) - 1)⁻¹‖ ≤ 1 := by
  have hi := Complex.abs_im_le_norm (((σ : ℂ) + (t : ℂ) * I) - 1)
  have him : (((σ : ℂ) + (t : ℂ) * I) - 1).im = t := by norm_num
  rw [him] at hi
  have hn : 1 ≤ ‖((σ : ℂ) + (t : ℂ) * I) - 1‖ := ht.trans hi
  rw [norm_inv, ← one_div]
  simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hn

private theorem residueUnit_logDeriv_eq_add_inv {s : ℂ}
    (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv zetaResidueUnit s = logDeriv riemannZeta s + (s - 1)⁻¹ := by
  have hG : zetaResidueUnit s ≠ 0 := by
    rw [(zetaResidueUnit_eventuallyEq hs).eq_of_nhds]
    exact mul_ne_zero (sub_ne_zero.mpr hs) hz
  have h := logDeriv_zeta_eq hs hG
  linear_combination -h

/-- The pole removal does not change the sublogarithmic right-boundary estimate. -/
theorem exists_logDeriv_residueUnit_right_le_epsilon_log {σ ε : ℝ}
    (hσ : (7 : ℝ) / 8 < σ) (hσ1 : σ < 1) (hε : 0 < ε) :
    ∃ T : ℝ, 8 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      ‖logDeriv zetaResidueUnit ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        ε * Real.log |t| := by
  obtain ⟨T₀, hT₀, hb⟩ := exists_logDeriv_zeta_le_epsilon_log hσ hσ1
    (show 0 < ε / 2 by positivity)
  obtain ⟨T₁, _, hc⟩ := exists_constant_le_epsilon_log
    (show 0 < ε / 2 by positivity) 1
  refine ⟨max T₀ T₁, hT₀.trans (le_max_left _ _), ?_⟩
  intro t ht
  have ht₀ := (le_max_left T₀ T₁).trans ht
  have ht₁ := (le_max_right T₀ T₁).trans ht
  have hs : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro hs
    have h := congrArg Complex.re hs
    norm_num at h
    linarith only [h, hσ1]
  have hz : riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_seven_eighths_lt_re (by simpa using hσ)
  rw [residueUnit_logDeriv_eq_add_inv hs hz]
  have hp := norm_line_pole_inv_le_one σ t (by linarith only [hT₀.trans ht₀])
  exact (norm_add_le _ _).trans (by linarith only [hb t ht₀, hc t ht₁, hp])

/-- The chi logarithmic derivative differs from `-log |t|` by a fixed constant
throughout the closed critical strip at large height. -/
theorem norm_logDeriv_zetaChi_add_log_le_boundary_constant {σ t : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (ht : 8 ≤ |t|) :
    ‖logDeriv zetaChi ((σ : ℂ) + (t : ℂ) * I) + (Real.log |t| : ℂ)‖ ≤
      36 + |Real.log (2 * Real.pi)| := by
  have hu : ‖((σ - 1 / 2 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith only [hσ0, hσ1]
  have hchi := ZetaNotch.norm_logDeriv_zetaChi_linePt_add_log_le
    (show 4 ≤ |t| by linarith only [ht])
    (u := ((σ - 1 / 2 : ℝ) : ℂ))
    (by simp only [Complex.ofReal_re]; linarith only [hσ0])
    (by simp only [Complex.ofReal_re]; linarith only [hσ1])
    (by simp only [Complex.ofReal_im, abs_zero, mul_zero]; exact (abs_nonneg t))
  have he : linePt t + ((σ - 1 / 2 : ℝ) : ℂ) =
      (σ : ℂ) + (t : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  rw [he] at hchi
  have ht1 : 1 ≤ |t| := by linarith only [ht]
  have ht2 : 1 ≤ t ^ 2 := by nlinarith only [sq_abs t, ht1]
  have hdiv1 := div_le_self (by positivity : 0 ≤ 10 * ‖((σ - 1 / 2 : ℝ) : ℂ)‖) ht1
  have hdiv2 := div_le_self (by norm_num : (0 : ℝ) ≤ 26) ht2
  have hbase : ‖logDeriv zetaChi ((σ : ℂ) + (t : ℂ) * I) +
      (Real.log (|t| / (2 * Real.pi)) : ℂ)‖ ≤ 36 := by
    linarith only [hchi, hdiv1, hdiv2, hu]
  have heq : logDeriv zetaChi ((σ : ℂ) + (t : ℂ) * I) + (Real.log |t| : ℂ) =
      (logDeriv zetaChi ((σ : ℂ) + (t : ℂ) * I) +
        (Real.log (|t| / (2 * Real.pi)) : ℂ)) + (Real.log (2 * Real.pi) : ℂ) := by
    rw [Real.log_div (by linarith only [ht] : |t| ≠ 0) (by positivity : 2 * Real.pi ≠ 0)]
    push_cast
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact add_le_add_right hbase _)

/-- Reflection gives the full main term on the left boundary of the zero strip. -/
theorem exists_logDeriv_residueUnit_left_add_log_le_epsilon_log {σ ε : ℝ}
    (hσ0 : 0 < σ) (hσ : σ < (1 : ℝ) / 8) (hε : 0 < ε) :
    ∃ T : ℝ, 8 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      ‖logDeriv zetaResidueUnit ((σ : ℂ) + (t : ℂ) * I) +
        (Real.log |t| : ℂ)‖ ≤ ε * Real.log |t| := by
  obtain ⟨T₀, hT₀, hb⟩ := exists_logDeriv_zeta_le_epsilon_log
    (σ := 1 - σ) (by linarith only [hσ]) (by linarith only [hσ0])
    (show 0 < ε / 2 by positivity)
  obtain ⟨T₁, _, hc⟩ := exists_constant_le_epsilon_log
    (show 0 < ε / 2 by positivity) (37 + |Real.log (2 * Real.pi)|)
  refine ⟨max T₀ T₁, hT₀.trans (le_max_left _ _), ?_⟩
  intro t ht
  have ht₀ := (le_max_left T₀ T₁).trans ht
  have ht₁ := (le_max_right T₀ T₁).trans ht
  have ht8 : 8 ≤ |t| := hT₀.trans ht₀
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs0 : 0 < s.re := by simpa only [s, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_self, add_zero] using hσ0
  have hs1 : s.re < 1 := by dsimp [s]; norm_num; linarith only [hσ]
  have hs : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs1
    exact lt_irrefl _ hs1
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_re_lt_one_eighth hs0
    (by dsimp [s]; norm_num; exact hσ)
  have hrefre : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith only [hs1]
  have hzr : riemannZeta (1 - s) ≠ 0 :=
    riemannZeta_ne_zero_of_seven_eighths_lt_re (by dsimp [s]; norm_num; linarith only [hσ])
  have hfe := logDeriv_riemannZeta_add_reflect_of_strip hs0 hs1 hz hzr
  have hchi := logDeriv_zetaChi_off_poles
    (div_two_ne_neg_nat_of_re_pos hs0) (div_two_ne_neg_nat_of_re_pos hrefre)
  have hG := residueUnit_logDeriv_eq_add_inv hs hz
  have heq : logDeriv zetaResidueUnit s + (Real.log |t| : ℂ) =
      (logDeriv zetaChi s + (Real.log |t| : ℂ)) -
        logDeriv riemannZeta (1 - s) + (s - 1)⁻¹ := by
    linear_combination hG + hfe - hchi
  have hreflect : 1 - s = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    dsimp [s]
    push_cast
    ring
  have hright : ‖logDeriv riemannZeta (1 - s)‖ ≤ ε / 2 * Real.log |t| := by
    rw [hreflect]
    simpa only [abs_neg] using hb (-t) (by simpa only [abs_neg] using ht₀)
  have harch := norm_logDeriv_zetaChi_add_log_le_boundary_constant hσ0.le
    (show σ ≤ 1 by linarith only [hσ]) ht8
  have hp := norm_line_pole_inv_le_one σ t (show 1 ≤ |t| by linarith only [ht8])
  change ‖logDeriv zetaResidueUnit s + (Real.log |t| : ℂ)‖ ≤ _
  rw [heq]
  calc ‖(logDeriv zetaChi s + (Real.log |t| : ℂ)) -
          logDeriv riemannZeta (1 - s) + (s - 1)⁻¹‖
      ≤ ‖logDeriv zetaChi s + (Real.log |t| : ℂ)‖ +
          ‖logDeriv riemannZeta (1 - s)‖ + ‖(s - 1)⁻¹‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ ε * Real.log |t| := by linarith only [harch, hright, hp, hc t ht₁]

end GaloisForLFunctions.ConjugateDiagonalGeometry
