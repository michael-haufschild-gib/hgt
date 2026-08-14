import GaloisForLFunctions.RHTower.SmoothAFEDualFactorization
import GaloisForLFunctions.RHTower.ArchLadderRegular

/-!
# Height derivative of the exact zeta-AFE chi shift ratio

The height derivative of `chi(s+w)/chi(s)` is the ratio itself times a *difference* of logarithmic
derivatives.  On the dual-weight contour `w = -(1+iv)`, the two leading `log |tau|` contributions
cancel exactly.  The remaining slope is a pair of digamma increments, exposing the slow conductor
variation needed for a moving-coefficient mean-square theorem.
-/

noncomputable section

open Complex Filter

namespace RHTower

/-- Raw quotient-rule derivative of the exact chi shift ratio along the critical height. -/
theorem hasDerivAt_smoothAFEZetaChiShiftRatio_line
    {tau : ℝ} {w : ℂ} (hnum : Gammaℝ (1 - (linePt tau + w)) ≠ 0) :
    HasDerivAt (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u) w)
      (((deriv zetaChi (linePt tau + w) * I) * zetaChi (linePt tau) -
          zetaChi (linePt tau + w) * (deriv zetaChi (linePt tau) * I)) /
        zetaChi (linePt tau) ^ 2) tau := by
  have hn := ((zetaChi_analyticAt hnum).differentiableAt.hasDerivAt.comp tau
    ((hasDerivAt_linePt tau).add_const w))
  have hbase : Gammaℝ (1 - linePt tau) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re, linePt_re]
      norm_num)
  have hd := ((zetaChi_analyticAt (z := linePt tau) hbase).differentiableAt.hasDerivAt.comp tau
    (hasDerivAt_linePt tau))
  unfold smoothAFEZetaChiShiftRatio
  exact (hn.div hd (zetaChi_line_ne_zero tau)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Logarithmic-derivative form of the critical-height chi-ratio derivative. -/
theorem hasDerivAt_smoothAFEZetaChiShiftRatio_line_logDeriv
    {tau : ℝ} {w : ℂ} (hnumA : Gammaℝ (1 - (linePt tau + w)) ≠ 0)
    (hnum0 : zetaChi (linePt tau + w) ≠ 0) :
    HasDerivAt (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u) w)
      (I * smoothAFEZetaChiShiftRatio (linePt tau) w *
        (logDeriv zetaChi (linePt tau + w) - logDeriv zetaChi (linePt tau))) tau := by
  have hraw := hasDerivAt_smoothAFEZetaChiShiftRatio_line hnumA
  convert hraw using 1
  unfold smoothAFEZetaChiShiftRatio
  rw [logDeriv_apply, logDeriv_apply]
  field_simp [hnum0, zetaChi_line_ne_zero tau]

/-- Closed logarithmic derivative of zeta's chi factor away from Gamma poles. -/
theorem logDeriv_zetaChi_off_poles {z : ℂ}
    (hz : ∀ m : ℕ, z / 2 ≠ -(m : ℂ))
    (h1z : ∀ m : ℕ, (1 - z) / 2 ≠ -(m : ℂ)) :
    logDeriv zetaChi z =
      -(Complex.digamma (z / 2) / 2) -
        Complex.digamma ((1 - z) / 2) / 2 + (Real.log Real.pi : ℂ) := by
  have hz0 := Gammaℝ_ne_zero_off_poles hz
  have h1z0 := Gammaℝ_ne_zero_off_poles h1z
  have hden := (hasDerivAt_Gammaℝ_off_poles hz).differentiableAt
  have hinner : HasDerivAt (fun q : ℂ => 1 - q) (-1) z :=
    (hasDerivAt_id z).const_sub 1
  have hnumDeriv : HasDerivAt (fun q : ℂ => Gammaℝ (1 - q))
      (Gammaℝ (1 - z) *
        (Complex.digamma ((1 - z) / 2) / 2 - (Real.log Real.pi : ℂ) / 2) * (-1)) z := by
    exact ((hasDerivAt_Gammaℝ_off_poles h1z).comp z hinner).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hnum := hnumDeriv.differentiableAt
  have hLDnum : logDeriv (fun q : ℂ => Gammaℝ (1 - q)) z =
      -(logDeriv Gammaℝ (1 - z)) := by
    rw [logDeriv_apply, hnumDeriv.deriv, logDeriv_apply,
      (hasDerivAt_Gammaℝ_off_poles h1z).deriv]
    field_simp [h1z0]
  unfold zetaChi
  rw [logDeriv_div (f := fun q : ℂ => Gammaℝ (1 - q)) (g := Gammaℝ)
      z h1z0 hz0 hnum hden, hLDnum,
    logDeriv_Gammaℝ_off_poles hz, logDeriv_Gammaℝ_off_poles h1z]
  ring

theorem div_two_ne_neg_nat_of_re_eq_neg_half {z : ℂ}
    (hz : z.re = -1 / 2) :
    ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
  intro m hm
  have hre := congrArg Complex.re hm
  rw [re_div_two, hz, Complex.neg_re, Complex.natCast_re] at hre
  cases m with
  | zero => norm_num at hre
  | succ m =>
      have hm1 : (1 : ℝ) ≤ (Nat.succ m : ℕ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      norm_num at hre
      linarith

/-- The shifted chi factor on the positive dual contour is unconditionally nonzero. -/
theorem zetaChi_line_add_neg_right_one_ne_zero (tau v : ℝ) :
    zetaChi (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) ≠ 0 := by
  let z : ℂ := linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  have hzre : z.re = -1 / 2 := by
    dsimp only [z]
    rw [Complex.sub_re, linePt_re, Complex.add_re]
    norm_num
  have hzPole : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) :=
    div_two_ne_neg_nat_of_re_eq_neg_half hzre
  have h1zpos : 0 < (1 - z).re := by
    rw [Complex.sub_re, Complex.one_re, hzre]
    norm_num
  unfold zetaChi
  exact div_ne_zero (Gammaℝ_ne_zero_of_re_pos h1zpos)
    (Gammaℝ_ne_zero_off_poles hzPole)

/-- On the dual contour, the logarithmic slope is exactly two digamma increments; constants and
leading logarithmic modes cancel before estimation. -/
theorem logDeriv_zetaChi_shift_sub_line_eq_digamma_increments (tau v : ℝ) :
    logDeriv zetaChi
          (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau) =
      -(Complex.digamma
          ((linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2) -
          Complex.digamma (linePt tau / 2)) / 2 -
        (Complex.digamma
          ((1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2) -
          Complex.digamma ((1 - linePt tau) / 2)) / 2 := by
  let z : ℂ := linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  have hzre : z.re = -1 / 2 := by
    dsimp only [z]
    rw [Complex.sub_re, linePt_re, Complex.add_re]
    norm_num
  have hzPole : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) :=
    div_two_ne_neg_nat_of_re_eq_neg_half hzre
  have h1zpos : 0 < (1 - z).re := by
    rw [Complex.sub_re, Complex.one_re, hzre]
    norm_num
  have hspos : 0 < (linePt tau).re := by rw [linePt_re]; norm_num
  have h1spos : 0 < (1 - linePt tau).re := by
    rw [Complex.sub_re, Complex.one_re, linePt_re]
    norm_num
  rw [show linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I) = z by rfl,
    logDeriv_zetaChi_off_poles hzPole (div_two_ne_neg_nat_of_re_pos h1zpos),
    logDeriv_zetaChi_off_poles (div_two_ne_neg_nat_of_re_pos hspos)
      (div_two_ne_neg_nat_of_re_pos h1spos)]
  ring

/-- Exact slow-slope derivative on the positive dual-weight contour. -/
theorem hasDerivAt_smoothAFEZetaChiShiftRatio_neg_right_one_line (tau v : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)))
      (I * smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        (logDeriv zetaChi
            (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
          logDeriv zetaChi (linePt tau))) tau := by
  have hnumA : Gammaℝ
      (1 - (linePt tau + -(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    rw [Complex.sub_re, Complex.one_re, Complex.add_re, linePt_re, Complex.neg_re,
      Complex.add_re]
    norm_num
  have hnum0 : zetaChi
      (linePt tau + -(((1 : ℝ) : ℂ) + (v : ℂ) * I)) ≠ 0 := by
    simpa only [sub_eq_add_neg] using zetaChi_line_add_neg_right_one_ne_zero tau v
  simpa only [sub_eq_add_neg] using
    (hasDerivAt_smoothAFEZetaChiShiftRatio_line_logDeriv hnumA hnum0)

end RHTower
