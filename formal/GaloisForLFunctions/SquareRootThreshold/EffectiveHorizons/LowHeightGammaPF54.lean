import GaloisForLFunctions.RHTower.DigammaLeLog
import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount
import GaloisForLFunctions.RHTower.XiSliceCoeffOrderTwentyThreeBand

/-!
# The retained Gamma constant gives PF54 at the centre

At real part `5/4`, the negative constant in the Gamma logarithmic derivative strengthens
the three-four-one inequality on heights `[14,18]`. The functional-equation pair gives depth
bounds `5/12` through height 16 and `7/16` through 18.
Together with the fourth-trace height floor, this places every Xi zero in the PF54 cone.
-/

open Complex RHTower GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SquareRootThreshold

noncomputable section

private theorem eleven_tenths_le_log_pi : (11 / 10 : ℝ) ≤ Real.log Real.pi := by
  have he : Real.exp (1 / 10 : ℝ) ≤ 10 / 9 := by
    have h := Real.add_one_le_exp (-(1 / 10 : ℝ))
    rw [Real.exp_neg] at h
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)] at h
    norm_num at h
    exact h
  have he1 : Real.exp (1 : ℝ) ≤ 11 / 4 := by linarith [Real.exp_one_lt_d9]
  have hexp : Real.exp (11 / 10 : ℝ) < Real.pi := by
    rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, Real.exp_add]
    have hb := mul_le_mul he1 he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 11 / 4)
    linarith [Real.pi_gt_d2]
  have h := Real.log_le_log (Real.exp_pos _) hexp.le
  simpa only [Real.log_exp] using h

/-- Keeping the factor `2π` in Stirling's formula pays a fixed negative constant. -/
private theorem gamma_five_fourths_le {t : ℝ} (ht : 14 ≤ t) :
    (logDeriv Complex.Gammaℝ ((5 / 4 : ℂ) + t * I)).re ≤
      Real.log t / 2 - 27 / 40 := by
  let s : ℂ := (5 / 4 : ℂ) + t * I
  have hsre : s.re = 5 / 4 := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hn : ‖s / 2‖ ^ 2 = ((5 / 4 : ℝ) ^ 2 + t ^ 2) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.div_ofNat_re, Complex.div_ofNat_im, hsre, hsim]
    ring
  have hn0 := norm_nonneg (s / 2)
  have hlow : t / 2 ≤ ‖s / 2‖ := by nlinarith only [hn, hn0, ht]
  have hupp : ‖s / 2‖ ≤ 101 * t / 200 := by nlinarith only [hn, hn0, ht]
  have hnpos : 0 < ‖s / 2‖ := by linarith
  have hlog := Real.log_le_log hnpos hupp
  have hlogid : Real.log (101 * t / 200) =
      Real.log t - Real.log 2 + Real.log (101 / 100 : ℝ) := by
    rw [show 101 * t / 200 = (t / 2) * (101 / 100 : ℝ) by ring,
      Real.log_mul (by positivity) (by norm_num),
      Real.log_div (by linarith : t ≠ 0) (by norm_num)]
  rw [hlogid] at hlog
  have hsmall : Real.log (101 / 100 : ℝ) ≤ 1 / 100 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 101 / 100)
    linarith
  have herror : 3 / ‖s / 2‖ ≤ 3 / 7 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    linarith
  have hstir := norm_digamma_sub_log_le_of_re_pos (z := s / 2)
    (by rw [Complex.div_ofNat_re, hsre]; norm_num) (by linarith)
  have hpsi := (Complex.re_le_norm (Complex.digamma (s / 2) - Complex.log (s / 2))).trans hstir
  rw [Complex.sub_re, Complex.log_re] at hpsi
  have hG := logDeriv_Gammaℝ_digamma (s := s) (by rw [hsre]; norm_num)
  change (logDeriv Complex.Gammaℝ s).re ≤ _
  rw [hG]
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
  linarith [Real.log_two_gt_d9, eleven_tenths_le_log_pi]

/-- The two rational pole terms consume at most `1/120` above height fourteen. -/
private theorem pole_five_fourths_le {t : ℝ} (ht : 14 ≤ t) :
    (1 / ((5 / 4 : ℂ) + t * I)).re +
      (1 / (((5 / 4 : ℂ) + t * I) - 1)).re ≤ 1 / 120 := by
  let s : ℂ := (5 / 4 : ℂ) + t * I
  have hsre : s.re = 5 / 4 := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hnorm : Complex.normSq s = 25 / 16 + t ^ 2 := by
    rw [Complex.normSq_apply, hsre, hsim]
    ring
  have hnorm1 : Complex.normSq (s - 1) = 1 / 16 + t ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hsre, hsim]
    norm_num
    ring
  have ht2 : (196 : ℝ) ≤ t ^ 2 := by nlinarith only [ht]
  have hA : (1 / s).re ≤ 5 / 784 := by
    rw [one_div, Complex.inv_re, hsre, hnorm]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [ht2]
  have hB : (1 / (s - 1)).re ≤ 1 / 784 := by
    rw [one_div, Complex.inv_re, Complex.sub_re, hsre, Complex.one_re, hnorm1]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [ht2]
  change (1 / s).re + (1 / (s - 1)).re ≤ _
  linarith

/-- Landau's identity with its full Xi term retained. -/
private theorem zeta_five_fourths_le_sub_xi {t : ℝ} (ht : 14 ≤ t) :
    -(logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re ≤
      Real.log t / 2 - 2 / 3 - (logDeriv xi ((5 / 4 : ℂ) + t * I)).re := by
  let s : ℂ := (5 / 4 : ℂ) + t * I
  have hs : 1 < s.re := by norm_num [s]
  have hfour := logDeriv_xi_fourFactor hs
  have hG := logDeriv_Gammaℝ_digamma (s := s) (by linarith)
  have hid : logDeriv riemannZeta s =
      logDeriv xi s - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s := by
    rw [hG, hfour]
    ring
  change -(logDeriv riemannZeta s).re ≤ _
  rw [hid]
  simp only [Complex.sub_re]
  have hgamma := gamma_five_fourths_le ht
  have hpole := pole_five_fourths_le ht
  change (logDeriv Complex.Gammaℝ s).re ≤ _ at hgamma
  change (1 / s).re + (1 / (s - 1)).re ≤ _ at hpole
  change _ ≤ Real.log t / 2 - 2 / 3 - (logDeriv xi s).re
  linarith

/-- Three-four-one bounds the complete Xi response before any zero term is discarded. -/
private theorem xi_response_upper {t : ℝ} (ht : 14 ≤ t) :
    4 * (logDeriv xi ((5 / 4 : ℂ) + t * I)).re ≤
      12 + 5 / 2 * Real.log t + Real.log 2 / 2 - 59 / 15 := by
  have hmain := zeta_five_fourths_le_sub_xi ht
  have hdouble := zeta_five_fourths_le_sub_xi (t := 2 * t) (by linarith)
  have hxi : 0 ≤ (logDeriv xi ((5 / 4 : ℂ) + (2 * t : ℝ) * I)).re :=
    (re_logDeriv_xi_pos_of_one_le_re
      (s := (5 / 4 : ℂ) + (2 * t : ℝ) * I) (by norm_num)).le
  have hA := neg_re_logDeriv_riemannZeta_real_le_neg
    (σ := 5 / 4) (by norm_num) (by norm_num)
  have hB : (-deriv riemannZeta (((5 / 4 : ℝ) : ℂ) + (2 * t : ℂ) * I) /
      riemannZeta (((5 / 4 : ℝ) : ℂ) + (2 * t : ℂ) * I)).re ≤
        Real.log (2 * t) / 2 - 2 / 3 := by
    rw [Sieve.neg_div_re_eq_neg_logDeriv_re]
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
    push_cast at hdouble hxi
    linarith only [hdouble, hxi]
  have hshift := Sieve.re_logDeriv_shift_le (σ := 5 / 4) (t := t) (by norm_num) hA hB
  rw [Sieve.neg_div_re_eq_neg_logDeriv_re] at hshift
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hshift
  rw [Real.log_mul (by norm_num) (by linarith : t ≠ 0)] at hshift
  linarith only [hmain, hshift]

/-- Distinct line-conjugate copies contribute both resonant terms, with no factor lost to pairing. -/
private theorem xi_response_lower_pair (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    1 / (5 / 4 - (q.1 : ℂ).re) + 1 / (1 / 4 + (q.1 : ℂ).re) ≤
      (logDeriv xi ((5 / 4 : ℂ) + (q.1 : ℂ).im * I)).re := by
  classical
  let s : ℂ := (5 / 4 : ℂ) + (q.1 : ℂ).im * I
  have hsre : s.re = 5 / 4 := by simp [s]
  have hsim : s.im = (q.1 : ℂ).im := by simp [s]
  have hs : xi s ≠ 0 := xi_ne_zero_of_one_le_re (by rw [hsre]; norm_num)
  have hnn (r : XiZeroCopy) :
      0 ≤ xiLinePairRe (s.re - 1 / 2) ((r.1 : ℂ).re - 1 / 2) (s.im - (r.1 : ℂ).im) := by
    have h0 := xiZeroCopy_re_pos r
    have h1 := xiZeroCopy_re_lt_one r
    rw [hsre]
    unfold xiLinePairRe
    apply add_nonneg
    · exact div_nonneg (by linarith) (by positivity)
    · exact div_nonneg (by linarith) (by positivity)
  have hsum := sum_pair_le_two_mul_re_logDeriv_xi hs hnn
    ({q, xiZeroCopyLineConjEquiv q} : Finset XiZeroCopy)
  rw [Finset.sum_pair (xiZeroCopy_ne_lineConj_of_re_ne_half q hoff)] at hsum
  have hJ : xiLinePairRe (s.re - 1 / 2)
      (((xiZeroCopyLineConjEquiv q).1 : ℂ).re - 1 / 2)
      (s.im - ((xiZeroCopyLineConjEquiv q).1 : ℂ).im) =
        xiLinePairRe (s.re - 1 / 2) ((q.1 : ℂ).re - 1 / 2) (s.im - (q.1 : ℂ).im) := by
    rw [xiZero_lineConj_eq]
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re,
      Complex.sub_im, Complex.one_im, Complex.conj_im]
    have ha : 1 - (q.1 : ℂ).re - 1 / 2 = -((q.1 : ℂ).re - 1 / 2) := by ring
    rw [ha]
    unfold xiLinePairRe
    rw [sub_neg_eq_add, show s.re - 1 / 2 + -((q.1 : ℂ).re - 1 / 2) =
      s.re - 1 / 2 - ((q.1 : ℂ).re - 1 / 2) by ring]
    ring
  rw [hJ, hsre, hsim, sub_self] at hsum
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hneA : 5 / 4 - (q.1 : ℂ).re ≠ 0 := by linarith
  have hneB : 1 / 4 + (q.1 : ℂ).re ≠ 0 := by linarith
  have hv : xiLinePairRe (5 / 4 - 1 / 2) ((q.1 : ℂ).re - 1 / 2) 0 =
      1 / (5 / 4 - (q.1 : ℂ).re) + 1 / (1 / 4 + (q.1 : ℂ).re) := by
    unfold xiLinePairRe
    rw [show 5 / 4 - 1 / 2 - ((q.1 : ℂ).re - 1 / 2) = 5 / 4 - (q.1 : ℂ).re by ring,
      show 5 / 4 - 1 / 2 + ((q.1 : ℂ).re - 1 / 2) = 1 / 4 + (q.1 : ℂ).re by ring]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    field_simp
  rw [hv] at hsum
  change _ ≤ (logDeriv xi s).re
  linarith only [hsum]

/-- The paired resonant response increases strictly with depth right of the critical line. -/
private theorem paired_response_strict {b β : ℝ}
    (hb : 1 / 2 < b) (hβ : b < β) (hβ1 : β < 1) :
    (3 / 2) / ((5 / 4 - b) * (1 / 4 + b)) <
      1 / (5 / 4 - β) + 1 / (1 / 4 + β) := by
  have hA : 0 < 5 / 4 - β := by linarith
  have hB : 0 < 1 / 4 + β := by linarith
  have hAb : 0 < 5 / 4 - b := by linarith
  have hBb : 0 < 1 / 4 + b := by linarith
  have hid : 1 / (5 / 4 - β) + 1 / (1 / 4 + β) =
      (3 / 2) / ((5 / 4 - β) * (1 / 4 + β)) := by
    rw [div_add_div _ _ hA.ne' hB.ne']
    congr 1
    ring
  rw [hid, div_lt_div_iff₀ (mul_pos hAb hBb) (mul_pos hA hB)]
  nlinarith only [mul_pos (sub_pos.mpr hβ) (show 0 < β + b - 1 by linarith)]

private theorem xiZeroCopy_re_le_eleven_twelfths (q : XiZeroCopy)
    (hlo : 14 ≤ (q.1 : ℂ).im) (hhi : (q.1 : ℂ).im ≤ 16) :
    (q.1 : ℂ).re ≤ 11 / 12 := by
  by_contra h
  have hβ : 11 / 12 < (q.1 : ℂ).re := not_le.mp h
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by linarith
  have hlower := xi_response_lower_pair q hoff
  have hstrict := paired_response_strict (by norm_num : (1 / 2 : ℝ) < 11 / 12)
    hβ (xiZeroCopy_re_lt_one q)
  norm_num at hstrict
  simp only [one_div] at hlower
  have hupper := xi_response_upper hlo
  have hlog : Real.log (q.1 : ℂ).im ≤ 4 * Real.log 2 := by
    have h := Real.log_le_log (by linarith : 0 < (q.1 : ℂ).im) hhi
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at h
    norm_num at h
    exact h
  linarith only [hstrict, hlower, hupper, hlog, Real.log_two_lt_d9]

private theorem log_eighteen_le_three : Real.log (18 : ℝ) ≤ 3 := by
  have he : (8 / 3 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 8 / 3) (by norm_num : (3 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 18) (by linarith : (18 : ℝ) ≤ Real.exp 3)
  simpa only [Real.log_exp] using h

private theorem xiZeroCopy_re_le_fifteen_sixteenths (q : XiZeroCopy)
    (hlo : 14 ≤ (q.1 : ℂ).im) (hhi : (q.1 : ℂ).im ≤ 18) :
    (q.1 : ℂ).re ≤ 15 / 16 := by
  by_contra h
  have hβ : 15 / 16 < (q.1 : ℂ).re := not_le.mp h
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by linarith
  have hlower := xi_response_lower_pair q hoff
  have hstrict := paired_response_strict (by norm_num : (1 / 2 : ℝ) < 15 / 16)
    hβ (xiZeroCopy_re_lt_one q)
  norm_num at hstrict
  simp only [one_div] at hlower
  have hupper := xi_response_upper hlo
  have hlog := (Real.log_le_log (by linarith : 0 < (q.1 : ℂ).im) hhi).trans log_eighteen_le_three
  linarith only [hstrict, hlower, hupper, hlog, Real.log_two_lt_d9]

/-- Reflecting both coordinates turns a right-edge estimate into a depth estimate. -/
private theorem depth_bound_of_right_bound {H b : ℝ}
    (hright : ∀ r : XiZeroCopy, 14 ≤ (r.1 : ℂ).im → (r.1 : ℂ).im ≤ H → (r.1 : ℂ).re ≤ b)
    (q : XiZeroCopy) (hlo : 14 ≤ |(q.1 : ℂ).im|) (hhi : |(q.1 : ℂ).im| ≤ H) :
    |(q.1 : ℂ).re - 1 / 2| ≤ b - 1 / 2 := by
  have habs (r : XiZeroCopy) (hl : 14 ≤ |(r.1 : ℂ).im|)
      (hh : |(r.1 : ℂ).im| ≤ H) : (r.1 : ℂ).re ≤ b := by
    by_cases hsign : 0 ≤ (r.1 : ℂ).im
    · rw [abs_of_nonneg hsign] at hl hh
      exact hright r hl hh
    · rw [abs_of_neg (lt_of_not_ge hsign)] at hl hh
      have hl' : 14 ≤ ((xiZeroCopyConjEquiv r).1 : ℂ).im := by
        change 14 ≤ ((starRingEnd ℂ) (r.1 : ℂ)).im
        simpa only [Complex.conj_im] using hl
      have hh' : ((xiZeroCopyConjEquiv r).1 : ℂ).im ≤ H := by
        change ((starRingEnd ℂ) (r.1 : ℂ)).im ≤ H
        simpa only [Complex.conj_im] using hh
      have h := hright (xiZeroCopyConjEquiv r) hl' hh'
      change ((starRingEnd ℂ) (r.1 : ℂ)).re ≤ b at h
      simpa only [Complex.conj_re] using h
  have hr := habs q hlo hhi
  have hl' : 14 ≤ |((xiZeroCopyLineConjEquiv q).1 : ℂ).im| := by
    rw [xiZero_lineConj_eq]
    simpa using hlo
  have hh' : |((xiZeroCopyLineConjEquiv q).1 : ℂ).im| ≤ H := by
    rw [xiZero_lineConj_eq]
    simpa using hhi
  have hl := habs (xiZeroCopyLineConjEquiv q) hl' hh'
  rw [xiZero_lineConj_eq] at hl
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hl
  rw [abs_le]
  constructor <;> linarith only [hr, hl]

/-- Every Xi zero between absolute heights fourteen and sixteen has depth at most `5/12`. -/
theorem xiZeroCopy_depth_le_five_twelfths (q : XiZeroCopy)
    (hlo : 14 ≤ |(q.1 : ℂ).im|) (hhi : |(q.1 : ℂ).im| ≤ 16) :
    |(q.1 : ℂ).re - 1 / 2| ≤ 5 / 12 := by
  have h := depth_bound_of_right_bound xiZeroCopy_re_le_eleven_twelfths q hlo hhi
  norm_num at h ⊢
  exact h

/-- Every Xi zero between absolute heights fourteen and eighteen has depth at most `7/16`. -/
theorem xiZeroCopy_depth_le_seven_sixteenths (q : XiZeroCopy)
    (hlo : 14 ≤ |(q.1 : ℂ).im|) (hhi : |(q.1 : ℂ).im| ≤ 18) :
    |(q.1 : ℂ).re - 1 / 2| ≤ 7 / 16 := by
  have h := depth_bound_of_right_bound xiZeroCopy_re_le_fifteen_sixteenths q hlo hhi
  norm_num at h ⊢
  exact h

private theorem one_sub_cos_pi_div_fiftyFive_ge :
    (162 / 100000 : ℝ) ≤ 1 - Real.cos (Real.pi / 55) := by
  let θ := Real.pi / 55
  have hθ0 : 0 ≤ θ := by positivity
  have hθlo : 3.14 / 55 < θ := div_lt_div_of_pos_right Real.pi_gt_d2 (by norm_num)
  have hθhi : θ < 3.15 / 55 := div_lt_div_of_pos_right Real.pi_lt_d2 (by norm_num)
  have hθ1 : |θ| ≤ 1 := by rw [abs_of_nonneg hθ0]; linarith
  have hb := Real.cos_bound hθ1
  rw [abs_of_nonneg hθ0] at hb
  have hb2 := (abs_le.mp hb).2
  have h2 := pow_lt_pow_left₀ hθlo (by norm_num : (0 : ℝ) ≤ 3.14 / 55) (by norm_num : (2 : ℕ) ≠ 0)
  have h4 := pow_lt_pow_left₀ hθhi hθ0 (by norm_num : (4 : ℕ) ≠ 0)
  change _ ≤ 1 - Real.cos θ
  norm_num at h2 h4
  linarith only [hb2, h2, h4]

/-- The paired low-height estimate and the fourth-trace height floor cover the PF54 cone. -/
theorem pf54Cone_centre (q : XiZeroCopy) :
    Real.cos (Real.pi / (((54 : ℕ) : ℝ) + 1)) *
      ((q.1 : ℂ).im ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
        (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
  norm_num only [Nat.cast_ofNat] at ⊢
  have hcos := Real.cos_le_one (Real.pi / 55)
  have hL := one_sub_cos_pi_div_fiftyFive_ge
  have hu0 := sq_nonneg ((q.1 : ℂ).re - 1 / 2)
  by_cases hline : (q.1 : ℂ).re = 1 / 2
  · rw [hline, sub_self]
    nlinarith [sq_nonneg ((q.1 : ℂ).im)]
  · have hv := fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine q hline
    have hheight : 14 ≤ |(q.1 : ℂ).im| := by
      have ha := abs_nonneg ((q.1 : ℂ).im)
      rw [← sq_abs] at hv
      nlinarith only [ha, hv]
    have hU : ((q.1 : ℂ).re - 1 / 2) ^ 2 * (1 + Real.cos (Real.pi / 55)) ≤
        2 * ((q.1 : ℂ).re - 1 / 2) ^ 2 := by nlinarith only [hcos, hu0]
    have hcone (U V : ℝ) (hU' : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ U)
        (hV' : V ≤ (q.1 : ℂ).im ^ 2) (hpay : 2 * U ≤ V * (162 / 100000)) :
        Real.cos (Real.pi / 55) * ((q.1 : ℂ).im ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
          (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
      have hV := mul_le_mul hV' hL (by norm_num : (0 : ℝ) ≤ 162 / 100000)
        (by positivity : (0 : ℝ) ≤ (q.1 : ℂ).im ^ 2)
      nlinarith only [hU', hU, hV, hpay]
    by_cases h16 : |(q.1 : ℂ).im| ≤ 16
    · have hd := xiZeroCopy_depth_le_five_twelfths q hheight h16
      have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (5 / 12 : ℝ) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      exact hcone _ _ hu hv (by norm_num)
    · have hv16 : (256 : ℝ) ≤ (q.1 : ℂ).im ^ 2 := by
        rw [← sq_abs]
        nlinarith only [not_le.mp h16, abs_nonneg ((q.1 : ℂ).im)]
      by_cases h18 : |(q.1 : ℂ).im| ≤ 18
      · have hd := xiZeroCopy_depth_le_seven_sixteenths q hheight h18
        have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (7 / 16 : ℝ) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hd 2
        exact hcone _ _ hu hv16 (by norm_num)
      · have hv18 : (324 : ℝ) ≤ (q.1 : ℂ).im ^ 2 := by
          rw [← sq_abs]
          nlinarith only [not_le.mp h18, abs_nonneg ((q.1 : ℂ).im)]
        exact hcone _ _ (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hv18 (by norm_num)

/-- Every Toeplitz minor of the centre Taylor sequence of order at most 54 is nonnegative. -/
theorem xi_centre_pfSeq_fiftyFour : PFSeq 54 (evenTaylorRe (fun x => xi (1 / 2 + x))) :=
  xi_centre_pfSeq_of_cone (by norm_num) pf54Cone_centre

/-- The first 55 coefficients of the even reciprocal Xi series are nonnegative. -/
theorem evenRecipCoeff_XiC_nonneg_of_le_fiftyFour {m : ℕ} (hm : m ≤ 54) :
    0 ≤ evenRecipCoeff XiC m :=
  evenRecipCoeff_XiC_nonneg_of_pfSeq xi_centre_pfSeq_fiftyFour hm

#print axioms xiZeroCopy_depth_le_five_twelfths
#print axioms xiZeroCopy_depth_le_seven_sixteenths
#print axioms xi_centre_pfSeq_fiftyFour
#print axioms evenRecipCoeff_XiC_nonneg_of_le_fiftyFour

end

end GaloisForLFunctions.SquareRootThreshold
