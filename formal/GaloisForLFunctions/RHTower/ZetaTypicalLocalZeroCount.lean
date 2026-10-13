import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxScaledLength
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxPrimeCascade
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.XiLogDerivReLocality

/-!
# Local zero counts at the critical scale, at typical heights

*Log-derivative scale data* `ZetaLogDerivScaleData t R B` say that zeros right of `½ + R/2` keep
away from the height `t`, and that `|ζ'/ζ| ≤ B` on a box right of `½ + 3R/4` around `t`.

**Theorem** (`card_le_of_zetaLogDerivScaleData`).  Under these data, for `t ≥ 8` and
`0 < R ≤ 1/16`, every finite family of zero copies with ordinates within `R` of `t` has at most
`(13R/2)(B + log t + c + 1)` members, `c = 2 + 2π + log 2`.

*Proof.*  At `s = ½ + R + it` every line-conjugate pair of the partial fraction of `ξ'/ξ` has real
part `P(R, a, u) = (R − a)/((R − a)² + u²) + (R + a)/((R + a)² + u²)`, with `a = Re ρ − ½`,
`u = t − Im ρ` (`re_partialFraction_pair_eq`).  It is nonnegative for every zero: either
`|a| ≤ R/2`, or the zero keeps away, `|u| > |a|` (`xiLinePairRe_nonneg_of_sq_lt`).  A zero with
ordinate within `R` of `t` has `|a| ≤ R/2` and contributes `P ≥ 4/(13R)`
(`four_div_thirteen_le_xiLinePairRe`).
So `2 Re ξ'/ξ(s) ≥ (4/(13R)) · #F`, while
`Re ξ'/ξ(s) ≤ |ζ'/ζ(s)| + |1/s| + |1/(s−1)| + |Γ_ℝ'/Γ_ℝ(s)| ≤ B + ½ + log t + c`.

**Corollary** (`exists_volume_localZeroCount_gt_le`).  There is `C` such that for all large `T`
and every `0 < R ≤ 1/16` with `κ = R log T ≥ 9·10⁸`, the heights `t ∈ [T, 2T]` at which some
family of more than `10κ` zero copies has ordinates within `R` of `t` have measure at most
`C T e^{−√κ/4} + C T^{1/2}`, by the typical box bound
`exists_volume_not_zetaLogDerivScaleData_le_sqrt` at level `½ log T`.

**Smoothed density** (`two_mul_re_logDeriv_xi_eq_tsum_pair`,
`abs_re_logDeriv_xi_sub_half_log_le_of_zetaLogDerivScaleData`).  Twice `Re ξ'/ξ(½ + R + it)` is the
full pair sum, i.e. the Poisson-smoothed zero density at scale `R` around `t`. Under scale data it
equals `log(t/2π)` up to `2B + 3`, so at typical heights the smoothed density at the critical scale
is its Riemann–von Mangoldt value up to the relative error of the box bound.

With the prime-cascade scale-data theorem `exists_volume_not_zetaLogDerivScaleData_le_exp` the
rate improves to `C T (2e^{−κ/120000} + κ²e^{−κ/16} + e^{−κ/30}) + C T^{1/2}` for `κ ≥ κ₁`
(`exists_volume_localZeroCount_gt_le_exp`).

So clusters of zeros at the critical scale `κ/log T` larger than `10κ` occupy an exponentially
small proportion of heights, unconditionally.
-/

open Complex MeasureTheory Filter Set GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The real part of a line-conjugate pair at distance `R` right of the line. -/
def xiLinePairRe (R a u : ℝ) : ℝ :=
  (R - a) / ((R - a) ^ 2 + u ^ 2) + (R + a) / ((R + a) ^ 2 + u ^ 2)

/-- **One term of a near pair is at least `2/(13R)`.** -/
theorem two_div_thirteen_le_xiLinePairRe_half {R a u : ℝ} (hR : 0 < R) (ha : |a| ≤ R / 2)
    (hu : |u| ≤ R) : 2 / (13 * R) ≤ (R - a) / ((R - a) ^ 2 + u ^ 2) := by
  have ha' := abs_le.mp ha
  have hu2 : u ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have hpos : 0 < R - a := by linarith
  have hden : 0 < (R - a) ^ 2 + u ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hden]
  nlinarith [mul_nonneg hpos.le (show 0 ≤ 3 * R / 2 - (R - a) by linarith),
    mul_nonneg hR.le (show 0 ≤ R - a - R / 2 by linarith)]

/-- **A near pair contributes at least `4/(13R)`.** -/
theorem four_div_thirteen_le_xiLinePairRe {R a u : ℝ} (hR : 0 < R) (ha : |a| ≤ R / 2)
    (hu : |u| ≤ R) : 4 / (13 * R) ≤ xiLinePairRe R a u := by
  have h1 := two_div_thirteen_le_xiLinePairRe_half hR ha hu
  have h2 := two_div_thirteen_le_xiLinePairRe_half (a := -a) hR (by rwa [abs_neg]) hu
  rw [sub_neg_eq_add] at h2
  unfold xiLinePairRe
  have : 4 / (13 * R) = 2 / (13 * R) + 2 / (13 * R) := by ring
  linarith

/-- A pair with `|a| ≤ R/2` is nonnegative. -/
theorem xiLinePairRe_nonneg_of_near {R a u : ℝ} (hR : 0 < R) (ha : |a| ≤ R / 2) :
    0 ≤ xiLinePairRe R a u := by
  have ha' := abs_le.mp ha
  have h1 : 0 < R - a := by linarith
  have h2 : 0 < R + a := by linarith
  unfold xiLinePairRe
  positivity

/-- A pair whose ordinate distance exceeds its displacement is nonnegative. -/
theorem xiLinePairRe_nonneg_of_sq_lt {R a u : ℝ} (hR : 0 < R) (hsq : a ^ 2 < u ^ 2) :
    0 ≤ xiLinePairRe R a u := by
  have hd1 : 0 < (R - a) ^ 2 + u ^ 2 := by nlinarith [sq_nonneg (R - a)]
  have hd2 : 0 < (R + a) ^ 2 + u ^ 2 := by nlinarith [sq_nonneg (R + a)]
  unfold xiLinePairRe
  rw [div_add_div _ _ hd1.ne' hd2.ne']
  apply div_nonneg _ (by positivity)
  have hnum : (R - a) * ((R + a) ^ 2 + u ^ 2) + ((R - a) ^ 2 + u ^ 2) * (R + a) =
      2 * R * (R ^ 2 - a ^ 2 + u ^ 2) := by ring
  rw [hnum]
  have : 0 ≤ R ^ 2 - a ^ 2 + u ^ 2 := by nlinarith
  positivity

/-- Every zero copy is a zero of `ζ`. -/
theorem riemannZeta_xiZeroCopy_eq_zero (q : XiZeroCopy) : riemannZeta (q.1 : ℂ) = 0 := by
  have hxi := xi_xiZeroCopy_eq_zero q
  have hne1 : (q.1 : ℂ) ≠ 1 := by
    intro h1
    have := xiZeroCopy_re_lt_one q
    rw [h1, Complex.one_re] at this
    exact lt_irrefl 1 this
  exact (xi_eq_zero_iff (xiZeroCopy_re_pos q) hne1).mp hxi

/-- Under scale data, a zero copy far from the line in either direction is far from `t`. -/
theorem lt_abs_im_sub_of_zetaLogDerivScaleData {t R B : ℝ} (hR : 0 < R)
    (hdata : ZetaLogDerivScaleData t R B) (q : XiZeroCopy)
    (hq : R / 2 < |((q.1 : ℂ)).re - 1 / 2|) :
    |((q.1 : ℂ)).re - 1 / 2| + 12 * R < |((q.1 : ℂ)).im - t| := by
  rcases lt_abs.mp hq with h | h
  · have := hdata.zeroFree _ (riemannZeta_xiZeroCopy_eq_zero q) (by linarith)
    rwa [abs_of_pos (by linarith : (0 : ℝ) < ((q.1 : ℂ)).re - 1 / 2)]
  · -- reflect `ρ ↦ 1 − conj ρ`, which keeps the ordinate
    set q' := xiZeroCopyLineConjEquiv q with hq'
    have hρ' := xiZero_lineConj_eq q
    have hre : ((q'.1 : ℂ)).re = 1 - ((q.1 : ℂ)).re := by
      rw [hq', hρ']; simp
    have him : ((q'.1 : ℂ)).im = ((q.1 : ℂ)).im := by
      rw [hq', hρ']; simp
    have := hdata.zeroFree _ (riemannZeta_xiZeroCopy_eq_zero q') (by rw [hre]; linarith)
    rw [hre, him] at this
    rw [abs_of_neg (by linarith : ((q.1 : ℂ)).re - 1 / 2 < 0)]
    linarith

/-- **The real part of a line-conjugate pair of the partial fraction.** -/
theorem re_partialFraction_pair_eq (s : ℂ) (q : XiZeroCopy) :
    ((((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹) +
      ((((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹ +
        (s - ((xiZeroCopyLineConjEquiv q).1 : ℂ))⁻¹)).re =
      xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have hρ' := xiZero_lineConj_eq q
  have hcenter : (((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2) =
      -((starRingEnd ℂ) ((q.1 : ℂ) - 1 / 2)) := by
    rw [hρ', map_sub, hhalf]; ring
  have hconst : ((((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹).re =
      -((((q.1 : ℂ)) - 1 / 2)⁻¹).re := by
    rw [hcenter, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
  simp only [Complex.add_re]
  rw [hconst, hρ', re_inv_sub_lineConj_eq s (q.1 : ℂ), re_inv_sub_eq s (q.1 : ℂ)]
  unfold xiLinePairRe
  linarith

/-- The partial-fraction term of a zero copy at `s`. -/
def pfTerm (s : ℂ) (q : XiZeroCopy) : ℂ := ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹

/-- **A finite sub-sum of nonnegative pairs is at most twice `Re ξ'/ξ`.** -/
theorem sum_pair_le_two_mul_re_logDeriv_xi {s : ℂ} (hxi : xi s ≠ 0)
    (hpair : ∀ q : XiZeroCopy,
      0 ≤ xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im))
    (F : Finset XiZeroCopy) :
    ∑ q ∈ F, xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im) ≤
      2 * (logDeriv xi s).re := by
  have hsum : Summable (pfTerm s) := summable_partialFractionTerm hxi
  have hpf : logDeriv xi s = ∑' q, pfTerm s q := logDeriv_xi_eq_partialFraction hxi
  have hsumJ : Summable (fun q => pfTerm s (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpairs : Summable (fun q => pfTerm s q + pfTerm s (xiZeroCopyLineConjEquiv q)) :=
    hsum.add hsumJ
  have heq : ∀ q, (pfTerm s q + pfTerm s (xiZeroCopyLineConjEquiv q)).re =
      xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im) :=
    fun q => re_partialFraction_pair_eq s q
  have hpairsRe : Summable (fun q : XiZeroCopy =>
      xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im)) :=
    (Complex.reCLM.summable hpairs).congr heq
  have htsum : (∑' q : XiZeroCopy, xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2)
      (s.im - ((q.1 : ℂ)).im)) = 2 * (logDeriv xi s).re := by
    rw [← tsum_congr heq, ← Complex.re_tsum hpairs, hsum.tsum_add hsumJ,
      xiZeroCopyLineConjEquiv.tsum_eq (pfTerm s), Complex.add_re, hpf]
    ring
  rw [← htsum]
  exact hpairsRe.sum_le_tsum F (fun q _ => hpair q)

/-- **The upper bound of `Re ξ'/ξ` at `½ + R + it` from `|ζ'/ζ| ≤ B`.** -/
theorem re_logDeriv_xi_le_of_norm_logDeriv_zeta_le {t R B : ℝ} (ht : 8 ≤ t) (hR : 0 < R)
    (hR1 : R ≤ 1 / 16) (hζ : riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0)
    (hB : ‖logDeriv riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ B) :
    (logDeriv xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)).re ≤
      B + Real.log t + digammaVerticalLogConstant + 1 := by
  set s : ℂ := ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = 1 / 2 + R := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim, Complex.one_im] at this; linarith
  have hdec := logDeriv_zeta_eq_logDeriv_xi (by rw [hsre]; linarith) hs1 hζ
  have hinv : ‖s⁻¹‖ ≤ 1 / 4 := norm_inv_le_quarter hsim (by linarith)
  have hinv1 : ‖(s - 1)⁻¹‖ ≤ 1 / 4 :=
    norm_inv_le_quarter (s := s - 1) (t := t) (by simp [hsim]) (by linarith)
  have hΓ : ‖logDeriv Gammaℝ s‖ ≤ Real.log t + digammaVerticalLogConstant :=
    norm_logDeriv_Gammaℝ_le (σ := 1 / 2 + R) (t := t) (by linarith) (by linarith) (by linarith)
  have hxiEq : logDeriv xi s = logDeriv riemannZeta s + s⁻¹ + (s - 1)⁻¹ + logDeriv Gammaℝ s := by
    rw [hdec]; ring
  rw [hxiEq]
  simp only [Complex.add_re]
  have h1 := Complex.re_le_norm (logDeriv riemannZeta s)
  have h2 := Complex.re_le_norm s⁻¹
  have h3 := Complex.re_le_norm (s - 1)⁻¹
  have h4 := Complex.re_le_norm (logDeriv Gammaℝ s)
  linarith

/-- **Local zero count from log-derivative scale data.** -/
theorem card_le_of_zetaLogDerivScaleData {t R B : ℝ} (ht : 8 ≤ t) (hR : 0 < R) (hR1 : R ≤ 1 / 16)
    (hdata : ZetaLogDerivScaleData t R B) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ R) :
    (F.card : ℝ) ≤ 13 * R / 2 * (B + Real.log t + digammaVerticalLogConstant + 1) := by
  set s : ℂ := ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = 1 / 2 + R := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim, Complex.one_im] at this; linarith
  have hζ : riemannZeta s ≠ 0 := by
    intro h0
    have := hdata.zeroFree s h0 (by rw [hsre]; linarith)
    rw [hsim, sub_self, abs_zero, hsre] at this
    linarith
  have hxi : xi s ≠ 0 := fun h => hζ ((xi_eq_zero_iff (by rw [hsre]; linarith) hs1).mp h)
  have hζB : ‖logDeriv riemannZeta s‖ ≤ B :=
    hdata.logDeriv s (by rw [hsre]; linarith) (by rw [hsre]; linarith)
      (by rw [hsim, sub_self, abs_zero]; positivity)
  have hupper := re_logDeriv_xi_le_of_norm_logDeriv_zeta_le ht hR hR1 hζ hζB
  rw [← hs] at hupper
  -- every pair is nonnegative
  have hpair : ∀ q : XiZeroCopy,
      0 ≤ xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im) := by
    intro q
    rw [hsre, hsim, show 1 / 2 + R - 1 / 2 = R by ring]
    by_cases hnear : |((q.1 : ℂ)).re - 1 / 2| ≤ R / 2
    · exact xiLinePairRe_nonneg_of_near hR hnear
    · push Not at hnear
      have hfar := lt_abs_im_sub_of_zetaLogDerivScaleData hR hdata q hnear
      rw [abs_sub_comm ((q.1 : ℂ)).im t] at hfar
      refine xiLinePairRe_nonneg_of_sq_lt hR ?_
      have h1 : |((q.1 : ℂ)).re - 1 / 2| < |t - ((q.1 : ℂ)).im| := by linarith
      exact sq_lt_sq.mpr h1
  -- the pairs in `F` contribute at least `4/(13R)` each
  have hFlow : (F.card : ℝ) * (4 / (13 * R)) ≤
      ∑ q ∈ F, xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun q hq => ?_
    rw [hsre, hsim, show 1 / 2 + R - 1 / 2 = R by ring]
    have hu : |t - ((q.1 : ℂ)).im| ≤ R := by rw [abs_sub_comm]; exact hF q hq
    have ha : |((q.1 : ℂ)).re - 1 / 2| ≤ R / 2 := by
      by_contra hfar
      push Not at hfar
      have := lt_abs_im_sub_of_zetaLogDerivScaleData hR hdata q hfar
      linarith [abs_nonneg (((q.1 : ℂ)).re - 1 / 2), hF q hq]
    exact four_div_thirteen_le_xiLinePairRe hR ha hu
  have hkey := hFlow.trans (sum_pair_le_two_mul_re_logDeriv_xi hxi hpair F)
  have hcard : (F.card : ℝ) ≤ 13 * R / 2 * (logDeriv xi s).re := by
    have h := mul_le_mul_of_nonneg_right hkey (show 0 ≤ 13 * R / 4 by positivity)
    have hl : (F.card : ℝ) * (4 / (13 * R)) * (13 * R / 4) = F.card := by field_simp
    rw [hl] at h
    linarith
  exact hcard.trans (mul_le_mul_of_nonneg_left hupper (by positivity))

/-- **Critical-scale clusters are rare.**  There is `C` such that for all large `T` and every
`0 < R ≤ 1/16` with `κ = R log T ≥ 9·10⁸`, the heights `t ∈ [T, 2T]` at which some family of more
than `10κ` zero copies has ordinates within `R` of `t` have measure at most
`C T e^{−√κ/4} + C T^{1/2}`. -/
theorem exists_volume_localZeroCount_gt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 / 16 →
      9 * 10 ^ 8 ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ F : Finset XiZeroCopy,
          (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ R) ∧ 10 * (R * Real.log T) < F.card} ≤
        ENNReal.ofReal (C * T * Real.exp (-(Real.sqrt (R * Real.log T) / 4)) +
          C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, hC, hev⟩ := exists_volume_not_zetaLogDerivScaleData_le_sqrt (ε := 1 / 2)
    (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop
    (4 * (13 / 2 * (Real.log 2 + digammaVerticalLogConstant + 1)))
  filter_upwards [hev, hlog, eventually_ge_atTop (8 : ℝ)] with T hT hTlog hT8 R hR hR1 hκ
  have hmax : max (9 * 10 ^ 8) (1000 / (1 / 2 : ℝ) ^ 2) ≤ R * Real.log T := by
    rw [max_le_iff]; constructor
    · exact hκ
    · norm_num; linarith
  refine le_trans (measure_mono ?_) (hT R hR hR1 hmax)
  intro t ht
  refine ⟨ht.1, fun hdata => ?_⟩
  obtain ⟨F, hF, hcard⟩ := ht.2
  have ht8 : 8 ≤ t := le_trans hT8 ht.1.1
  have hbound := card_le_of_zetaLogDerivScaleData ht8 hR hR1 hdata F hF
  have hT0 : 0 < T := by linarith
  have hlogt : Real.log t ≤ Real.log 2 + Real.log T := by
    rw [← Real.log_mul (by norm_num) hT0.ne']
    exact Real.log_le_log (by linarith) ht.1.2
  have hc : 0 ≤ digammaVerticalLogConstant := by
    unfold digammaVerticalLogConstant
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  have hfinal : 13 * R / 2 * (1 / 2 * Real.log T + Real.log t + digammaVerticalLogConstant + 1) ≤
      10 * (R * Real.log T) := by
    have h1 : 1 / 2 * Real.log T + Real.log t + digammaVerticalLogConstant + 1 ≤
        3 / 2 * Real.log T + (Real.log 2 + digammaVerticalLogConstant + 1) := by linarith
    have h2 : 13 / 2 * (Real.log 2 + digammaVerticalLogConstant + 1) ≤ Real.log T / 4 := by
      linarith
    calc 13 * R / 2 * (1 / 2 * Real.log T + Real.log t + digammaVerticalLogConstant + 1)
        ≤ 13 * R / 2 * (3 / 2 * Real.log T + (Real.log 2 + digammaVerticalLogConstant + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = R * (39 / 4 * Real.log T + 13 / 2 * (Real.log 2 + digammaVerticalLogConstant + 1)) := by
          ring
      _ ≤ R * (39 / 4 * Real.log T + Real.log T / 4) :=
          mul_le_mul_of_nonneg_left (by linarith) hR.le
      _ = 10 * (R * Real.log T) := by ring
  linarith

/-- Under scale data at level `½ log T`, a cluster within `R` of `t ∈ [T, 2T]` has at most
`10 R log T` members once `log T` is large. -/
theorem card_le_ten_mul_of_zetaLogDerivScaleData_half {T t R : ℝ} (hT8 : 8 ≤ T)
    (hTlog : 4 * (13 / 2 * (Real.log 2 + digammaVerticalLogConstant + 1)) ≤ Real.log T)
    (ht : t ∈ Icc T (2 * T)) (hR : 0 < R) (hR1 : R ≤ 1 / 16)
    (hdata : ZetaLogDerivScaleData t R (1 / 2 * Real.log T)) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ R) : (F.card : ℝ) ≤ 10 * (R * Real.log T) := by
  have ht8 : 8 ≤ t := le_trans hT8 ht.1
  have hbound := card_le_of_zetaLogDerivScaleData ht8 hR hR1 hdata F hF
  have hT0 : 0 < T := by linarith
  have hlogt : Real.log t ≤ Real.log 2 + Real.log T := by
    rw [← Real.log_mul (by norm_num) hT0.ne']
    exact Real.log_le_log (by linarith) ht.2
  have h1 : 1 / 2 * Real.log T + Real.log t + digammaVerticalLogConstant + 1 ≤
      3 / 2 * Real.log T + (Real.log 2 + digammaVerticalLogConstant + 1) := by linarith
  calc (F.card : ℝ)
      ≤ 13 * R / 2 * (1 / 2 * Real.log T + Real.log t + digammaVerticalLogConstant + 1) := hbound
    _ ≤ 13 * R / 2 * (3 / 2 * Real.log T + (Real.log 2 + digammaVerticalLogConstant + 1)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = R * (39 / 4 * Real.log T + 13 / 2 * (Real.log 2 + digammaVerticalLogConstant + 1)) := by
        ring
    _ ≤ R * (39 / 4 * Real.log T + Real.log T / 4) :=
        mul_le_mul_of_nonneg_left (by linarith) hR.le
    _ = 10 * (R * Real.log T) := by ring

/-- **Critical-scale clusters are exponentially rare.**  There are `C` and `κ₁` such that for all
large `T` and every `0 < R ≤ 1/16` with `κ = R log T ≥ κ₁`, the heights `t ∈ [T, 2T]` at which
some family of more than `10κ` zero copies has ordinates within `R` of `t` have measure at most
`C T (2 e^{−κ/120000} + κ² e^{−κ/16} + e^{−κ/30}) + C T^{1/2}`. -/
theorem exists_volume_localZeroCount_gt_le_exp :
    ∃ C κ₁ : ℝ, 0 < C ∧ 1 ≤ κ₁ ∧ ∀ᶠ T in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 / 16 →
      κ₁ ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ F : Finset XiZeroCopy,
          (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ R) ∧ 10 * (R * Real.log T) < F.card} ≤
        ENNReal.ofReal (C * T * (Real.exp (-(R * Real.log T / 120000)) / (1 / 2) +
          ((R * Real.log T) ^ 2 * Real.exp (-(R * Real.log T / 16)) +
            Real.exp (-(R * Real.log T * (1 / 2) / 15)))) + C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, κ₁, hC, hκ₁, hev⟩ := exists_volume_not_zetaLogDerivScaleData_le_exp (ε := 1 / 2)
    (by norm_num) (by norm_num)
  refine ⟨C, κ₁, hC, hκ₁, ?_⟩
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop
    (4 * (13 / 2 * (Real.log 2 + digammaVerticalLogConstant + 1)))
  filter_upwards [hev, hlog, eventually_ge_atTop (8 : ℝ)] with T hT hTlog hT8 R hR hR1 hκ
  refine le_trans (measure_mono ?_) (hT R hR hR1 hκ)
  intro t ht
  refine ⟨ht.1, fun hdata => ?_⟩
  obtain ⟨F, hF, hcard⟩ := ht.2
  have := card_le_ten_mul_of_zetaLogDerivScaleData_half hT8 hTlog ht.1 hR hR1 hdata F hF
  linarith

/-- **`Re ξ'/ξ` is half the full pair sum.**  Off the zeros, twice the real part of `ξ'/ξ` at `s`
is the sum over all zero copies of the line-conjugate pair real parts. -/
theorem two_mul_re_logDeriv_xi_eq_tsum_pair {s : ℂ} (hxi : xi s ≠ 0) :
    2 * (logDeriv xi s).re = ∑' q : XiZeroCopy,
      xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im) := by
  have hsum : Summable (pfTerm s) := summable_partialFractionTerm hxi
  have hpf : logDeriv xi s = ∑' q, pfTerm s q := logDeriv_xi_eq_partialFraction hxi
  have hsumJ : Summable (fun q => pfTerm s (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpairs : Summable (fun q => pfTerm s q + pfTerm s (xiZeroCopyLineConjEquiv q)) :=
    hsum.add hsumJ
  have heq : ∀ q, (pfTerm s q + pfTerm s (xiZeroCopyLineConjEquiv q)).re =
      xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im) :=
    fun q => re_partialFraction_pair_eq s q
  rw [← tsum_congr heq, ← Complex.re_tsum hpairs, hsum.tsum_add hsumJ,
    xiZeroCopyLineConjEquiv.tsum_eq (pfTerm s), Complex.add_re, hpf]
  ring

/-- The archimedean part on the strip is `½ log(t/2π)` up to `½`. -/
theorem abs_re_logDeriv_Gammaℝ_sub_half_log_le {σ t : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 8 ≤ t) :
    |(logDeriv Gammaℝ ((σ : ℂ) + t * I)).re - Real.log (t / (2 * Real.pi)) / 2| ≤ 1 / 2 := by
  have hre : 0 < ((σ : ℂ) + t * I).re := by simp; linarith
  rw [logDeriv_Gammaℝ_digamma hre]
  set z : ℂ := ((σ : ℂ) + t * I) / 2 with hz
  have hzre : z.re = σ / 2 := by simp [hz]
  have hzim : z.im = t / 2 := by simp [hz]
  have hnorm_ge : t / 2 ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rw [hzim, abs_of_pos (by linarith)] at this
    exact this
  have hnorm_le : ‖z‖ ≤ t / 2 + σ / 2 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [hzre, hzim, abs_of_pos (by linarith), abs_of_pos (by linarith)] at this
    linarith
  have hψ := HTGeometry.norm_digamma_sub_log_le_of_re_pos (z := z) (by rw [hzre]; linarith)
    (by linarith)
  have hψre : |(Complex.digamma z).re - Real.log ‖z‖| ≤ 3 / ‖z‖ := by
    have h := (Complex.abs_re_le_norm _).trans hψ
    rwa [Complex.sub_re, Complex.log_re] at h
  have hz0 : 0 < ‖z‖ := by linarith
  have h3 : 3 / ‖z‖ ≤ 3 / 4 := by
    rw [div_le_div_iff₀ hz0 (by norm_num)]; linarith
  have hlog1 : Real.log (t / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by linarith) hnorm_ge
  have hlog2 : Real.log ‖z‖ ≤ Real.log (t / 2) + 1 / 8 := by
    have h1 : Real.log ‖z‖ ≤ Real.log (t / 2 + σ / 2) := Real.log_le_log hz0 hnorm_le
    have h2 : Real.log (t / 2 + σ / 2) - Real.log (t / 2) ≤ (σ / 2) / (t / 2) := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have := Real.log_le_sub_one_of_pos (show 0 < (t / 2 + σ / 2) / (t / 2) by positivity)
      have e : (t / 2 + σ / 2) / (t / 2) - 1 = (σ / 2) / (t / 2) := by field_simp; ring
      linarith
    have h3' : (σ / 2) / (t / 2) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hsplit : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by linarith) Real.pi_pos.ne']
  have hre_eq : (Complex.digamma z / 2 - (Real.log Real.pi : ℂ) / 2).re =
      (Complex.digamma z).re / 2 - Real.log Real.pi / 2 := by
    simp [Complex.sub_re]
  rw [hre_eq, hsplit]
  rw [abs_le] at hψre ⊢
  constructor <;> linarith [hψre.1, hψre.2]

/-- **Two-sided smoothed local density at typical heights.**  Under scale data at `(t, R, B)`,
`t ≥ 8`, `0 < R ≤ 1/16`, the real part of `ξ'/ξ` at `½ + R + it`, which is half the
Poisson-smoothed zero density at scale `R` around `t`, equals `½ log(t/2π)` up to `B + 3/2`. -/
theorem abs_re_logDeriv_xi_sub_half_log_le_of_zetaLogDerivScaleData {t R B : ℝ} (ht : 8 ≤ t)
    (hR : 0 < R) (hR1 : R ≤ 1 / 16) (hdata : ZetaLogDerivScaleData t R B) :
    |(logDeriv xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)).re - Real.log (t / (2 * Real.pi)) / 2| ≤
      B + 3 / 2 := by
  set s : ℂ := ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = 1 / 2 + R := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim, Complex.one_im] at this; linarith
  have hζ : riemannZeta s ≠ 0 := by
    intro h0
    have := hdata.zeroFree s h0 (by rw [hsre]; linarith)
    rw [hsim, sub_self, abs_zero, hsre] at this
    linarith
  have hdec := logDeriv_zeta_eq_logDeriv_xi (by rw [hsre]; linarith) hs1 hζ
  have hζB : ‖logDeriv riemannZeta s‖ ≤ B :=
    hdata.logDeriv s (by rw [hsre]; linarith) (by rw [hsre]; linarith)
      (by rw [hsim, sub_self, abs_zero]; positivity)
  have hinv : ‖s⁻¹‖ ≤ 1 / 4 := norm_inv_le_quarter hsim (by linarith)
  have hinv1 : ‖(s - 1)⁻¹‖ ≤ 1 / 4 :=
    norm_inv_le_quarter (s := s - 1) (t := t) (by simp [hsim]) (by linarith)
  have hΓ := abs_re_logDeriv_Gammaℝ_sub_half_log_le (σ := 1 / 2 + R) (t := t) (by linarith)
    (by linarith) ht
  rw [← hs] at hΓ
  have hxiEq : logDeriv xi s = logDeriv riemannZeta s + s⁻¹ + (s - 1)⁻¹ + logDeriv Gammaℝ s := by
    rw [hdec]; ring
  rw [hxiEq]
  simp only [Complex.add_re]
  have h1 := Complex.abs_re_le_norm (logDeriv riemannZeta s)
  have h2 := Complex.abs_re_le_norm s⁻¹
  have h3 := Complex.abs_re_le_norm (s - 1)⁻¹
  rw [abs_le] at hΓ h1 h2 h3 ⊢
  constructor <;> linarith [hΓ.1, hΓ.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end

end RHTower
