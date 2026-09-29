import GaloisForLFunctions.RHTower.PrimeDeletionLogDerivativeCeiling
import GaloisForLFunctions.RHTower.LandauSummabilityTransfer
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted

/-!
# Added integer generators cost the full dimension

Let an integer-supported Beurling system have integer masses `a` and generator von Mangoldt
function `Λ - e`, and suppose it only adds generators: `e ≤ 0`.  Then the logarithmic coefficients
`c(n) = -e(n)/log n ≥ 0` satisfy `L(a)/ζ = K exp L(c)` on `Re s > 1`.  If the integer count is
`A x + O(x^θ)`, the quotient continues analytically across the real segment `(θ, 1]`, where `ζ` has
no zeros, and there it equals `K exp L(c)` with `K exp L(c)(σ) ≥ K` on real `σ`.  Landau's theorem
for the nonnegative series `L(c)` then puts its abscissa at or below `θ`
(`abscissaOfAbsConv_logCoeff_le`): the added mass satisfies `Σ_n |e(n)| n^{-σ} < ∞` for every
`σ > θ` (`summable_pertSeq_of_nonpos`).

So adding generators costs the full dimension of the added set: integer regularity `O(x^θ)`
forces the added generators to have convergence exponent at most `θ`.  Deletions cost only half
(`not_isBigO_count_of_leading_chebyshev`), because `exp(-P)` may vanish analytically at the
abscissa while `exp(P)` cannot.
-/

open Filter Topology Complex Asymptotics Set Metric ArithmeticFunction

noncomputable section

namespace RHTower

namespace IntegerBeurling

variable {a e : ℕ → ℝ}

/-- `(s-1)ζ(s)` has no zeros in the strip `0 < Re s`, `|Im s| < 4`. -/
theorem zetaResidueFactor_ne_zero_of_strip {z : ℂ} (h0 : 0 < z.re) (him : |z.im| < 4) :
    zetaResidueFactor z ≠ 0 := by
  rcases eq_or_ne z 1 with rfl | hz1
  · rw [zetaResidueFactor_one]; exact one_ne_zero
  rw [zetaResidueFactor_of_ne hz1]
  refine mul_ne_zero (sub_ne_zero.mpr hz1) ?_
  rcases le_or_gt 1 z.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · exact riemannZeta_ne_zero_of_abs_im_lt_four h0 h1 him

variable (e) in
/-- The logarithmic coefficients `c(n) = -e(n)/log n`. -/
def logCoeff (n : ℕ) : ℝ := -e n / Real.log n

theorem logCoeff_nonneg (hadd : ∀ n, e n ≤ 0) (n : ℕ) : 0 ≤ logCoeff e n :=
  div_nonneg (neg_nonneg.mpr (hadd n)) (Real.log_natCast_nonneg n)

theorem abs_logCoeff_le (he : ∀ n, |e n| ≤ Real.log n) (n : ℕ) : |logCoeff e n| ≤ 1 := by
  unfold logCoeff
  rw [abs_div, abs_neg, abs_of_nonneg (Real.log_natCast_nonneg n)]
  exact div_le_one_of_le₀ (he n) (Real.log_natCast_nonneg n)

theorem logMul_logCoeff (he : ∀ n, |e n| ≤ Real.log n) :
    LSeries.logMul (fun n => ((logCoeff e n : ℝ) : ℂ)) = -pertSeq e := by
  funext n
  simp only [LSeries.logMul, Pi.neg_apply, pertSeq, logCoeff]
  rcases eq_or_ne (Real.log n) 0 with h0 | h0
  · have : e n = 0 := by
      have := he n; rw [h0] at this; exact abs_nonpos_iff.mp this
    rw [this]; simp
  · rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n), ← Complex.ofReal_mul,
      ← Complex.ofReal_neg]
    congr 1
    field_simp

theorem abscissa_logCoeff_le_one (he : ∀ n, |e n| ≤ Real.log n) :
    LSeries.abscissaOfAbsConv (fun n => ((logCoeff e n : ℝ) : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_logCoeff_le he n⟩

theorem hasDerivAt_LSeries_logCoeff (he : ∀ n, |e n| ≤ Real.log n) {s : ℂ}
    (hs : LSeries.abscissaOfAbsConv (fun n => ((logCoeff e n : ℝ) : ℂ)) < s.re) :
    HasDerivAt (LSeries fun n => ((logCoeff e n : ℝ) : ℂ)) (LSeries (pertSeq e) s) s := by
  have h := LSeries_hasDerivAt hs
  rw [logMul_logCoeff he, LSeries_neg, neg_neg] at h
  exact h

/-- A Dirichlet series with real nonnegative coefficients is real and nonnegative at real points
of convergence. -/
theorem LSeries_ofReal_eq {c : ℕ → ℝ} (σ : ℝ) :
    LSeries (fun n => (c n : ℂ)) (σ : ℂ) =
      ((∑' n : ℕ, if n = 0 then 0 else c n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  rw [LSeries.term_of_ne_zero hn, if_neg hn, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_div]

/-- **Up to a constant, `L(a)/ζ` is `exp L(c)` on `Re s > 1`.** -/
theorem exists_ratio_eq_mul_exp (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1)
    (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : LSeries.convolution (fun n => ((Λ n - e n : ℝ) : ℂ)) (countSeq a) =
      LSeries.logMul (countSeq a)) :
    ∃ K : ℂ, K ≠ 0 ∧ ∀ z : ℂ, 1 < z.re →
      ratio a z = K * Complex.exp (LSeries (fun n => ((logCoeff e n : ℝ) : ℂ)) z) := by
  set L : ℂ → ℂ := LSeries fun n => ((logCoeff e n : ℝ) : ℂ) with hL
  set H : ℂ → ℂ := fun z => ratio a z * Complex.exp (-L z) with hH
  set S : Set ℂ := {z | 1 < z.re} with hS
  have hSo : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hSc : Convex ℝ S := convex_halfSpace_re_gt 1
  have hLd : ∀ z ∈ S, HasDerivAt L (LSeries (pertSeq e) z) z := fun z hz =>
    hasDerivAt_LSeries_logCoeff he ((abscissa_logCoeff_le_one he).trans_lt
      (by exact_mod_cast hz))
  have hRd : ∀ z ∈ S, HasDerivAt (ratio a) (ratio a z * LSeries (pertSeq e) z) z := by
    intro z hz
    have hz1 : 1 < z.re := hz
    have hz1' : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz1; exact lt_irrefl _ hz1
    have habs : LSeries.abscissaOfAbsConv (countSeq a) < z.re :=
      (abscissa_countSeq_le ha).trans_lt (by exact_mod_cast hz1)
    have hdiff : DifferentiableAt ℂ (ratio a) z :=
      (LSeries_hasDerivAt habs).differentiableAt.div (differentiableAt_riemannZeta hz1')
        (riemannZeta_ne_zero_of_one_le_re hz1.le)
    have h := deriv_LSeries_div_riemannZeta ha he hconv hz1
    have h' : deriv (ratio a) z = ratio a z * LSeries (pertSeq e) z := h
    rw [← h']
    exact hdiff.hasDerivAt
  have hHd : ∀ z ∈ S, HasDerivAt H 0 z := by
    intro z hz
    have h3 := (hRd z hz).mul ((hLd z hz).neg.cexp)
    refine h3.congr_deriv ?_
    ring
  have hconst : ∀ z ∈ S, H z = H 3 := fun z hz =>
    hSo.is_const_of_deriv_eq_zero hSc.isPreconnected
      (fun y hy => (hHd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hHd y hy).deriv) hz (by simp [hS])
  refine ⟨H 3, ?_, fun z hz => ?_⟩
  · exact mul_ne_zero (ratio_ne_zero ha ha1 (by simp)) (Complex.exp_ne_zero _)
  · have := hconst z hz
    rw [← this, hH]
    simp only
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- **Landau for added generators.**  If only generators are added (`e ≤ 0`) and the integer count
is `A x + O(x^θ)`, the logarithmic coefficients `-e(n)/log n` have abscissa at most `θ`. -/
theorem abscissaOfAbsConv_logCoeff_le (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1)
    (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : LSeries.convolution (fun n => ((Λ n - e n : ℝ) : ℂ)) (countSeq a) =
      LSeries.logMul (countSeq a))
    (hadd : ∀ n, e n ≤ 0) {A θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ) :
    LSeries.abscissaOfAbsConv (fun n => ((logCoeff e n : ℝ) : ℂ)) ≤ θ := by
  set c : ℕ → ℂ := fun n => ((logCoeff e n : ℝ) : ℂ) with hc
  set L : ℂ → ℂ := LSeries c with hL
  classical
  by_contra hcon
  push Not at hcon
  have hle1 := abscissa_logCoeff_le_one he
  -- the abscissa is a real number `k ∈ (θ, 1]`
  obtain ⟨k, hk⟩ : ∃ k : ℝ, LSeries.abscissaOfAbsConv c = k := by
    induction h : LSeries.abscissaOfAbsConv c using EReal.rec with
    | bot => rw [h] at hcon; exact absurd hcon (not_lt.mpr bot_le)
    | top =>
      rw [h, ← EReal.coe_one] at hle1
      exact absurd hle1 (not_le.mpr (EReal.coe_lt_top 1))
    | coe x => exact ⟨x, rfl⟩
  rw [hk] at hcon hle1
  have hθk : θ < k := by exact_mod_cast hcon
  have hk1 : k ≤ 1 := by exact_mod_cast hle1
  have hk0 : 0 < k := lt_of_le_of_lt hθ hθk
  obtain ⟨K, hK0, hK⟩ := exists_ratio_eq_mul_exp ha ha1 he hconv
  -- the continued quotient
  set F : ℂ → ℂ := fun z => numerator a A z / zetaResidueFactor z / K with hF
  have hFana : ∀ z : ℂ, θ < z.re → |z.im| < 4 → AnalyticAt ℂ F z := by
    intro z hz him
    have hz0 : 0 < z.re := lt_of_le_of_lt hθ hz
    have hnum := differentiableAt_numerator hθ hN hz
    have hU : IsOpen {w : ℂ | θ < w.re ∧ |w.im| < 4} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
    have hdiff : DifferentiableOn ℂ F {w : ℂ | θ < w.re ∧ |w.im| < 4} := fun w hw =>
      (((differentiableAt_numerator hθ hN hw.1).div (differentiable_zetaResidueFactor w)
        (zetaResidueFactor_ne_zero_of_strip (lt_of_le_of_lt hθ hw.1) hw.2)).div_const
          K).differentiableWithinAt
    exact (hdiff.analyticOnNhd hU) z ⟨hz, him⟩
  have hFexp : ∀ z : ℂ, 1 < z.re → F z = Complex.exp (L z) := by
    intro z hz
    have hz1' : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz; exact lt_irrefl _ hz
    have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1'
    have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hz.le
    have hr := hK z hz
    rw [ratio] at hr
    rw [hF]
    simp only
    rw [numerator_eq ha hθ hN hz (by linarith), zetaResidueFactor_of_ne hz1',
      show (z - 1) * LSeries (countSeq a) z / ((z - 1) * riemannZeta z) =
        LSeries (countSeq a) z / riemannZeta z by field_simp, hr, mul_div_cancel_left₀ _ hK0]
  -- `F = exp L` on the strip right of the abscissa
  set D : Set ℂ := {z | k < z.re ∧ |z.im| < 4} with hD
  have hDo : IsOpen D :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hDc : Convex ℝ D := by
    have : D = {z : ℂ | k < z.re} ∩ ({z : ℂ | -4 < z.im} ∩ {z : ℂ | z.im < 4}) := by
      ext z; simp [hD, abs_lt]
    rw [this]
    exact (convex_halfSpace_re_gt k).inter
      ((convex_halfSpace_im_gt (-4)).inter (convex_halfSpace_im_lt 4))
  have hLana : AnalyticOnNhd ℂ (fun z => Complex.exp (L z)) D := by
    have hdiff : DifferentiableOn ℂ (fun z => Complex.exp (L z)) D := fun z hz =>
      ((LSeries_hasDerivAt (hk.trans_lt (by exact_mod_cast hz.1))).differentiableAt.cexp
        ).differentiableWithinAt
    exact hdiff.analyticOnNhd hDo
  have hFD : AnalyticOnNhd ℂ F D := fun z hz => hFana z (lt_trans hθk hz.1) hz.2
  have h2D : (2 : ℂ) ∈ D := ⟨by norm_num; linarith, by norm_num⟩
  have hEq : EqOn F (fun z => Complex.exp (L z)) D := by
    refine hFD.eqOn_of_preconnected_of_eventuallyEq hLana hDc.isPreconnected h2D ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact hFexp z hz
  -- real values right of the abscissa
  have hLreal : ∀ σ : ℝ, k < σ → (L σ).im = 0 ∧ 0 ≤ (L σ).re := by
    intro σ _
    rw [hL, hc, LSeries_ofReal_eq σ, Complex.ofReal_im, Complex.ofReal_re]
    refine ⟨rfl, tsum_nonneg fun n => ?_⟩
    split_ifs
    · exact le_rfl
    · exact div_nonneg (logCoeff_nonneg hadd n) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  have hFreal : ∀ σ : ℝ, k < σ → σ < k + 1 → 1 ≤ (F σ).re := by
    intro σ hσ _
    have hσD : (σ : ℂ) ∈ D := ⟨by simpa using hσ, by simp⟩
    rw [show F σ = Complex.exp (L σ) from hEq hσD]
    obtain ⟨him, hre⟩ := hLreal σ hσ
    have : L σ = ((L σ).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [this, ← Complex.ofReal_exp, Complex.ofReal_re]
    exact Real.one_le_exp hre
  -- `Re F ≥ 1` at the abscissa, hence near it
  have hFk : 1 ≤ (F k).re := by
    have hcont : ContinuousAt (fun σ : ℝ => (F σ).re) k :=
      Complex.continuous_re.continuousAt.comp ((hFana k (by simpa using hθk)
        (by simp)).continuousAt.comp Complex.continuous_ofReal.continuousAt)
    have htend := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi k))
    refine ge_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsGT (show k < k + 1 by linarith)] with σ hσ
    exact hFreal σ hσ.1 hσ.2
  obtain ⟨r₀, hr₀, hr₀F⟩ : ∃ r₀ > 0, ∀ z ∈ ball (k : ℂ) r₀, 0 < (F z).re := by
    have hcont : ContinuousAt (fun z => (F z).re) (k : ℂ) :=
      Complex.continuous_re.continuousAt.comp (hFana k (by simpa using hθk) (by simp)).continuousAt
    have := hcont.eventually (lt_mem_nhds (show (0 : ℝ) < (F k).re by linarith))
    exact Metric.eventually_nhds_iff_ball.mp this
  set r : ℝ := min r₀ (min 1 (k - θ)) with hr
  have hr0 : 0 < r := lt_min hr₀ (lt_min one_pos (by linarith))
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrθ : r ≤ k - θ := (min_le_right _ _).trans (min_le_right _ _)
  have hball : ∀ z ∈ ball (k : ℂ) r, θ < z.re ∧ |z.im| < 4 ∧ 0 < (F z).re := by
    intro z hz
    have hF0 := hr₀F z (ball_subset_ball hrr₀ hz)
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - k)
    have h2 := Complex.abs_im_le_norm (z - k)
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at h1 h2
    have := neg_abs_le (z.re - k)
    exact ⟨by linarith, by linarith, hF0⟩
  -- the logarithm of `F` agrees with `L` on the right half of the ball
  set U : Set ℂ := ball (k : ℂ) r ∩ {z | k < z.re} with hU
  have hUo : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hUc : Convex ℝ U := (convex_ball _ _).inter (convex_halfSpace_re_gt k)
  have hlogF : AnalyticOnNhd ℂ (fun z => Complex.log (F z)) U := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hball z hz.1
    exact (hFana z h1 h2).clog (Or.inl h3)
  have hLU : AnalyticOnNhd ℂ L U := by
    have hdiff : DifferentiableOn ℂ L U := fun z hz =>
      (LSeries_hasDerivAt (hk.trans_lt (by exact_mod_cast hz.2))).differentiableAt
        |>.differentiableWithinAt
    exact hdiff.analyticOnNhd hUo
  set z₀ : ℂ := ((k + r / 2 : ℝ) : ℂ) with hz₀
  have hz₀U : z₀ ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, hz₀, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    · simp [hz₀]; linarith
  have hlogEq : EqOn (fun z => Complex.log (F z)) L U := by
    refine hlogF.eqOn_of_preconnected_of_frequently_eq hLU hUc.isPreconnected hz₀U ?_
    rw [Filter.frequently_iff]
    intro V hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhdsWithin_iff.mp hV
    set t : ℝ := min (ε / 2) (r / 4) with ht
    have ht0 : 0 < t := lt_min (by linarith) (by linarith)
    refine ⟨((k + r / 2 + t : ℝ) : ℂ), hεV ⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, dist_eq_norm, hz₀, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [show k + r / 2 + t - (k + r / 2) = t by ring, abs_of_pos ht0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · rw [mem_compl_singleton_iff, hz₀, Ne, Complex.ofReal_inj]
      linarith
    · set σ : ℝ := k + r / 2 + t with hσ
      have hσk : k < σ := by rw [hσ]; linarith
      have hσ1 : σ < k + 1 := by
        rw [hσ]; have := min_le_right (ε / 2) (r / 4); linarith
      have hσD : (σ : ℂ) ∈ D := ⟨by simpa using hσk, by simp⟩
      show Complex.log (F σ) = L σ
      rw [show F σ = Complex.exp (L σ) from hEq hσD]
      obtain ⟨him, _⟩ := hLreal σ hσk
      exact Complex.log_exp (by rw [him]; linarith [Real.pi_pos]) (by rw [him]; exact Real.pi_pos.le)
  -- Landau's theorem across the abscissa
  set d : ℝ := r / 8 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set G : ℂ → ℂ := fun z => if z ∈ ball (k : ℂ) r then Complex.log (F z) else L z with hG
  have hsum : LSeriesSummable (fun n => ((logCoeff e n : ℝ) : ℂ)) ((k + d : ℝ) : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by rw [hk]; simp; exact_mod_cast (by linarith))
  set R : NNReal := ⟨3 * d, by linarith⟩ with hR
  have hsub : closedBall (((k + d + d : ℝ)) : ℂ) (R : ℝ) ⊆ ball (k : ℂ) r := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    have hR' : (R : ℝ) = 3 * d := rfl
    rw [hR'] at hz
    calc ‖z - k‖ = ‖(z - ((k + d + d : ℝ) : ℂ)) + ((2 * d : ℝ) : ℂ)‖ := by
          congr 1; push_cast; ring
      _ ≤ ‖z - ((k + d + d : ℝ) : ℂ)‖ + ‖((2 * d : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 * d + 2 * d := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
      _ < r := by rw [hd]; linarith
  have hGd : DifferentiableOn ℂ G (closedBall (((k + d + d : ℝ)) : ℂ) (R : ℝ)) := by
    intro z hz
    have hzb := hsub hz
    obtain ⟨h1, h2, h3⟩ := hball z hzb
    have hev : G =ᶠ[𝓝 z] fun w => Complex.log (F w) := by
      filter_upwards [isOpen_ball.mem_nhds hzb] with w hw
      show (if w ∈ ball (k : ℂ) r then Complex.log (F w) else L w) = _
      rw [if_pos hw]
    exact ((hFana z h1 h2).differentiableAt.clog (Or.inl h3)).congr_of_eventuallyEq hev
      |>.differentiableWithinAt
  have hagree : ∀ s : ℂ, k + d < s.re → G s = LSeries (fun n => ((logCoeff e n : ℝ) : ℂ)) s := by
    intro s hs
    by_cases hsb : s ∈ ball (k : ℂ) r
    · show (if s ∈ ball (k : ℂ) r then Complex.log (F s) else L s) = _
      rw [if_pos hsb]
      exact hlogEq ⟨hsb, show k < s.re by linarith⟩
    · show (if s ∈ ball (k : ℂ) r then Complex.log (F s) else L s) = _
      rw [if_neg hsb]
  have hlandau := landau_local_summability_transfer (logCoeff_nonneg hadd) hd0 hsum
    (R := R) hGd hagree (σ := k - d / 2) (by
      have hR' : (R : ℝ) = 3 * d := rfl
      rw [hR']; linarith)
  have := hlandau.abscissaOfAbsConv_le
  rw [hk, Complex.ofReal_re] at this
  have h' : k ≤ k - d / 2 := EReal.coe_le_coe_iff.mp this
  linarith

/-- **Added generators cost the full dimension.**  If only generators are added and the integer
count is `A x + O(x^θ)`, then `Σ_n |e(n)| n^{-s}` converges for every `Re s > θ`. -/
theorem summable_pertSeq_of_nonpos (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1)
    (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : LSeries.convolution (fun n => ((Λ n - e n : ℝ) : ℂ)) (countSeq a) =
      LSeries.logMul (countSeq a))
    (hadd : ∀ n, e n ≤ 0) {A θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ) {s : ℂ} (hs : θ < s.re) :
    LSeriesSummable (pertSeq e) s := by
  have habs := abscissaOfAbsConv_logCoeff_le ha ha1 he hconv hadd hθ hN
  have h := LSeriesSummable_logMul_of_lt_re (habs.trans_lt (by exact_mod_cast hs))
  rw [logMul_logCoeff he] at h
  simpa using h.neg

end IntegerBeurling

end RHTower
