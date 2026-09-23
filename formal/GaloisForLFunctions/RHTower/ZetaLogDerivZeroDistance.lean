import GaloisForLFunctions.RHTower.ZetaLocalZeroCount
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary

/-!
# `ζ'/ζ ≪ log t` away from the zeros

At a point `s` of the strip `½ ≤ Re s ≤ 2`, height `|t| ≥ 4`, at distance at least `δ ≤ 1` from
every zero, `‖ζ'/ζ(s)‖ ≤ C · log|t| / δ`.  Mechanism: the partial fraction of `ξ'/ξ` (corpus
`logDeriv_xi_eq_partialFraction`) at `s` and at the anchor `s₀ = 3 + it` differ by
`Σ_ρ (s₀ − s)/((s−ρ)(s₀−ρ))`, whose terms are summed in unit windows of ordinates using the local
zero count `≪ log t`; the archimedean pieces are digamma bounds and the anchor value is the
von Mangoldt series at `Re = 3`, bounded by `ζ(2)`.
-/

open Complex Set Metric GaloisForLFunctions

namespace RHTower

noncomputable section

/-! ## The partial-fraction difference -/

theorem summable_partialFractionTerm {s : ℂ} (hs : xi s ≠ 0) :
    Summable fun q : XiZeroCopy => (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹) := by
  have hz : XiC ((s - 1 / 2) * -Complex.I) ≠ 0 := by
    rw [← xi_eq_XiC_comp]; exact hs
  refine ((summable_xiRelativeResolventTerm hz).mul_right (-Complex.I)).congr fun q => ?_
  rw [xiRelativeResolventTerm]
  have hspec : xiSpectralPoint q = ((q.1 : ℂ) - 1 / 2) * -Complex.I := rfl
  rw [hspec]
  have hth := resolvent_coordinate_transport ((q.1 : ℂ) - 1 / 2) (s - 1 / 2)
  rw [hth, show ((q.1 : ℂ)) - 1 / 2 - (s - 1 / 2) = -(s - (q.1 : ℂ)) by ring, inv_neg]
  ring

theorem logDeriv_xi_sub_eq_tsum {s s₀ : ℂ} (hs : xi s ≠ 0) (hs₀ : xi s₀ ≠ 0) :
    logDeriv xi s - logDeriv xi s₀
      = ∑' q : XiZeroCopy, ((s - (q.1 : ℂ))⁻¹ - (s₀ - (q.1 : ℂ))⁻¹) := by
  rw [logDeriv_xi_eq_partialFraction hs, logDeriv_xi_eq_partialFraction hs₀,
    ← (summable_partialFractionTerm hs).tsum_sub (summable_partialFractionTerm hs₀)]
  congr 1
  funext q
  ring

theorem summable_partialFractionDiff {s s₀ : ℂ} (hs : xi s ≠ 0) (hs₀ : xi s₀ ≠ 0) :
    Summable fun q : XiZeroCopy => ((s - (q.1 : ℂ))⁻¹ - (s₀ - (q.1 : ℂ))⁻¹) := by
  refine ((summable_partialFractionTerm hs).sub (summable_partialFractionTerm hs₀)).congr fun q => ?_
  ring

/-! ## The split of `ζ'/ζ` through `ξ'/ξ` off the zero set -/

theorem logDeriv_zeta_eq_logDeriv_xi {s : ℂ} (hre : 0 < s.re) (h1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv xi s - s⁻¹ - (s - 1)⁻¹ - logDeriv Gammaℝ s := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hre
  have hVopen : IsOpen {w : ℂ | 0 < w.re ∧ w ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have heq : xi =ᶠ[nhds s] fun z => xiUnit z * riemannZeta z := by
    refine Filter.eventuallyEq_of_mem (hVopen.mem_nhds ⟨hre, h1⟩) fun w hw => ?_
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    exact xi_eq_xiUnit_mul_zeta hw0 hw.2 hw.1
  have hxi : logDeriv xi s = logDeriv (fun z => xiUnit z * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  have hpoly : HasDerivAt (fun z : ℂ => z * (z - 1) / 2) ((1 * (s - 1) + s * 1) / 2) s :=
    ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
  have hp0 : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero
  have hΓ : Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  have hu : logDeriv xiUnit s = s⁻¹ + (s - 1)⁻¹ + logDeriv Gammaℝ s := by
    unfold xiUnit
    rw [logDeriv_mul s hp0 hΓ hpoly.differentiableAt (hasDerivAt_Gammaℝ_of_re_pos hre).differentiableAt]
    congr 1
    rw [logDeriv_apply, hpoly.deriv]
    field_simp
  rw [hxi, logDeriv_mul s (xiUnit_ne_zero h0 h1 hre) hζ (analyticAt_xiUnit hre).differentiableAt
    (differentiableAt_riemannZeta h1), hu]
  ring

/-! ## Bounds at the anchor `3 + it` -/

theorem norm_logDeriv_zeta_three_le (t : ℝ) :
    ‖logDeriv riemannZeta ((3 : ℂ) + t * I)‖ ≤ 2 := by
  have hre : (1 : ℝ) < ((3 : ℂ) + t * I).re := by simp
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hζ : riemannZeta ((3 : ℂ) + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  have hlog : logDeriv riemannZeta ((3 : ℂ) + t * I)
      = -LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((3 : ℂ) + t * I) := by
    rw [hL, logDeriv_apply]; ring
  rw [hlog, norm_neg]
  unfold LSeries
  have hbound : ∀ n : ℕ, ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      ((3 : ℂ) + t * I) n‖ ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have hre3 : ((3 : ℂ) + t * I).re = 3 := by simp
      rw [hre3]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hΛ : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log.trans
          (by linarith [Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < n)])
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 := by gcongr
        _ = 1 * (n : ℝ) ^ (3 : ℝ) := by
            rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hsum : Summable fun n : ℕ => ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      ((3 : ℂ) + t * I) n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound summable_one_div_nat_sq
  calc ‖∑' n, LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((3 : ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((3 : ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := hsum.tsum_le_tsum hbound summable_one_div_nat_sq
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 2 := by
        have := Real.pi_lt_d2
        have := Real.pi_pos
        nlinarith

/-- The digamma piece of `logDeriv Γ_ℝ` on a vertical line of height `t ≥ 4`, real part in
`[½, 3]`. -/
theorem norm_logDeriv_Gammaℝ_le {σ t : ℝ} (hσ : 1 / 2 ≤ σ) (hσ3 : σ ≤ 3) (ht : 4 ≤ t) :
    ‖logDeriv Gammaℝ ((σ : ℂ) + t * I)‖ ≤ Real.log t + digammaVerticalLogConstant := by
  have hre : 0 < ((σ : ℂ) + t * I).re := by simp; linarith
  rw [logDeriv_Gammaℝ_digamma hre]
  have hhalf : ((σ : ℂ) + t * I) / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hhalf]
  have hψ := norm_digamma_vertical_le_log (σ := σ / 2) (t := t / 2) (by linarith) (by linarith)
    (by linarith)
  have hc : 0 ≤ digammaVerticalLogConstant := by
    unfold digammaVerticalLogConstant
    have := Real.pi_pos
    have := Real.log_pos (by norm_num : (1:ℝ) < 2)
    linarith
  have hlogπ : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogπ2 : Real.log Real.pi ≤ 2 := by
    have h1 : Real.log Real.pi < Real.log 4 := Real.log_lt_log Real.pi_pos Real.pi_lt_four
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have := Real.log_two_lt_d9
    linarith
  have hlog2 : Real.log (t / 2) ≤ Real.log t := Real.log_le_log (by linarith) (by linarith)
  have hlog2' : 0 ≤ Real.log (t / 2) := Real.log_nonneg (by linarith)
  have hπ := Real.pi_pos
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  calc ‖Complex.digamma (((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2 - (Real.log Real.pi : ℂ) / 2‖
      ≤ ‖Complex.digamma (((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2‖
        + ‖(Real.log Real.pi : ℂ) / 2‖ := norm_sub_le _ _
    _ = ‖Complex.digamma (((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ / 2 + Real.log Real.pi / 2 := by
        rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogπ]
        norm_num
    _ ≤ (Real.log (t / 2) + digammaVerticalLogConstant) / 2 + 2 / 2 := by gcongr
    _ ≤ Real.log t + digammaVerticalLogConstant := by
        unfold digammaVerticalLogConstant
        linarith

/-! ## The finite constant for small heights -/

/-- The zero copies of height at most `6`. -/
def smallHeightCopies : Set XiZeroCopy := {q | |(q.1 : ℂ).im| ≤ 6}

theorem smallHeightCopies_finite : smallHeightCopies.Finite := by
  classical
  have hZ : (xiZeroSet_weilLagFunctionCriterion ∩ closedBall (0 : ℂ) 7).Finite :=
    finite_xiZeroSet_inter (isCompact_closedBall _ _)
  -- every small-height copy sits over a zero in the ball
  have hsub : smallHeightCopies ⊆
      ⋃ ρ ∈ xiZeroSet_weilLagFunctionCriterion ∩ closedBall (0 : ℂ) 7, {q : XiZeroCopy | (q.1 : ℂ) = ρ} := by
    intro q hq
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    refine ⟨(q.1 : ℂ), ⟨xi_xiZeroCopy_eq_zero q, ?_⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    have hre := xiZeroCopy_re_pos q
    have hre1 := xiZeroCopy_re_lt_one q
    have him : |(q.1 : ℂ).im| ≤ 6 := hq
    calc ‖(q.1 : ℂ)‖ ≤ |(q.1 : ℂ).re| + |(q.1 : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + 6 := by
          gcongr
          rw [abs_le]; constructor <;> linarith
      _ = 7 := by norm_num
  refine (hZ.biUnion fun ρ _ => ?_).subset hsub
  -- each fibre is finite: the copy index is injective on it and lands in `Iio d`
  have hinj : Set.InjOn (fun q : XiZeroCopy => (q.2 : ℕ)) {q : XiZeroCopy | (q.1 : ℂ) = ρ} := by
    intro q hq q' hq' hqq'
    have hq1 : (q.1 : ℂ) = ρ := hq
    have hq1' : (q'.1 : ℂ) = ρ := hq'
    have h1 : q.1 = q'.1 := Subtype.ext (hq1.trans hq1'.symm)
    exact Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).mpr hqq')
  refine Set.Finite.of_finite_image ((Set.finite_Iio
    ((MeromorphicOn.divisor xi Set.univ ρ).toNat)).subset ?_) hinj
  rintro _ ⟨q, hq, rfl⟩
  have hq' : (q.1 : ℂ) = ρ := hq
  exact lt_of_lt_of_eq q.2.isLt (by rw [hq'])

/-- The number of zero copies of height at most `6`. -/
def smallHeightCount : ℕ := smallHeightCopies_finite.toFinset.card

theorem card_le_smallHeightCount (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, |(q.1 : ℂ).im| ≤ 6) : F.card ≤ smallHeightCount := by
  classical
  unfold smallHeightCount
  refine Finset.card_le_card fun q hq => ?_
  rw [Set.Finite.mem_toFinset]
  exact hF q hq

/-! ## Window counts -/

/-- The number of copies with `|γ − t| ∈ [k, k+1)` is at most `80 log(180(t+k+1)) + K₀`. -/
theorem card_zeroWindow_le {t : ℝ} (ht : 4 ≤ t) (k : ℕ) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, (k : ℝ) ≤ |t - (q.1 : ℂ).im| ∧ |t - (q.1 : ℂ).im| < k + 1) :
    (F.card : ℝ) ≤ 80 * Real.log (180 * (t + k + 1)) + smallHeightCount := by
  classical
  set Fp := F.filter (fun q : XiZeroCopy => t ≤ (q.1 : ℂ).im) with hFp
  set Fm := F.filter (fun q : XiZeroCopy => ¬ (t ≤ (q.1 : ℂ).im)) with hFm
  have hcard : F.card = Fp.card + Fm.card := (Finset.card_filter_add_card_filter_not _).symm
  have hlogmono : Real.log (180 * (t + k + 1 / 2)) ≤ Real.log (180 * (t + k + 1)) :=
    Real.log_le_log (by positivity) (by linarith)
  -- upper piece: ordinates in `[t + k, t + k + 1)`, within `1` of `t + k + ½`
  have hplus : (Fp.card : ℝ) ≤ 40 * Real.log (180 * (t + k + 1)) := by
    have hc : 4 ≤ |t + k + 1 / 2| := by
      rw [abs_of_pos (by positivity)]; linarith
    refine (card_le_of_ordinates_in_window hc Fp fun q hq => ?_).trans ?_
    · rw [hFp, Finset.mem_filter] at hq
      obtain ⟨hq1, hq2⟩ := hq
      have hw := hF q hq1
      rw [abs_of_nonpos (by linarith)] at hw
      rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
    · rw [abs_of_pos (by positivity)]
      linarith
  -- lower piece: ordinates in `(t − k − 1, t − k]`
  have hminus : (Fm.card : ℝ) ≤ 40 * Real.log (180 * (t + k + 1)) + smallHeightCount := by
    rcases le_or_gt 4 |t - k - 1 / 2| with hc | hc
    · refine (card_le_of_ordinates_in_window hc Fm fun q hq => ?_).trans ?_
      · rw [hFm, Finset.mem_filter] at hq
        obtain ⟨hq1, hq2⟩ := hq
        push Not at hq2
        have hw := hF q hq1
        rw [abs_of_pos (by linarith)] at hw
        rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
      · have habs : |t - k - 1 / 2| ≤ t + k + 1 := by
          rw [abs_le]; constructor <;> linarith
        have hlog : Real.log (180 * |t - k - 1 / 2|) ≤ Real.log (180 * (t + k + 1)) :=
          Real.log_le_log (by positivity) (by linarith)
        have : (0 : ℝ) ≤ smallHeightCount := Nat.cast_nonneg _
        linarith
    · -- all these copies have height at most `6`
      have hsmall : (Fm.card : ℝ) ≤ smallHeightCount := by
        have := card_le_smallHeightCount Fm fun q hq => by
          rw [hFm, Finset.mem_filter] at hq
          obtain ⟨hq1, hq2⟩ := hq
          push Not at hq2
          have hw := hF q hq1
          rw [abs_of_pos (by linarith)] at hw
          have hc' := abs_lt.mp hc
          rw [abs_le]; constructor <;> linarith [hw.1, hw.2, hc'.1, hc'.2]
        exact_mod_cast this
      have : 0 ≤ Real.log (180 * (t + k + 1)) := Real.log_nonneg (by nlinarith)
      linarith
  have : (F.card : ℝ) = Fp.card + Fm.card := by rw [hcard]; push_cast; ring
  linarith

/-! ## Two telescoping tail sums -/

theorem sum_inv_sq_Ico_le_aux (K : ℕ) (hK : 2 ≤ K) :
    ∑ k ∈ Finset.Ico 2 K, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 - 1 / ((K : ℝ) - 1) := by
  induction K with
  | zero => omega
  | succ K ih =>
      rcases Nat.lt_or_ge K 2 with hK' | hK'
      · interval_cases K
        · omega
        · norm_num
      · rw [Finset.sum_Ico_succ_top hK']
        have hK1 : (1 : ℝ) < K := by exact_mod_cast hK'
        have h1 : (1 : ℝ) / (K : ℝ) ^ 2 ≤ 1 / ((K : ℝ) - 1) - 1 / (K : ℝ) := by
          rw [div_sub_div _ _ (by linarith) (by linarith),
            div_le_div_iff₀ (by positivity) (by nlinarith)]
          nlinarith
        have := ih hK'
        have e : ((K + 1 : ℕ) : ℝ) - 1 = K := by push_cast; ring
        rw [e]
        linarith

theorem sum_inv_sq_Ico_le (K : ℕ) : ∑ k ∈ Finset.Ico 2 K, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · interval_cases K <;> simp
  · have := sum_inv_sq_Ico_le_aux K hK
    have hK1 : (1 : ℝ) < K := by exact_mod_cast hK
    have : (0 : ℝ) ≤ 1 / ((K : ℝ) - 1) := by
      apply div_nonneg zero_le_one; linarith
    linarith

theorem inv_mul_sqrt_le_telescope {k : ℕ} (hk : 2 ≤ k) :
    (1 : ℝ) / ((k : ℝ) * Real.sqrt k) ≤ 2 * (1 / Real.sqrt ((k : ℝ) - 1) - 1 / Real.sqrt k) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hk0 : (0 : ℝ) < k := by linarith
  set a := Real.sqrt ((k : ℝ) - 1) with ha
  set b := Real.sqrt (k : ℝ) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr hk0
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hbb : b * b = k := Real.mul_self_sqrt hk0.le
  have haa : a * a = (k : ℝ) - 1 := Real.mul_self_sqrt (by linarith)
  -- 1/a − 1/b = (b − a)/(ab) and b − a = 1/(a + b) ≥ 1/(2b)
  have hdiff : b - a = 1 / (a + b) := by
    rw [eq_div_iff (by positivity)]
    nlinarith
  have hsub : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  rw [hsub, hdiff]
  have h1 : (1 : ℝ) / ((k : ℝ) * b) = 1 / (b * b * b) := by rw [hbb]
  rw [h1, div_le_iff₀ (by positivity)]
  have h2 : 2 * (1 / (a + b) / (a * b)) * (b * b * b) = 2 * b * b / (a + b) / a := by
    field_simp
  rw [h2]
  have h3 : (1 : ℝ) ≤ 2 * b * b / (a + b) / a := by
    rw [le_div_iff₀ ha0, le_div_iff₀ (by positivity)]
    nlinarith
  exact h3

theorem sum_inv_mul_sqrt_Ico_le_aux (K : ℕ) (hK : 2 ≤ K) :
    ∑ k ∈ Finset.Ico 2 K, (1 : ℝ) / ((k : ℝ) * Real.sqrt k)
      ≤ 2 * (1 - 1 / Real.sqrt ((K : ℝ) - 1)) := by
  induction K with
  | zero => omega
  | succ K ih =>
      rcases Nat.lt_or_ge K 2 with hK' | hK'
      · interval_cases K
        · omega
        · norm_num
      · rw [Finset.sum_Ico_succ_top hK']
        have := ih hK'
        have h2 := inv_mul_sqrt_le_telescope hK'
        have e : ((K + 1 : ℕ) : ℝ) - 1 = K := by push_cast; ring
        rw [e]
        linarith

theorem sum_inv_mul_sqrt_Ico_le (K : ℕ) :
    ∑ k ∈ Finset.Ico 2 K, (1 : ℝ) / ((k : ℝ) * Real.sqrt k) ≤ 2 := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · interval_cases K <;> simp
  · have := sum_inv_mul_sqrt_Ico_le_aux K hK
    have : (0 : ℝ) ≤ 1 / Real.sqrt ((K : ℝ) - 1) := by positivity
    linarith

/-- `log(k+2) ≤ 2√k + 3` for `k ≥ 2`. -/
theorem log_add_two_le {k : ℕ} (hk : 2 ≤ k) :
    Real.log ((k : ℝ) + 2) ≤ 2 * Real.sqrt k + 3 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := Real.log_le_rpow_div (x := (k : ℝ) + 2) (by linarith) (by norm_num : (0:ℝ) < 1 / 2)
  have hs : ((k : ℝ) + 2) ^ ((1 : ℝ) / 2) = Real.sqrt ((k : ℝ) + 2) := by
    rw [Real.sqrt_eq_rpow]
  rw [hs] at h
  have hsq : Real.sqrt ((k : ℝ) + 2) ≤ Real.sqrt k + Real.sqrt 2 := by
    rw [Real.sqrt_le_left]
    · nlinarith [Real.sq_sqrt hk0, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (k:ℝ), Real.sqrt_nonneg 2]
    · positivity
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

theorem sum_log_div_sq_Ico_le (K : ℕ) :
    ∑ k ∈ Finset.Ico 2 K, Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2 ≤ 7 := by
  have h1 := sum_inv_sq_Ico_le K
  have h2 := sum_inv_mul_sqrt_Ico_le K
  have hterm : ∀ k ∈ Finset.Ico 2 K, Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2
      ≤ 2 * (1 / ((k : ℝ) * Real.sqrt k)) + 3 * (1 / (k : ℝ) ^ 2) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hl := log_add_two_le hk2
    have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
    have hsk0 : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    rw [div_le_iff₀ (by positivity)]
    have e : (2 * (1 / ((k : ℝ) * Real.sqrt k)) + 3 * (1 / (k : ℝ) ^ 2)) * (k : ℝ) ^ 2
        = 2 * Real.sqrt k + 3 := by
      field_simp
      nlinarith [hsk]
    rw [e]; exact hl
  calc ∑ k ∈ Finset.Ico 2 K, Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2
      ≤ ∑ k ∈ Finset.Ico 2 K, (2 * (1 / ((k : ℝ) * Real.sqrt k)) + 3 * (1 / (k : ℝ) ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ k ∈ Finset.Ico 2 K, (1 / ((k : ℝ) * Real.sqrt k))
        + 3 * ∑ k ∈ Finset.Ico 2 K, (1 / (k : ℝ) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * 2 + 3 * 1 := by gcongr
    _ = 7 := by norm_num

/-! ## Numerical constants -/

theorem log_ge_of_four_le {t : ℝ} (ht : 4 ≤ t) : (1.38 : ℝ) ≤ Real.log t := by
  have h := Real.log_le_log (by norm_num) ht
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_gt_d9
  linarith

theorem log_360_lt : Real.log 360 < (6.24 : ℝ) := by
  have h := Real.log_lt_log (by norm_num) (by norm_num : (360 : ℝ) < 2 ^ 9)
  rw [Real.log_pow] at h
  push_cast at h
  have := Real.log_two_lt_d9
  linarith

theorem log_zeroWindow_le {t : ℝ} (ht : 4 ≤ t) (k : ℕ) :
    Real.log (180 * (t + k + 1)) ≤ 6 * Real.log t + Real.log ((k : ℝ) + 2) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : 180 * (t + k + 1) ≤ 360 * t * ((k : ℝ) + 2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - 4) hk]
  have h2 : Real.log (180 * (t + k + 1)) ≤ Real.log (360 * t * ((k : ℝ) + 2)) :=
    Real.log_le_log (by positivity) h1
  have ht0 : t ≠ 0 := (by linarith : (0 : ℝ) < t).ne'
  rw [Real.log_mul (mul_ne_zero (by norm_num) ht0) (by positivity),
    Real.log_mul (by norm_num) ht0] at h2
  have := log_360_lt
  have := log_ge_of_four_le ht
  linarith

theorem log_window_small_le {t : ℝ} (ht : 4 ≤ t) {k : ℕ} (hk : k ≤ 2) :
    Real.log (180 * (t + k + 1)) ≤ 7 * Real.log t := by
  have h := log_zeroWindow_le ht k
  have hk' : (k : ℝ) + 2 ≤ 4 := by
    have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    linarith
  have h4 : Real.log ((k : ℝ) + 2) ≤ Real.log 4 := Real.log_le_log (by positivity) hk'
  have h4' : Real.log 4 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  linarith

theorem sum_window_tail_le {t : ℝ} (ht : 4 ≤ t) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (K : ℕ) :
    ∑ k ∈ Finset.Ico 2 K, (80 * Real.log (180 * (t + k + 1)) + K₀) * (5 / 2 / (k : ℝ) ^ 2)
      ≤ 5 / 2 * (480 * Real.log t + 560 + K₀) := by
  have h1 := sum_inv_sq_Ico_le K
  have h2 := sum_log_div_sq_Ico_le K
  have hLt := log_ge_of_four_le ht
  have hterm : ∀ k ∈ Finset.Ico 2 K,
      (80 * Real.log (180 * (t + k + 1)) + K₀) * (5 / 2 / (k : ℝ) ^ 2)
        ≤ 5 / 2 * (480 * Real.log t * (1 / (k : ℝ) ^ 2)
          + 80 * (Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2) + K₀ * (1 / (k : ℝ) ^ 2)) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hl := log_zeroWindow_le ht k
    have e : (5 : ℝ) / 2 * (480 * Real.log t * (1 / (k : ℝ) ^ 2)
          + 80 * (Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2) + K₀ * (1 / (k : ℝ) ^ 2))
        = (80 * (6 * Real.log t + Real.log ((k : ℝ) + 2)) + K₀) * (5 / 2 / (k : ℝ) ^ 2) := by
      field_simp
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  calc ∑ k ∈ Finset.Ico 2 K, (80 * Real.log (180 * (t + k + 1)) + K₀) * (5 / 2 / (k : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.Ico 2 K, 5 / 2 * (480 * Real.log t * (1 / (k : ℝ) ^ 2)
          + 80 * (Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2) + K₀ * (1 / (k : ℝ) ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = 5 / 2 * (480 * Real.log t * ∑ k ∈ Finset.Ico 2 K, (1 / (k : ℝ) ^ 2)
          + 80 * ∑ k ∈ Finset.Ico 2 K, (Real.log ((k : ℝ) + 2) / (k : ℝ) ^ 2)
          + K₀ * ∑ k ∈ Finset.Ico 2 K, (1 / (k : ℝ) ^ 2)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ 5 / 2 * (480 * Real.log t * 1 + 80 * 7 + K₀ * 1) := by gcongr
    _ = 5 / 2 * (480 * Real.log t + 560 + K₀) := by ring

/-! ## The partial-fraction terms -/

/-- The window index of a zero copy relative to the height `t`. -/
def windowIndex (t : ℝ) (q : XiZeroCopy) : ℕ := ⌊|t - (q.1 : ℂ).im|⌋₊

/-- The bound on one partial-fraction difference in the window `k`. -/
def windowWeight (δ : ℝ) (k : ℕ) : ℝ := if k < 2 then 5 / 4 / δ else 5 / 2 / (k : ℝ) ^ 2

theorem windowWeight_nonneg {δ : ℝ} (hδ : 0 < δ) (k : ℕ) : 0 ≤ windowWeight δ k := by
  unfold windowWeight; split_ifs <;> positivity

theorem windowIndex_le (t : ℝ) (q : XiZeroCopy) :
    (windowIndex t q : ℝ) ≤ |t - (q.1 : ℂ).im| :=
  Nat.floor_le (abs_nonneg _)

theorem norm_partialFractionDiff_eq {s s₀ ρ : ℂ} (hs : s - ρ ≠ 0) (hs₀ : s₀ - ρ ≠ 0) :
    ‖(s - ρ)⁻¹ - (s₀ - ρ)⁻¹‖ = ‖s₀ - s‖ / (‖s - ρ‖ * ‖s₀ - ρ‖) := by
  rw [inv_sub_inv hs hs₀, norm_div, norm_mul, show s₀ - ρ - (s - ρ) = s₀ - s by ring]

theorem abs_im_le_norm_sub {s : ℂ} {t : ℝ} (hs : s.im = t) (q : XiZeroCopy) :
    |t - (q.1 : ℂ).im| ≤ ‖s - (q.1 : ℂ)‖ := by
  have h := Complex.abs_im_le_norm (s - (q.1 : ℂ))
  rwa [Complex.sub_im, hs] at h

theorem two_le_norm_anchor_sub (t : ℝ) (q : XiZeroCopy) :
    2 ≤ ‖(3 + t * I : ℂ) - (q.1 : ℂ)‖ := by
  have h := Complex.abs_re_le_norm ((3 + t * I : ℂ) - (q.1 : ℂ))
  have hre := xiZeroCopy_re_lt_one q
  have e : ((3 + t * I : ℂ) - (q.1 : ℂ)).re = 3 - (q.1 : ℂ).re := by simp
  rw [e, abs_of_pos (by linarith)] at h
  linarith

theorem norm_term_le_windowWeight {σ t δ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (hδ : 0 < δ)
    (q : XiZeroCopy) (hq : δ ≤ ‖(σ + t * I : ℂ) - (q.1 : ℂ)‖) :
    ‖((σ + t * I : ℂ) - (q.1 : ℂ))⁻¹ - ((3 + t * I : ℂ) - (q.1 : ℂ))⁻¹‖
      ≤ windowWeight δ (windowIndex t q) := by
  have h2 := two_le_norm_anchor_sub t q
  have hs : (σ + t * I : ℂ) - (q.1 : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hq; linarith
  have hs₀ : (3 + t * I : ℂ) - (q.1 : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; linarith
  rw [norm_partialFractionDiff_eq hs hs₀]
  have hnum : ‖(3 + t * I : ℂ) - (σ + t * I)‖ ≤ 5 / 2 := by
    rw [show (3 + t * I : ℂ) - (σ + t * I) = ((3 - σ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have him := abs_im_le_norm_sub (s := σ + t * I) (t := t) (by simp) q
  have him₀ := abs_im_le_norm_sub (s := 3 + t * I) (t := t) (by simp) q
  have hk := windowIndex_le t q
  unfold windowWeight
  split_ifs with hlt
  · calc ‖(3 + t * I : ℂ) - (σ + t * I)‖
          / (‖(σ + t * I : ℂ) - (q.1 : ℂ)‖ * ‖(3 + t * I : ℂ) - (q.1 : ℂ)‖)
        ≤ (5 / 2) / (δ * 2) := by
          apply div_le_div₀ (by norm_num) hnum (by positivity)
          exact mul_le_mul hq h2 (by norm_num) (norm_nonneg _)
      _ = 5 / 4 / δ := by field_simp; ring
  · push Not at hlt
    have hk2 : (2 : ℝ) ≤ windowIndex t q := by exact_mod_cast hlt
    have hks : (windowIndex t q : ℝ) ≤ ‖(σ + t * I : ℂ) - (q.1 : ℂ)‖ := hk.trans him
    have hks₀ : (windowIndex t q : ℝ) ≤ ‖(3 + t * I : ℂ) - (q.1 : ℂ)‖ := hk.trans him₀
    calc ‖(3 + t * I : ℂ) - (σ + t * I)‖
          / (‖(σ + t * I : ℂ) - (q.1 : ℂ)‖ * ‖(3 + t * I : ℂ) - (q.1 : ℂ)‖)
        ≤ (5 / 2) / ((windowIndex t q : ℝ) * (windowIndex t q : ℝ)) := by
          apply div_le_div₀ (by norm_num) hnum (by positivity)
          exact mul_le_mul hks hks₀ (by positivity) (norm_nonneg _)
      _ = 5 / 2 / (windowIndex t q : ℝ) ^ 2 := by ring

/-! ## The finite-sum bound -/

theorem sum_norm_partialFractionDiff_le {σ t δ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hall : ∀ q : XiZeroCopy, δ ≤ ‖(σ + t * I : ℂ) - (q.1 : ℂ)‖) (F : Finset XiZeroCopy) :
    ∑ q ∈ F, ‖((σ + t * I : ℂ) - (q.1 : ℂ))⁻¹ - ((3 + t * I : ℂ) - (q.1 : ℂ))⁻¹‖
      ≤ (3650 + 5 * smallHeightCount) * Real.log t / δ := by
  classical
  set K₀ : ℝ := (smallHeightCount : ℝ) with hK₀def
  have hK₀ : 0 ≤ K₀ := Nat.cast_nonneg _
  set Lt := Real.log t with hLtdef
  have hLt : 1.38 ≤ Lt := log_ge_of_four_le ht
  set K := F.sup (windowIndex t) + 1 with hKdef
  have hmaps : ∀ q ∈ F, windowIndex t q ∈ Finset.range K := fun q hq =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := windowIndex t) hq))
  set h : ℕ → ℝ := fun k => (80 * Real.log (180 * (t + k + 1)) + K₀) * windowWeight δ k
    with hdef
  have hlogpos : ∀ k : ℕ, 0 ≤ Real.log (180 * (t + k + 1)) := fun k =>
    Real.log_nonneg (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; nlinarith)
  have hnonneg : ∀ k, 0 ≤ h k := fun k =>
    mul_nonneg (by have := hlogpos k; positivity) (windowWeight_nonneg hδ k)
  have hfib : ∀ k ∈ Finset.range K,
      ∑ q ∈ F with windowIndex t q = k, windowWeight δ (windowIndex t q) ≤ h k := by
    intro k _
    have e : ∑ q ∈ F with windowIndex t q = k, windowWeight δ (windowIndex t q)
        = ∑ q ∈ F with windowIndex t q = k, windowWeight δ k :=
      Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.mp hq).2]
    rw [e, Finset.sum_const, nsmul_eq_mul, hdef]
    apply mul_le_mul_of_nonneg_right _ (windowWeight_nonneg hδ k)
    apply card_zeroWindow_le ht k
    intro q hq
    have := (Finset.mem_filter.mp hq).2
    exact (Nat.floor_eq_iff (abs_nonneg _)).mp this
  have hh0 : h 0 ≤ (700 * Lt + 5 / 4 * K₀) / δ := by
    have hl := log_window_small_le ht (k := 0) (by norm_num)
    have hw : windowWeight δ 0 = 5 / 4 / δ := by simp [windowWeight]
    simp only [hdef, hw, Nat.cast_zero, add_zero]
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hδ]
    simp only [Nat.cast_zero, add_zero] at hl
    linarith
  have hh1 : h 1 ≤ (700 * Lt + 5 / 4 * K₀) / δ := by
    have hl := log_window_small_le ht (k := 1) (by norm_num)
    have hw : windowWeight δ 1 = 5 / 4 / δ := by simp [windowWeight]
    simp only [hdef, hw, Nat.cast_one]
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hδ]
    simp only [Nat.cast_one] at hl
    linarith
  have htail : ∑ k ∈ Finset.Ico 2 (max K 2), h k ≤ 5 / 2 * (480 * Lt + 560 + K₀) := by
    have e : ∀ k ∈ Finset.Ico 2 (max K 2), h k
        = (80 * Real.log (180 * (t + k + 1)) + K₀) * (5 / 2 / (k : ℝ) ^ 2) := by
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
      simp only [hdef, windowWeight, if_neg (by omega : ¬ k < 2)]
    rw [Finset.sum_congr rfl e]
    exact sum_window_tail_le ht hK₀ _
  calc ∑ q ∈ F, ‖((σ + t * I : ℂ) - (q.1 : ℂ))⁻¹ - ((3 + t * I : ℂ) - (q.1 : ℂ))⁻¹‖
      ≤ ∑ q ∈ F, windowWeight δ (windowIndex t q) :=
        Finset.sum_le_sum fun q _ => norm_term_le_windowWeight hσ hσ2 hδ q (hall q)
    _ = ∑ k ∈ Finset.range K, ∑ q ∈ F with windowIndex t q = k,
          windowWeight δ (windowIndex t q) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.range K, h k := Finset.sum_le_sum hfib
    _ ≤ ∑ k ∈ Finset.range (max K 2), h k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
          (fun k _ _ => hnonneg k)
    _ = h 0 + h 1 + ∑ k ∈ Finset.Ico 2 (max K 2), h k := by
        rw [← Finset.sum_range_add_sum_Ico h (le_max_right K 2), Finset.sum_range_succ,
          Finset.sum_range_one]
    _ ≤ (700 * Lt + 5 / 4 * K₀) / δ + (700 * Lt + 5 / 4 * K₀) / δ
          + 5 / 2 * (480 * Lt + 560 + K₀) := by gcongr
    _ ≤ (3650 + 5 * K₀) * Lt / δ := by
        rw [← add_div, div_add' _ _ _ hδ.ne', div_le_div_iff_of_pos_right hδ]
        have e1 : 5 / 2 * (480 * Lt + 560 + K₀) * δ ≤ 5 / 2 * (480 * Lt + 560 + K₀) :=
          mul_le_of_le_one_right (by positivity) hδ1
        have e2 : K₀ ≤ K₀ * Lt := le_mul_of_one_le_right hK₀ (by linarith)
        nlinarith

/-! ## The bound on `ζ'/ζ` -/

/-- The constant in the bound `|ζ'/ζ(s)| ≤ C log t / δ`. -/
def logDerivZetaConstant : ℝ := 3700 + 5 * smallHeightCount

theorem norm_inv_le_quarter {s : ℂ} {t : ℝ} (hs : s.im = t) (ht : 4 ≤ t) : ‖s⁻¹‖ ≤ 1 / 4 := by
  have h := Complex.abs_im_le_norm s
  rw [hs, abs_of_pos (by linarith)] at h
  rw [norm_inv, one_div]
  exact inv_anti₀ (by norm_num) (by linarith)

/-- **The logarithmic derivative of `ζ` away from zeros.**  For `½ ≤ σ ≤ 2`, `t ≥ 4` and
`0 < δ ≤ 1` with every nontrivial zero at distance at least `δ` from `s = σ + it`,
`|ζ'/ζ(s)| ≤ C log t / δ` with the explicit constant `C = 3700 + 5 K₀`, where `K₀` is the
number of zero copies of height at most `6`. -/
theorem norm_logDeriv_zeta_le {σ t δ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hall : ∀ q : XiZeroCopy, δ ≤ ‖(σ + t * I : ℂ) - (q.1 : ℂ)‖) :
    ‖logDeriv riemannZeta (σ + t * I)‖ ≤ logDerivZetaConstant * Real.log t / δ := by
  set s : ℂ := σ + t * I with hsdef
  set s₀ : ℂ := 3 + t * I with hs₀def
  have hsim : s.im = t := by simp [hsdef]
  have hs₀im : s₀.im = t := by simp [hs₀def]
  have hsre : s.re = σ := by simp [hsdef]
  have hs₀re : s₀.re = 3 := by simp [hs₀def]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim, Complex.one_im] at this; linarith
  have hs₀1 : s₀ ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hs₀im, Complex.one_im] at this; linarith
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hsim, Complex.zero_im] at this; linarith
  have hs₀0 : s₀ ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hs₀im, Complex.zero_im] at this; linarith
  have hxis : xi s ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h
    have := hall q
    rw [hq, sub_self, norm_zero] at this
    linarith
  have hxis₀ : xi s₀ ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h
    have := xiZeroCopy_re_lt_one q
    rw [hq, hs₀re] at this
    linarith
  have hζs : riemannZeta s ≠ 0 := by
    intro h
    apply hxis
    rw [xi_eq_xiUnit_mul_zeta hs0 hs1 (by rw [hsre]; linarith), h, mul_zero]
  have hζs₀ : riemannZeta s₀ ≠ 0 := by
    intro h
    apply hxis₀
    rw [xi_eq_xiUnit_mul_zeta hs₀0 hs₀1 (by rw [hs₀re]; norm_num), h, mul_zero]
  -- the decomposition
  have hdec := logDeriv_zeta_eq_logDeriv_xi (s := s) (by rw [hsre]; linarith) hs1 hζs
  have hdec₀ := logDeriv_zeta_eq_logDeriv_xi (s := s₀) (by rw [hs₀re]; norm_num) hs₀1 hζs₀
  have hpf := logDeriv_xi_sub_eq_tsum hxis hxis₀
  -- the tsum bound
  have hsum : Summable fun q : XiZeroCopy => ‖(s - (q.1 : ℂ))⁻¹ - (s₀ - (q.1 : ℂ))⁻¹‖ :=
    summable_norm_iff.mpr (summable_partialFractionDiff hxis hxis₀)
  have htsum : ‖∑' q : XiZeroCopy, ((s - (q.1 : ℂ))⁻¹ - (s₀ - (q.1 : ℂ))⁻¹)‖
      ≤ (3650 + 5 * smallHeightCount) * Real.log t / δ := by
    refine (norm_tsum_le_tsum_norm hsum).trans ?_
    exact hsum.tsum_le_of_sum_le fun F =>
      sum_norm_partialFractionDiff_le hσ hσ2 ht hδ hδ1 hall F
  -- the boundary terms
  have hz₀ := norm_logDeriv_zeta_three_le t
  have hi₀ := norm_inv_le_quarter hs₀im ht
  have hi₀' : ‖(s₀ - 1)⁻¹‖ ≤ 1 / 4 := norm_inv_le_quarter (s := s₀ - 1) (by simp [hs₀im]) ht
  have hi := norm_inv_le_quarter hsim ht
  have hi' : ‖(s - 1)⁻¹‖ ≤ 1 / 4 := norm_inv_le_quarter (s := s - 1) (by simp [hsim]) ht
  have hΓ := norm_logDeriv_Gammaℝ_le hσ (by linarith) ht
  have hΓ₀ := norm_logDeriv_Gammaℝ_le (σ := 3) (by norm_num) le_rfl ht
  have hC : digammaVerticalLogConstant ≤ 11 := by
    unfold digammaVerticalLogConstant
    have := Real.pi_lt_four
    have := Real.log_two_lt_d9
    linarith
  have hLt := log_ge_of_four_le ht
  -- assemble
  have hxi : logDeriv xi s = logDeriv riemannZeta s₀ + s₀⁻¹ + (s₀ - 1)⁻¹ + logDeriv Gammaℝ s₀
      + ∑' q : XiZeroCopy, ((s - (q.1 : ℂ))⁻¹ - (s₀ - (q.1 : ℂ))⁻¹) := by
    rw [← hpf, hdec₀]; ring
  rw [hdec, hxi]
  have hΓ' : ‖logDeriv Gammaℝ s‖ ≤ Real.log t + digammaVerticalLogConstant := by
    have : ((σ : ℂ) + t * I) = s := rfl
    simpa [this] using hΓ
  have hΓ₀' : ‖logDeriv Gammaℝ s₀‖ ≤ Real.log t + digammaVerticalLogConstant := by
    have : (((3 : ℝ) : ℂ) + t * I) = s₀ := by rw [hs₀def]; push_cast; rfl
    simpa [this] using hΓ₀
  have hLtδ : Real.log t ≤ Real.log t / δ := by
    rw [le_div_iff₀ hδ]
    exact mul_le_of_le_one_right (by linarith) hδ1
  have hK₀ : (0 : ℝ) ≤ smallHeightCount := Nat.cast_nonneg _
  have hK₀' : 0 ≤ 5 * (smallHeightCount : ℝ) * Real.log t / δ := by positivity
  have hfinal : logDerivZetaConstant * Real.log t / δ
      = (3650 + 5 * smallHeightCount) * Real.log t / δ + 50 * (Real.log t / δ) := by
    unfold logDerivZetaConstant; ring
  rw [hfinal]
  calc ‖logDeriv riemannZeta s₀ + s₀⁻¹ + (s₀ - 1)⁻¹ + logDeriv Gammaℝ s₀
        + ∑' q : XiZeroCopy, ((s - (q.1 : ℂ))⁻¹ - (s₀ - (q.1 : ℂ))⁻¹)
        - s⁻¹ - (s - 1)⁻¹ - logDeriv Gammaℝ s‖
      ≤ ‖logDeriv riemannZeta s₀‖ + ‖s₀⁻¹‖ + ‖(s₀ - 1)⁻¹‖ + ‖logDeriv Gammaℝ s₀‖
        + ‖∑' q : XiZeroCopy, ((s - (q.1 : ℂ))⁻¹ - (s₀ - (q.1 : ℂ))⁻¹)‖
        + ‖s⁻¹‖ + ‖(s - 1)⁻¹‖ + ‖logDeriv Gammaℝ s‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 2 + 1 / 4 + 1 / 4 + (Real.log t + digammaVerticalLogConstant)
        + (3650 + 5 * smallHeightCount) * Real.log t / δ
        + 1 / 4 + 1 / 4 + (Real.log t + digammaVerticalLogConstant) := by
        gcongr
    _ ≤ (3650 + 5 * smallHeightCount) * Real.log t / δ + 50 * (Real.log t / δ) := by
        linarith

end

end RHTower
