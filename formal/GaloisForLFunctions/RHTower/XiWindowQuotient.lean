import GaloisForLFunctions.RHTower.HodgeNyquistExclusion

/-!
# `ξ` divided by the divisor of a window of zeros

For a height `t₀ ≥ 8` let `V` be the zeros of `ξ` (with multiplicity) whose ordinate is within `2`
of `t₀`. Their number is `O(log t₀)` (`card_windowCopySet_le`), and removing them from the
partial-fraction expansion leaves a logarithmic derivative of size `O(log t₀)`
(`norm_logDeriv_xi_sub_window_le`):

`|ξ'/ξ(s) - Σ_{ρ ∈ V} (s - ρ)⁻¹| ≤ C log t₀`  for `½ ≤ Re s ≤ 2`, `|Im s - t₀| ≤ 1`.

No distance from `s` to the zeros enters. Hence `log|ξ/P_V|`, `P_V(s) = Π_{ρ∈V}(s - ρ)`, is
`C log t₀`-Lipschitz along every segment of that region that avoids the zeros of `ξ`
(`abs_log_windowQuotient_sub_le`). At the anchor `2 + iτ` it is at least
`-πτ/4 - 2 - |V| log 5` (`log_norm_windowQuotient_anchor_ge`).
-/

open Complex MeasureTheory Filter Topology Set GaloisForLFunctions
open scoped Real

namespace RHTower

noncomputable section

/-! ## The window of zeros around a height -/

/-- The multiplicity of a point of the divisor of `ξ`. -/
def divMult (ρ : XiDivisorSupport) : ℕ := Int.toNat (MeromorphicOn.divisor xi Set.univ (ρ : ℂ))

theorem one_le_divMult (ρ : XiDivisorSupport) : 1 ≤ divMult ρ := by
  have h0 := xi_divisor_nonneg Set.univ (ρ : ℂ)
  have hne : MeromorphicOn.divisor xi Set.univ (ρ : ℂ) ≠ 0 := ρ.2
  unfold divMult; omega

/-- The first copy of a divisor point. -/
def firstCopy (ρ : XiDivisorSupport) : XiZeroCopy := ⟨ρ, ⟨0, one_le_divMult ρ⟩⟩

theorem xi_divisorSupport_eq_zero (ρ : XiDivisorSupport) : xi (ρ : ℂ) = 0 :=
  xi_xiZeroCopy_eq_zero (firstCopy ρ)

theorem divisorSupport_re_pos (ρ : XiDivisorSupport) : 0 < (ρ : ℂ).re :=
  xiZeroCopy_re_pos (firstCopy ρ)

theorem divisorSupport_re_lt_one (ρ : XiDivisorSupport) : (ρ : ℂ).re < 1 :=
  xiZeroCopy_re_lt_one (firstCopy ρ)

/-- The divisor points with ordinate within `2` of `t₀`. -/
def windowSupport (t₀ : ℝ) : Set XiDivisorSupport := {ρ | |(ρ : ℂ).im - t₀| < 2}

theorem windowSupport_finite (t₀ : ℝ) : (windowSupport t₀).Finite := by
  have hZ : (xiZeroSet_weilLagFunctionCriterion ∩ Metric.closedBall ((t₀ : ℂ) * I) 3).Finite :=
    finite_xiZeroSet_inter (isCompact_closedBall _ _)
  refine (hZ.preimage Subtype.val_injective.injOn).subset fun ρ hρ => ?_
  have hρ' : |(ρ : ℂ).im - t₀| < 2 := hρ
  refine ⟨xi_divisorSupport_eq_zero ρ, ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h1 := divisorSupport_re_pos ρ
  have h2 := divisorSupport_re_lt_one ρ
  calc ‖(ρ : ℂ) - (t₀ : ℂ) * I‖ ≤ |((ρ : ℂ) - (t₀ : ℂ) * I).re| + |((ρ : ℂ) - (t₀ : ℂ) * I).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 + 2 := by
        gcongr
        · simp; rw [abs_le]; constructor <;> linarith
        · simp; linarith
    _ = 3 := by norm_num

/-- The window divisor points as a finset. -/
def windowSet (t₀ : ℝ) : Finset XiDivisorSupport := (windowSupport_finite t₀).toFinset

theorem mem_windowSet {t₀ : ℝ} {ρ : XiDivisorSupport} :
    ρ ∈ windowSet t₀ ↔ |(ρ : ℂ).im - t₀| < 2 := by
  unfold windowSet; rw [Set.Finite.mem_toFinset]; rfl

/-- All copies (with multiplicity) of the window zeros. -/
def windowCopySet (t₀ : ℝ) : Finset XiZeroCopy := (windowSet t₀).sigma fun _ => Finset.univ

theorem mem_windowCopySet {t₀ : ℝ} {q : XiZeroCopy} :
    q ∈ windowCopySet t₀ ↔ |(q.1 : ℂ).im - t₀| < 2 := by
  unfold windowCopySet
  rw [Finset.mem_sigma, mem_windowSet]
  simp

theorem prod_windowCopySet {M : Type*} [CommMonoid M] (t₀ : ℝ) (f : ℂ → M) :
    ∏ q ∈ windowCopySet t₀, f (q.1 : ℂ) = ∏ ρ ∈ windowSet t₀, f (ρ : ℂ) ^ divMult ρ := by
  unfold windowCopySet
  rw [Finset.prod_sigma]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

theorem sum_windowCopySet {M : Type*} [AddCommMonoid M] (t₀ : ℝ) (f : ℂ → M) :
    ∑ q ∈ windowCopySet t₀, f (q.1 : ℂ) = ∑ ρ ∈ windowSet t₀, divMult ρ • f (ρ : ℂ) := by
  unfold windowCopySet
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- The number of window copies is logarithmic in the height. -/
theorem card_windowCopySet_le {t₀ : ℝ} (ht : 4 ≤ t₀) :
    ((windowCopySet t₀).card : ℝ) ≤ 2 * (80 * Real.log (180 * (t₀ + 2)) + smallHeightCount) := by
  classical
  set V := windowCopySet t₀
  have hsplit : V.card = (V.filter (fun q => windowIndex t₀ q = 0)).card +
      (V.filter (fun q => ¬ windowIndex t₀ q = 0)).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have hwin : ∀ q ∈ V, windowIndex t₀ q < 2 := by
    intro q hq
    have h := mem_windowCopySet.mp hq
    unfold windowIndex
    rw [Nat.floor_lt (abs_nonneg _)]
    rw [abs_sub_comm]; push_cast; exact h
  have hlog : ∀ k : ℕ, k ≤ 1 → Real.log (180 * (t₀ + k + 1)) ≤ Real.log (180 * (t₀ + 2)) := by
    intro k hk
    have : (k : ℝ) ≤ 1 := by exact_mod_cast hk
    exact Real.log_le_log (by positivity) (by linarith)
  have h0 := card_zeroWindow_le ht 0 (V.filter (fun q => windowIndex t₀ q = 0)) fun q hq => by
    have := (Finset.mem_filter.mp hq).2
    exact (Nat.floor_eq_iff (abs_nonneg _)).mp this
  have h1 := card_zeroWindow_le ht 1 (V.filter (fun q => ¬ windowIndex t₀ q = 0)) fun q hq => by
    obtain ⟨hqV, hq0⟩ := Finset.mem_filter.mp hq
    have hlt := hwin q hqV
    have h1' : windowIndex t₀ q = 1 := by omega
    exact (Nat.floor_eq_iff (abs_nonneg _)).mp h1'
  have e0 := hlog 0 (by norm_num)
  have e1 := hlog 1 le_rfl
  push_cast at h0 h1 e0 e1
  have : (V.card : ℝ) = (V.filter (fun q => windowIndex t₀ q = 0)).card +
      (V.filter (fun q => ¬ windowIndex t₀ q = 0)).card := by rw [hsplit]; push_cast; ring
  linarith

/-! ## The logarithmic derivative with the window zeros removed -/

/-- `sum_norm_partialFractionDiff_le` with the distance hypothesis only on the summed copies. -/
theorem sum_norm_partialFractionDiff_le_of_mem {σ t δ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2)
    (ht : 4 ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (F : Finset XiZeroCopy)
    (hall : ∀ q ∈ F, δ ≤ ‖(σ + t * I : ℂ) - (q.1 : ℂ)‖) :
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
        Finset.sum_le_sum fun q hq => norm_term_le_windowWeight hσ hσ2 hδ q (hall q hq)
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

/-- The constant of the window-removed logarithmic derivative. -/
def windowLogConst : ℝ := 7700 + 11 * smallHeightCount

theorem windowLogConst_nonneg : 0 ≤ windowLogConst := by unfold windowLogConst; positivity

/-- **The logarithmic derivative of `ξ` with the window zeros removed.** For `t₀ ≥ 8`,
`½ ≤ Re s ≤ 2`, `|Im s - t₀| ≤ 1` and `ξ(s) ≠ 0`,
`|ξ'/ξ(s) - Σ_{window copies} (s-ρ)⁻¹| ≤ C log t₀`. -/
theorem norm_logDeriv_xi_sub_window_le {s : ℂ} {t₀ : ℝ} (ht₀ : 8 ≤ t₀) (hσ : 1 / 2 ≤ s.re)
    (hσ2 : s.re ≤ 2) (hs : |s.im - t₀| ≤ 1) (hxi : xi s ≠ 0) :
    ‖logDeriv xi s - ∑ q ∈ windowCopySet t₀, (s - (q.1 : ℂ))⁻¹‖ ≤
      windowLogConst * Real.log t₀ := by
  classical
  set τ := s.im with hτ
  have hτ4 : 4 ≤ τ := by linarith [(abs_le.mp hs).1]
  have hτle : τ ≤ t₀ + 1 := by linarith [(abs_le.mp hs).2]
  set σ := s.re with hσdef
  have hsdef : s = (σ : ℂ) + τ * I := by simp [hσdef, hτ]
  set s₀ : ℂ := 3 + τ * I with hs₀def
  have hs₀re : s₀.re = 3 := by simp [hs₀def]
  have hs₀im : s₀.im = τ := by simp [hs₀def]
  have hs₀1 : s₀ ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hs₀im, Complex.one_im] at this; linarith
  have hs₀0 : s₀ ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hs₀im, Complex.zero_im] at this; linarith
  have hxis₀ : xi s₀ ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h
    have := xiZeroCopy_re_lt_one q
    rw [hq, hs₀re] at this
    linarith
  have hζs₀ : riemannZeta s₀ ≠ 0 := by
    intro h
    apply hxis₀
    rw [xi_eq_xiUnit_mul_zeta hs₀0 hs₀1 (by rw [hs₀re]; norm_num), h, mul_zero]
  have hdec₀ := logDeriv_zeta_eq_logDeriv_xi (s := s₀) (by rw [hs₀re]; norm_num) hs₀1 hζs₀
  have hpf := logDeriv_xi_sub_eq_tsum hxi hxis₀
  set d : XiZeroCopy → ℂ := fun q => (s - (q.1 : ℂ))⁻¹ - (s₀ - (q.1 : ℂ))⁻¹ with hd
  have hsum : Summable d := summable_partialFractionDiff hxi hxis₀
  set V := windowCopySet t₀
  have hsplit := hsum.sum_add_tsum_compl (s := V)
  -- the far part
  have hfar : ∀ q : XiZeroCopy, q ∉ V → 1 ≤ ‖s - (q.1 : ℂ)‖ := by
    intro q hq
    have h1 : 2 ≤ |(q.1 : ℂ).im - t₀| := by
      by_contra hc; push Not at hc; exact hq (mem_windowCopySet.mpr hc)
    have h2 := abs_im_le_norm_sub (s := s) (t := τ) rfl q
    have h3 : |(q.1 : ℂ).im - t₀| ≤ |τ - (q.1 : ℂ).im| + |τ - t₀| := by
      calc |(q.1 : ℂ).im - t₀| = |(τ - t₀) - (τ - (q.1 : ℂ).im)| := by ring_nf
        _ ≤ |τ - t₀| + |τ - (q.1 : ℂ).im| := abs_sub _ _
        _ = _ := by ring
    linarith
  have hfarsum : ‖∑' x : ↑((V : Set XiZeroCopy)ᶜ), d x‖ ≤
      (3650 + 5 * smallHeightCount) * Real.log τ := by
    have hs' : Summable (fun x : ↑((V : Set XiZeroCopy)ᶜ) => ‖d x‖) :=
      (summable_norm_iff.mpr hsum).subtype _
    refine (norm_tsum_le_tsum_norm hs').trans ?_
    refine hs'.tsum_le_of_sum_le fun F => ?_
    have hF := sum_norm_partialFractionDiff_le_of_mem (σ := σ) (t := τ) (δ := 1) hσ hσ2 hτ4
      one_pos le_rfl (F.map (Function.Embedding.subtype _)) (by
        intro q hq
        obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hq
        rw [← hsdef]
        exact hfar x x.2)
    rw [Finset.sum_map] at hF
    simp only [Function.Embedding.coe_subtype] at hF
    rw [div_one] at hF
    refine le_trans (le_of_eq ?_) hF
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hd, hsdef, hs₀def]
  -- the near part
  have hnear : ‖∑ q ∈ V, (s₀ - (q.1 : ℂ))⁻¹‖ ≤ (V.card : ℝ) / 2 := by
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ q ∈ V, ‖(s₀ - (q.1 : ℂ))⁻¹‖ ≤ 1 / 2 := by
      intro q _
      have h2 : 2 ≤ ‖s₀ - (q.1 : ℂ)‖ := by rw [hs₀def]; exact two_le_norm_anchor_sub τ q
      rw [norm_inv, one_div]
      exact inv_anti₀ (by norm_num) h2
    calc ∑ q ∈ V, ‖(s₀ - (q.1 : ℂ))⁻¹‖ ≤ ∑ q ∈ V, (1 / 2 : ℝ) := Finset.sum_le_sum hb
      _ = (V.card : ℝ) / 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- the anchor terms
  have hz₀ := norm_logDeriv_zeta_three_le τ
  have hi₀ := norm_inv_le_quarter hs₀im hτ4
  have hi₀' : ‖(s₀ - 1)⁻¹‖ ≤ 1 / 4 := norm_inv_le_quarter (s := s₀ - 1) (by simp [hs₀im]) hτ4
  have hΓ₀ := norm_logDeriv_Gammaℝ_le (σ := 3) (by norm_num) le_rfl hτ4
  have hC : digammaVerticalLogConstant ≤ 11 := by
    unfold digammaVerticalLogConstant
    have := Real.pi_lt_four
    have := Real.log_two_lt_d9
    linarith
  have hΓ₀' : ‖logDeriv Gammaℝ s₀‖ ≤ Real.log τ + digammaVerticalLogConstant := by
    have : (((3 : ℝ) : ℂ) + τ * I) = s₀ := by rw [hs₀def]; push_cast; rfl
    simpa [this] using hΓ₀
  -- assemble
  have hid : logDeriv xi s - ∑ q ∈ V, (s - (q.1 : ℂ))⁻¹ =
      (logDeriv riemannZeta s₀ + s₀⁻¹ + (s₀ - 1)⁻¹ + logDeriv Gammaℝ s₀)
        - ∑ q ∈ V, (s₀ - (q.1 : ℂ))⁻¹ + ∑' x : ↑((V : Set XiZeroCopy)ᶜ), d x := by
    have e1 : logDeriv xi s = logDeriv xi s₀ + ∑' q, d q := by rw [← hpf]; ring
    have e2 : ∑ q ∈ V, d q = ∑ q ∈ V, (s - (q.1 : ℂ))⁻¹ - ∑ q ∈ V, (s₀ - (q.1 : ℂ))⁻¹ := by
      rw [← Finset.sum_sub_distrib]
    rw [e1, ← hsplit, e2, hdec₀]; ring
  rw [hid]
  have hcard := card_windowCopySet_le (t₀ := t₀) (by linarith)
  have hK₀ : (0 : ℝ) ≤ smallHeightCount := Nat.cast_nonneg _
  have hL8 : 2 ≤ Real.log t₀ := by
    have h := Real.add_one_le_exp (2 : ℝ)
    have h8 : Real.exp 2 ≤ 8 := by
      have := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e]; nlinarith [Real.exp_pos 1]
    rw [← Real.exp_le_exp, Real.exp_log (by linarith)]; linarith
  have hτlog : Real.log τ ≤ 2 * Real.log t₀ := by
    have : Real.log τ ≤ Real.log (2 * t₀) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    have := Real.log_two_lt_d9
    linarith
  have hlog180 : Real.log (180 * (t₀ + 2)) ≤ 4 * Real.log t₀ := by
    have h1 : Real.log (180 * (t₀ + 2)) ≤ Real.log (360 * t₀) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num : (360 : ℝ) ≠ 0) (by linarith : t₀ ≠ 0)] at h1
    have h2 : Real.log 360 ≤ 6 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have e : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) this.le 6]
    linarith
  have hlogτ0 : 0 ≤ Real.log τ := Real.log_nonneg (by linarith)
  calc ‖(logDeriv riemannZeta s₀ + s₀⁻¹ + (s₀ - 1)⁻¹ + logDeriv Gammaℝ s₀)
        - ∑ q ∈ V, (s₀ - (q.1 : ℂ))⁻¹ + ∑' x : ↑((V : Set XiZeroCopy)ᶜ), d x‖
      ≤ (‖logDeriv riemannZeta s₀‖ + ‖s₀⁻¹‖ + ‖(s₀ - 1)⁻¹‖ + ‖logDeriv Gammaℝ s₀‖)
          + ‖∑ q ∈ V, (s₀ - (q.1 : ℂ))⁻¹‖ + ‖∑' x : ↑((V : Set XiZeroCopy)ᶜ), d x‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ((norm_sub_le _ _).trans
          (add_le_add_left ?_ _)) _)
        exact (norm_add_le _ _).trans (add_le_add_left ((norm_add_le _ _).trans
          (add_le_add_left (norm_add_le _ _) _)) _) |>.trans (le_of_eq (by ring))
    _ ≤ (2 + 1 / 4 + 1 / 4 + (Real.log τ + 11)) + (V.card : ℝ) / 2 +
          (3650 + 5 * smallHeightCount) * Real.log τ := by
        gcongr; linarith
    _ ≤ windowLogConst * Real.log t₀ := by
        unfold windowLogConst
        nlinarith

/-! ## `ξ` divided by the window divisor -/

/-- The window divisor `Π (s - ρ)` over the window copies. -/
def windowPoly (t₀ : ℝ) (s : ℂ) : ℂ := ∏ q ∈ windowCopySet t₀, (s - (q.1 : ℂ))

/-- `ξ` with the window zeros divided out. -/
def windowQuotient (t₀ : ℝ) (s : ℂ) : ℂ := xi s / windowPoly t₀ s

theorem windowPoly_ne_zero {t₀ : ℝ} {s : ℂ} (hxi : xi s ≠ 0) : windowPoly t₀ s ≠ 0 := by
  unfold windowPoly
  rw [Finset.prod_ne_zero_iff]
  intro q _ h
  apply hxi
  rw [sub_eq_zero.mp h]
  exact xi_xiZeroCopy_eq_zero q

theorem differentiable_windowPoly (t₀ : ℝ) : Differentiable ℂ (windowPoly t₀) := by
  unfold windowPoly
  exact Differentiable.fun_finsetProd fun q _ => differentiable_id.sub_const _

theorem logDeriv_windowQuotient {t₀ : ℝ} {s : ℂ} (hxi : xi s ≠ 0) :
    logDeriv (windowQuotient t₀) s = logDeriv xi s - ∑ q ∈ windowCopySet t₀, (s - (q.1 : ℂ))⁻¹ := by
  have hP := windowPoly_ne_zero (t₀ := t₀) hxi
  have h := logDeriv_div (f := xi) (g := windowPoly t₀) s hxi hP
    (xi_differentiable s) ((differentiable_windowPoly t₀) s)
  have e : (fun z => xi z / windowPoly t₀ z) = windowQuotient t₀ := rfl
  rw [e] at h
  rw [h]
  congr 1
  have hne : ∀ q ∈ windowCopySet t₀, (fun z : ℂ => z - (q.1 : ℂ)) s ≠ 0 := by
    intro q _ h0
    apply hxi
    rw [sub_eq_zero.mp h0]
    exact xi_xiZeroCopy_eq_zero q
  have hp := logDeriv_prod (s := windowCopySet t₀) (f := fun q (z : ℂ) => z - (q.1 : ℂ)) (x := s)
    hne (fun q _ => (differentiable_id.sub_const _).differentiableAt)
  have e2 : (∏ q ∈ windowCopySet t₀, (fun q (z : ℂ) => z - (q.1 : ℂ)) q ·) = windowPoly t₀ := rfl
  rw [e2] at hp
  rw [hp]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [logDeriv_apply]
  simp

/-- **Lipschitz continuity of `log|ξ/P|`.** Along a segment in `½ ≤ Re s ≤ 2`,
`|Im s - t₀| ≤ 1` avoiding the zeros of `ξ`, `log|ξ/P|` varies by at most
`C log t₀` times the length. -/
theorem abs_log_windowQuotient_sub_le {t₀ : ℝ} (ht₀ : 8 ≤ t₀) {a b : ℂ}
    (hseg : ∀ z ∈ segment ℝ a b, 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im - t₀| ≤ 1 ∧ xi z ≠ 0) :
    |Real.log ‖windowQuotient t₀ b‖ - Real.log ‖windowQuotient t₀ a‖| ≤
      windowLogConst * Real.log t₀ * ‖b - a‖ := by
  refine abs_log_norm_sub_le (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨-, -, -, hxi⟩ := hseg z hz
    exact (xi_differentiable z).div ((differentiable_windowPoly t₀) z) (windowPoly_ne_zero hxi)
  · obtain ⟨-, -, -, hxi⟩ := hseg z hz
    exact div_ne_zero hxi (windowPoly_ne_zero hxi)
  · obtain ⟨h1, h2, h3, hxi⟩ := hseg z hz
    rw [← logDeriv_apply, logDeriv_windowQuotient hxi]
    exact norm_logDeriv_xi_sub_window_le ht₀ h1 h2 h3 hxi

/-- **The anchor value.** At `2 + iτ` with `|τ - t₀| ≤ 1`,
`log|ξ/P| ≥ -πτ/4 - 2 - N log 5`, `N` the number of window copies. -/
theorem log_norm_windowQuotient_anchor_ge {t₀ τ : ℝ} (ht₀ : 8 ≤ t₀) (hτ : |τ - t₀| ≤ 1) :
    -(π * τ / 4) - 2 - (windowCopySet t₀).card * Real.log 5 ≤
      Real.log ‖windowQuotient t₀ (2 + τ * I)‖ := by
  set z : ℂ := 2 + τ * I with hz
  have hτ7 : 7 ≤ τ := by linarith [(abs_le.mp hτ).1]
  have hzre : z.re = 2 := by simp [hz]
  have hzim : z.im = τ := by simp [hz]
  have hz0 : z ≠ 0 := fun h => by have := congrArg Complex.re h; rw [hzre] at this; simp at this
  have hz1 : z ≠ 1 := fun h => by have := congrArg Complex.re h; rw [hzre] at this; simp at this
  have hxi : xi z = xiUnit z * riemannZeta z := xi_eq_xiUnit_mul_zeta hz0 hz1 (by rw [hzre]; norm_num)
  have hζ : 1 / 3 ≤ ‖riemannZeta z‖ := norm_riemannZeta_ge_third (by rw [hzre])
  -- the unit
  have hpoly : τ ^ 2 / 2 ≤ ‖z * (z - 1) / 2‖ := by
    rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
    have h1 : |τ| ≤ ‖z‖ := by rw [← hzim]; exact Complex.abs_im_le_norm z
    have h2 : |τ| ≤ ‖z - 1‖ := by
      have := Complex.abs_im_le_norm (z - 1); simpa [hzim] using this
    have : τ ^ 2 = |τ| * |τ| := by rw [← sq_abs]; ring
    rw [this]
    gcongr
  have hpi : ‖(π : ℂ) ^ (-z / 2)‖ = π⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have : (-z / 2).re = -1 := by simp [hzre]
    rw [this, Real.rpow_neg_one]
  have hhalf : z / 2 = 1 + I * ((τ / 2 : ℝ) : ℂ) := by rw [hz]; push_cast; ring
  have hG2 := norm_Gamma_one_add_I_mul_sq (y := τ / 2) (by linarith)
  rw [← hhalf] at hG2
  have hsinh : Real.sinh (π * (τ / 2)) ≤ Real.exp (π * (τ / 2)) / 2 := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (-(π * (τ / 2)))
    linarith
  have hsinh0 : 0 < Real.sinh (π * (τ / 2)) := Real.sinh_pos_iff.mpr (by positivity)
  have hGsq : Real.exp (-(π * (τ / 2))) ≤ ‖Complex.Gamma (z / 2)‖ ^ 2 := by
    rw [hG2, le_div_iff₀ hsinh0]
    calc Real.exp (-(π * (τ / 2))) * Real.sinh (π * (τ / 2))
        ≤ Real.exp (-(π * (τ / 2))) * (Real.exp (π * (τ / 2)) / 2) := by gcongr
      _ = 1 / 2 := by rw [mul_div_assoc', ← Real.exp_add]; simp
      _ ≤ π * (τ / 2) := by nlinarith [Real.pi_gt_three]
  have hG : Real.exp (-(π * τ / 4)) ≤ ‖Complex.Gamma (z / 2)‖ := by
    have e : Real.exp (-(π * (τ / 2))) = Real.exp (-(π * τ / 4)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e] at hGsq
    exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (norm_nonneg _) two_ne_zero).mp hGsq
  have hunit : ‖xiUnit z‖ = ‖z * (z - 1) / 2‖ * ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖ := by
    unfold xiUnit; rw [Complex.Gammaℝ_def, norm_mul, norm_mul, mul_assoc]
  have hU : Real.exp (-(π * τ / 4)) ≤ ‖xiUnit z‖ := by
    rw [hunit, hpi]
    have h1 : 1 ≤ τ ^ 2 / 2 * π⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_four]
    calc Real.exp (-(π * τ / 4)) = 1 * Real.exp (-(π * τ / 4)) := (one_mul _).symm
      _ ≤ (τ ^ 2 / 2 * π⁻¹) * ‖Complex.Gamma (z / 2)‖ := by gcongr
      _ ≤ ‖z * (z - 1) / 2‖ * π⁻¹ * ‖Complex.Gamma (z / 2)‖ := by gcongr
  -- the window divisor
  have hP : ‖windowPoly t₀ z‖ ≤ 5 ^ (windowCopySet t₀).card := by
    unfold windowPoly
    rw [norm_prod]
    have hb : ∀ q ∈ windowCopySet t₀, ‖z - (q.1 : ℂ)‖ ≤ 5 := by
      intro q hq
      have hw := mem_windowCopySet.mp hq
      have hre0 := xiZeroCopy_re_pos q
      have hre1 := xiZeroCopy_re_lt_one q
      calc ‖z - (q.1 : ℂ)‖ ≤ |(z - (q.1 : ℂ)).re| + |(z - (q.1 : ℂ)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 2 + 3 := by
            gcongr
            · simp only [Complex.sub_re, hzre]; rw [abs_le]; constructor <;> linarith
            · simp only [Complex.sub_im, hzim]
              calc |τ - (q.1 : ℂ).im| = |(τ - t₀) - ((q.1 : ℂ).im - t₀)| := by ring_nf
                _ ≤ |τ - t₀| + |(q.1 : ℂ).im - t₀| := abs_sub _ _
                _ ≤ 1 + 2 := by linarith
                _ = 3 := by norm_num
        _ = 5 := by norm_num
    calc ∏ q ∈ windowCopySet t₀, ‖z - (q.1 : ℂ)‖ ≤ ∏ q ∈ windowCopySet t₀, (5 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) hb
      _ = 5 ^ (windowCopySet t₀).card := Finset.prod_const _
  have hxi0 : xi z ≠ 0 := by
    rw [hxi]
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · rw [h, norm_zero] at hU; linarith [Real.exp_pos (-(π * τ / 4))]
    · rw [h, norm_zero] at hζ; linarith
  have hP0 : 0 < ‖windowPoly t₀ z‖ := norm_pos_iff.mpr (windowPoly_ne_zero hxi0)
  have hU0 : 0 < ‖xiUnit z‖ := lt_of_lt_of_le (Real.exp_pos _) hU
  have hζ0 : 0 < ‖riemannZeta z‖ := by linarith
  unfold windowQuotient
  rw [norm_div, hxi, norm_mul, Real.log_div (mul_pos hU0 hζ0).ne' hP0.ne',
    Real.log_mul hU0.ne' hζ0.ne']
  have l1 : -(π * τ / 4) ≤ Real.log ‖xiUnit z‖ := by
    rw [← Real.log_exp (-(π * τ / 4))]; exact Real.log_le_log (Real.exp_pos _) hU
  have l2 : -2 ≤ Real.log ‖riemannZeta z‖ := by
    have : Real.log (1 / 3) ≤ Real.log ‖riemannZeta z‖ := Real.log_le_log (by norm_num) hζ
    have h3 : Real.log (1 / 3) = -Real.log 3 := by rw [one_div, Real.log_inv]
    have : Real.log 3 < 2 := by
      have := Real.log_two_lt_d9
      have h : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    linarith
  have l3 : Real.log ‖windowPoly t₀ z‖ ≤ (windowCopySet t₀).card * Real.log 5 := by
    rw [← Real.log_pow]; exact Real.log_le_log hP0 hP
  linarith

end

end RHTower
