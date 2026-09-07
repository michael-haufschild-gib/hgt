import GaloisForLFunctions.RHTower.WeightedScrewLandauEngineThreshold
import GaloisForLFunctions.RHTower.WeightedScrewPoleContradiction

/-!
# The pole contradiction with an exponential slack

If the weighted screw divisor `Φ_W` is real and satisfies `Φ_W(t) ≥ −C₀ e^{εt}` on the source half-line
with `0 ≤ ε < 1/2`, then no zero copy has `Im γ_q < −ε`, hence, by the functional-equation reflection,
every copy satisfies `|Im γ_q| ≤ ε`.

Proof.  By the threshold engine the Laplace transform `F` of the shifted divisor is analytic on
`Re s > ε`.  The continuation `G(s) = Σ'_q W_q/(s(s² + γ_q²)) + C₀/(s − ε)` is analytic on the
half-plane `Re s > ε` minus the countable pole set `{±iγ_q}`, which is connected, and `F = G` there.
A copy `q₀` with `Im γ_{q₀} < −ε` gives the pole `s₀ = iγ_{q₀}` with `Re s₀ > ε`; along
`s_n = s₀ + ρ/(n+2)` the products `(s_n − s₀) G(s_n)` tend to `(Σ_{γ_q = ±γ_{q₀}} W_q)/(2s₀²) ≠ 0`,
whereas `(s_n − s₀) F(s_n) → 0`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

variable (W : XiZeroCopy → ℂ) (C₀ ε : ℝ)

/-! ## The punctured half-plane above the threshold -/

/-- The half-plane `Re s > ε` with the poles removed. -/
def thrPunctured : Set ℂ := {s : ℂ | ε < s.re} \ spectralPoleSet

/-- The chart `u ↦ ε + e^{Re u} + i Im u` onto `Re s > ε`. -/
def thrChart (u : ℂ) : ℂ := (ε : ℂ) + rightHalfPlaneChart u

theorem continuous_thrChart : Continuous (thrChart ε) :=
  continuous_const.add continuous_rightHalfPlaneChart

theorem thrChart_injective : Function.Injective (thrChart ε) := by
  intro u v huv
  exact halfPlaneChart_injective (add_left_cancel huv)

theorem thrChart_re (u : ℂ) : (thrChart ε u).re = ε + Real.exp u.re := by
  simp [thrChart]

theorem exists_thrChart_eq {s : ℂ} (hs : ε < s.re) : ∃ u, thrChart ε u = s := by
  obtain ⟨u, hu⟩ := exists_halfPlaneChart_eq (s := s - (ε : ℂ)) (by simp; linarith)
  exact ⟨u, by unfold thrChart; rw [hu]; ring⟩

/-- **The punctured half-plane above the threshold is connected.** -/
theorem isPreconnected_thrPunctured : IsPreconnected (thrPunctured ε) := by
  have hT : IsConnected (thrChart ε ⁻¹' spectralPoleSet)ᶜ :=
    Set.Countable.isConnected_compl_of_one_lt_rank one_lt_rank_real_complex
      (countable_spectralPoleSet.preimage_of_injOn (thrChart_injective ε).injOn)
  have himg : thrChart ε '' (thrChart ε ⁻¹' spectralPoleSet)ᶜ = thrPunctured ε := by
    ext s
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, hu⟩
      show ε < (thrChart ε u).re
      rw [thrChart_re]
      linarith [Real.exp_pos u.re]
    · rintro ⟨hre, hP⟩
      obtain ⟨u, rfl⟩ := exists_thrChart_eq ε hre
      exact ⟨u, hP, rfl⟩
  rw [← himg]
  exact (hT.image _ (continuous_thrChart ε).continuousOn).isPreconnected

theorem one_mem_thrPunctured (hε : ε < 1) : (1 : ℂ) ∈ thrPunctured ε :=
  ⟨by simp; exact hε, one_notMem_spectralPoleSet⟩

theorem analyticOnNhd_thrContinuation_punctured {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hε0 : 0 ≤ ε) :
    AnalyticOnNhd ℂ (thrContinuation W C₀ ε) (thrPunctured ε) := by
  intro s₁ hs₁
  have hs₁re : ε < s₁.re := hs₁.1
  have hre : 0 < s₁.re := by linarith
  have h1 := analyticAt_weightedScrewContinuationExcept W hC hW ∅ hre (fun q _ =>
    ⟨fun h => hs₁.2 (Or.inl ⟨q, h⟩), fun h => hs₁.2 (Or.inr ⟨q, h⟩)⟩)
  rw [weightedScrewContinuationExcept_empty] at h1
  have h2 : AnalyticAt ℂ (fun s : ℂ => (C₀ : ℂ) / (s - (ε : ℂ))) s₁ := by
    refine analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hs₁re
    simp at hs₁re
  exact h1.add h2

/-- **Identity theorem on the punctured half-plane above the threshold.** -/
theorem thrLaplace_eqOn_punctured {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    EqOn (thrLaplace W C₀ ε) (thrContinuation W C₀ ε) (thrPunctured ε) := by
  have hF := analyticOnNhd_thrLaplace_gt_eps W C₀ ε hC hW hlow hreal hε0 hε
  have hF' : AnalyticOnNhd ℂ (thrLaplace W C₀ ε) (thrPunctured ε) := fun s hs => hF s hs.1
  have hG := analyticOnNhd_thrContinuation_punctured W C₀ ε hC hW hε0
  have hone : (1 : ℂ) ∈ thrPunctured ε := one_mem_thrPunctured ε (by linarith)
  have hev : thrLaplace W C₀ ε =ᶠ[𝓝 (1 : ℂ)] thrContinuation W C₀ ε := by
    have hopen : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with s hs
    exact thrLaplace_eq_continuation W C₀ ε hC hW hε hs
  exact hF'.eqOn_of_preconnected_of_eventuallyEq hG (isPreconnected_thrPunctured ε) hone hev

/-! ## The pole contradiction -/

/-- **No copy below the threshold.**  Under the exponential lower bound, every copy satisfies
`Im γ_q ≥ −ε`. -/
theorem neg_le_im_of_thr {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hWpt : ∀ q q' : XiZeroCopy, xiSpectralPoint q' = xiSpectralPoint q → W q' = W q)
    (hWeven : ∀ q q' : XiZeroCopy, xiSpectralPoint q' = -xiSpectralPoint q → W q' = W q)
    (hWne : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → W q ≠ 0)
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (q₀ : XiZeroCopy) : -ε ≤ (xiSpectralPoint q₀).im := by
  by_contra hq₀'
  push Not at hq₀'
  have hq₀ : (xiSpectralPoint q₀).im < -ε := hq₀'
  set γ₀ : ℂ := xiSpectralPoint q₀ with hγ₀
  set s₀ : ℂ := I * γ₀ with hs₀
  have hre0 : ε < s₀.re := by
    rw [hs₀, mul_re, I_re, I_im]
    simp only [zero_mul, one_mul, zero_sub]
    linarith
  have hre0' : 0 < s₀.re := by linarith
  have hs₀ne : s₀ ≠ 0 := by
    intro h
    rw [h, zero_re] at hre0'
    exact lt_irrefl _ hre0'
  have hs₀ε : s₀ - (ε : ℂ) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have := congrArg Complex.re h
    rw [ofReal_re] at this
    linarith
  -- the exceptional copies `γ_q = ±γ₀`
  set E : Finset XiZeroCopy := (finite_xiZeroCopy_norm_le ‖γ₀‖).toFinset.filter
    (fun q => xiSpectralPoint q = γ₀ ∨ xiSpectralPoint q = -γ₀) with hE
  have hEmem : ∀ q, q ∈ E ↔ (xiSpectralPoint q = γ₀ ∨ xiSpectralPoint q = -γ₀) := by
    intro q
    rw [hE, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      show ‖xiSpectralPoint q‖ ≤ ‖γ₀‖
      rcases h with h | h
      · rw [h]
      · rw [h, norm_neg]
  have hq₀E : q₀ ∈ E := (hEmem q₀).mpr (Or.inl rfl)
  have hnot : ∀ q, q ∉ E → I * xiSpectralPoint q ≠ s₀ ∧ -(I * xiSpectralPoint q) ≠ s₀ := by
    intro q hq
    constructor
    · intro h
      apply hq
      rw [hEmem]
      left
      exact mul_left_cancel₀ I_ne_zero h
    · intro h
      apply hq
      rw [hEmem]
      right
      have h' : I * xiSpectralPoint q = I * -γ₀ := by
        rw [hs₀] at h
        linear_combination (-1 : ℂ) * h
      exact mul_left_cancel₀ I_ne_zero h'
  have hWE : ∀ q ∈ E, W q = W q₀ := by
    intro q hq
    rcases (hEmem q).mp hq with h | h
    · exact hWpt q₀ q h
    · exact hWeven q₀ q h
  -- analytic data
  have hF := analyticOnNhd_thrLaplace_gt_eps W C₀ ε hC hW hlow hreal hε0 hε
  have hEq := thrLaplace_eqOn_punctured W C₀ ε hC hW hlow hreal hε0 hε
  have hrest := analyticAt_weightedScrewContinuationExcept W hC hW E hre0' hnot
  obtain ⟨ρ, hρ, u, hu, hu0, hball_re, hball_ne, hball_le⟩ :=
    exists_uniform_atom_bound W hC hW E hre0' hnot
  -- the approaching sequence `s_n = s₀ + ρ/(n+2)`
  let c : ℕ → ℝ := fun n => ρ / ((n : ℝ) + 2)
  let sn : ℕ → ℂ := fun n => s₀ + (c n : ℂ)
  have hc_pos : ∀ n, 0 < c n := fun n => by dsimp only [c]; positivity
  have hc_le : ∀ n, c n ≤ ρ / 2 := fun n => by
    dsimp only [c]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hc_tend : Tendsto c atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h2 := h1.inv_tendsto_atTop.const_mul ρ
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    dsimp only [c]
    rw [div_eq_mul_inv]
    rfl
  have hcC_tend : Tendsto (fun n => (c n : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp hc_tend
    rw [Complex.ofReal_zero] at this
    exact this
  have hsn_ball : ∀ n, sn n ∈ Metric.closedBall s₀ ρ := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp only [sn]
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc_pos n)]
    linarith [hc_le n]
  have hsn_ne_s₀ : ∀ n, sn n ≠ s₀ := by
    intro n h
    dsimp only [sn] at h
    have : (c n : ℂ) = 0 := by linear_combination h
    exact (hc_pos n).ne' (by exact_mod_cast this)
  have hsn_re : ∀ n, 0 < (sn n).re := fun n => hball_re _ (hsn_ball n)
  have hsn_re_eps : ∀ n, ε < (sn n).re := by
    intro n
    dsimp only [sn]
    rw [add_re, ofReal_re]
    linarith [hc_pos n]
  have hsn_mem : ∀ n, sn n ∈ thrPunctured ε := by
    intro n
    refine ⟨hsn_re_eps n, ?_⟩
    rintro (⟨q, hq⟩ | ⟨q, hq⟩)
    · change I * xiSpectralPoint q = sn n at hq
      by_cases hqE : q ∈ E
      · rcases (hEmem q).mp hqE with h | h
        · rw [h] at hq
          exact hsn_ne_s₀ n hq.symm
        · rw [h] at hq
          have := hsn_re n
          rw [← hq, mul_neg, neg_re] at this
          linarith
      · exact (hball_ne q hqE _ (hsn_ball n)).1 (by rw [hq]; ring)
    · change -(I * xiSpectralPoint q) = sn n at hq
      by_cases hqE : q ∈ E
      · rcases (hEmem q).mp hqE with h | h
        · rw [h] at hq
          have := hsn_re n
          rw [← hq, neg_re] at this
          linarith
        · rw [h] at hq
          apply hsn_ne_s₀ n
          rw [← hq]
          ring
      · exact (hball_ne q hqE _ (hsn_ball n)).2 (by rw [← hq]; ring)
  have hsn_tend : Tendsto sn atTop (𝓝 s₀) := by
    have := hcC_tend.const_add s₀
    simpa using this
  -- summability of the full series at `s_n`
  have hsum : ∀ n, Summable fun q : XiZeroCopy =>
      W q * suzukiPsiLaplaceAtom (sn n) (xiSpectralPoint q) := by
    intro n
    have hfin : Summable fun q : XiZeroCopy =>
        if q ∈ E then ‖W q * suzukiPsiLaplaceAtom (sn n) (xiSpectralPoint q)‖ else 0 :=
      summable_of_ne_finset_zero (s := E) fun q hq => by simp [hq]
    refine Summable.of_norm_bounded (g := fun q => u q +
      (if q ∈ E then ‖W q * suzukiPsiLaplaceAtom (sn n) (xiSpectralPoint q)‖ else 0))
      (hu.add hfin) fun q => ?_
    by_cases hq : q ∈ E
    · simp only [hq, if_true]
      linarith [hu0 q]
    · simp only [hq, if_false, add_zero]
      exact hball_le q hq _ (hsn_ball n)
  -- the finite part along the sequence
  have hatomE : ∀ n, ∀ q ∈ E,
      (c n : ℂ) * suzukiPsiLaplaceAtom (sn n) (xiSpectralPoint q) = 1 / (sn n * (sn n + s₀)) := by
    intro n q hq
    have hsq : xiSpectralPoint q ^ 2 = γ₀ ^ 2 := by
      rcases (hEmem q).mp hq with h | h
      · rw [h]
      · rw [h, neg_sq]
    unfold suzukiPsiLaplaceAtom
    rw [hsq]
    have hs₀sq : s₀ ^ 2 = -γ₀ ^ 2 := by rw [hs₀, mul_pow, I_sq]; ring
    have hfac : sn n ^ 2 + γ₀ ^ 2 = (c n : ℂ) * (sn n + s₀) := by
      have : (sn n : ℂ) - s₀ = (c n : ℂ) := by dsimp only [sn]; ring
      rw [← this, ← sub_neg_eq_add (sn n ^ 2), ← hs₀sq]
      ring
    rw [hfac]
    have hc0 : (c n : ℂ) ≠ 0 := by exact_mod_cast (hc_pos n).ne'
    have hsn0 : sn n ≠ 0 := by
      intro h
      have := hsn_re n
      rw [h, zero_re] at this
      exact lt_irrefl _ this
    have hsum0 : sn n + s₀ ≠ 0 := by
      intro h
      have h1 := hsn_re n
      have h2 := congrArg Complex.re h
      rw [add_re, zero_re] at h2
      linarith
    field_simp
  -- limit of `c_n · G(s_n)`
  have hlimG : Tendsto (fun n => (c n : ℂ) * thrContinuation W C₀ ε (sn n)) atTop
      (𝓝 (((∑ q ∈ E, W q) * (1 / (s₀ * (s₀ + s₀))) + 0 * weightedScrewContinuationExcept W E s₀)
        + 0 * ((C₀ : ℂ) / (s₀ - (ε : ℂ))))) := by
    have hfun : (fun n => (c n : ℂ) * thrContinuation W C₀ ε (sn n)) =
        fun n => ((∑ q ∈ E, W q) * (1 / (sn n * (sn n + s₀))) +
          (c n : ℂ) * weightedScrewContinuationExcept W E (sn n))
          + (c n : ℂ) * ((C₀ : ℂ) / (sn n - (ε : ℂ))) := by
      funext n
      unfold thrContinuation
      rw [weightedScrewLaplaceContinuation_eq_sum_add_except W E (hsum n), mul_add, mul_add,
        Finset.mul_sum, Finset.sum_mul]
      congr 2
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [← hatomE n q hq]
      ring
    rw [hfun]
    refine Tendsto.add (Tendsto.add (tendsto_const_nhds.mul ?_) (hcC_tend.mul ?_)) (hcC_tend.mul ?_)
    · have hden : Tendsto (fun n => sn n * (sn n + s₀)) atTop (𝓝 (s₀ * (s₀ + s₀))) :=
        hsn_tend.mul (hsn_tend.add_const s₀)
      have hden0 : s₀ * (s₀ + s₀) ≠ 0 := by
        refine mul_ne_zero hs₀ne ?_
        intro h
        have := congrArg Complex.re h
        rw [add_re, zero_re] at this
        linarith
      simpa [one_div] using hden.inv₀ hden0
    · exact (hrest.continuousAt.tendsto).comp hsn_tend
    · have hden : Tendsto (fun n => sn n - (ε : ℂ)) atTop (𝓝 (s₀ - (ε : ℂ))) :=
        hsn_tend.sub_const _
      exact tendsto_const_nhds.div hden hs₀ε
  -- limit of `c_n · F(s_n)`
  have hlimF : Tendsto (fun n => (c n : ℂ) * thrLaplace W C₀ ε (sn n)) atTop
      (𝓝 (0 * thrLaplace W C₀ ε s₀)) :=
    hcC_tend.mul (((hF s₀ hre0).continuousAt.tendsto).comp hsn_tend)
  have heqn : (fun n => (c n : ℂ) * thrLaplace W C₀ ε (sn n)) =
      fun n => (c n : ℂ) * thrContinuation W C₀ ε (sn n) := by
    funext n
    rw [hEq (hsn_mem n)]
  rw [heqn] at hlimF
  have hzero := tendsto_nhds_unique hlimG hlimF
  rw [zero_mul, add_zero, zero_mul, add_zero, zero_mul] at hzero
  -- contradiction with the nonzero finite part
  have hsumE : ∑ q ∈ E, W q = (E.card : ℂ) * W q₀ := by
    rw [Finset.sum_congr rfl hWE, Finset.sum_const, nsmul_eq_mul]
  have hW0 : W q₀ ≠ 0 := hWne q₀ (by linarith)
  have hcard : (E.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨q₀, hq₀E⟩).ne'
  have hden0 : s₀ * (s₀ + s₀) ≠ 0 := by
    refine mul_ne_zero hs₀ne ?_
    intro h
    have := congrArg Complex.re h
    rw [add_re, zero_re] at this
    linarith
  rw [hsumE] at hzero
  have : (E.card : ℂ) * W q₀ * (1 / (s₀ * (s₀ + s₀))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcard hW0) (one_div_ne_zero hden0)
  exact this hzero

/-- **Exponential slack caps the excess.**  Under the exponential lower bound every copy satisfies
`|Im γ_q| ≤ ε`. -/
theorem abs_im_le_of_thr {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hWpt : ∀ q q' : XiZeroCopy, xiSpectralPoint q' = xiSpectralPoint q → W q' = W q)
    (hWeven : ∀ q q' : XiZeroCopy, xiSpectralPoint q' = -xiSpectralPoint q → W q' = W q)
    (hWne : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → W q ≠ 0)
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε := by
  rw [abs_le]
  constructor
  · exact neg_le_im_of_thr W C₀ ε hC hW hWpt hWeven hWne hlow hreal hε0 hε q
  · have h := neg_le_im_of_thr W C₀ ε hC hW hWpt hWeven hWne hlow hreal hε0 hε
      (xiZeroCopyReflectEquiv q)
    rw [xiSpectralPoint_reflect, neg_im] at h
    linarith

end

end RHTower
