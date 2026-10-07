import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseTrace
import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift

/-!
# The pole-subtracted actual producer has an integrable boundary trace

The original full-positive source supplies the uniform strip decay needed by
inverse Mellin. The pole at one is removed in the interior; no continuity on
the critical edge is assumed. The resulting trace converges globally in L1.
-/

open Complex Set Filter MeasureTheory Topology

noncomputable section
namespace RHTower.WeilWorkSettledPhase

open WeilSpectral IntegerMassRigidity PhaseLockRigidity

/-- The actual completion with its pole subtracted using the corpus normalization. -/
def sourceRemainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : ℂ → ℂ :=
  bigEG (sourceCompletion hW)

theorem differentiableOn_sourceRemainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    DifferentiableOn ℂ (sourceRemainder hW) {s : ℂ | 1 / 2 < s.re} :=
  differentiableOn_bigEG (fun _ hs => hasDerivAt_sourceCompletion hW hs)

theorem continuous_sourceRemainder_slice {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) : Continuous (fun y : ℝ => sourceRemainder hW (tracePoint x y)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd := (differentiableOn_sourceRemainder hW).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp; linarith :
      tracePoint x y ∈ {s : ℂ | 1 / 2 < s.re}))
  exact hd.continuousAt.comp (f := tracePoint x) (by unfold tracePoint; fun_prop)

private theorem exists_bound_sourceRemainder_compact {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ B : ℝ, ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 → |s.im| ≤ 4 →
      ‖sourceRemainder hW s‖ ≤ B := by
  let KL := Icc (1 / 2 : ℝ) (3 / 4) ×ℂ Icc (-4 : ℝ) 4
  let KR := Icc (3 / 4 : ℝ) (3 / 2) ×ℂ Icc (-4 : ℝ) 4
  have hKL : IsCompact KL := isCompact_Icc.reProdIm isCompact_Icc
  have hKR : IsCompact KR := isCompact_Icc.reProdIm isCompact_Icc
  have hΓc : ContinuousOn (fun s : ℂ => Gammaℝ (s - 1)) KL := by
    intro s hs
    have hs' : s.re ∈ Icc (1 / 2 : ℝ) (3 / 4) ∧ s.im ∈ Icc (-4 : ℝ) 4 :=
      Complex.mem_reProdIm.mp hs
    have hs1 : s ≠ 1 := by
      intro h
      have := hs'.1.2
      rw [h] at this
      norm_num at this
    exact (differentiableAt_Gammaℝ_sub_one (by linarith [hs'.1.1]) hs1).continuousAt.continuousWithinAt
  obtain ⟨BΓ, hBΓ⟩ := hKL.exists_bound_of_continuousOn hΓc
  have hEc : ContinuousOn (sourceRemainder hW) KR :=
    (differentiableOn_sourceRemainder hW).continuousOn.mono (fun s hs => by
      have hs' := (Complex.mem_reProdIm.mp hs).1.1
      change (3 / 4 : ℝ) ≤ s.re at hs'
      change (1 / 2 : ℝ) < s.re
      linarith)
  obtain ⟨BE, hBE⟩ := hKR.exists_bound_of_continuousOn hEc
  obtain ⟨BG, hBG⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-4 : ℝ) 4)
    (continuous_sourceCompletion_slice hW (by norm_num : (0 : ℝ) < 3 / 2)).continuousOn
  refine ⟨max BE (8 * max BG 0 + ‖betaG (sourceCompletion hW)‖ * max BΓ 0), ?_⟩
  intro s hs hs2 him
  have him' : s.im ∈ Icc (-4 : ℝ) 4 := abs_le.mp him
  by_cases hre : s.re ≤ 3 / 4
  · have hmem : s ∈ KL := Complex.mem_reProdIm.mpr ⟨⟨hs.le, hre⟩, him'⟩
    have hn0 : (1 / 2 : ℝ) ≤ ‖s‖ := hs.le.trans (Complex.re_le_norm s)
    have hn1 : (1 / 4 : ℝ) ≤ ‖s - 1‖ := by
      have h := Complex.abs_re_le_norm (s - 1)
      have h' := neg_le_abs (s - 1).re
      simp only [Complex.sub_re, Complex.one_re] at h h'
      linarith
    have hden : (1 / 8 : ℝ) ≤ ‖s * (s - 1)‖ := by
      rw [norm_mul]
      nlinarith
    have hs0 : s ≠ 0 := by intro h; rw [h, norm_zero] at hn0; norm_num at hn0
    have hs1 : s ≠ 1 := by intro h; rw [h, sub_self, norm_zero] at hn1; norm_num at hn1
    have hg : ‖sourceCompletion hW s‖ ≤ max BG 0 := by
      have hp : tracePoint (s.re - 1 / 2) s.im = s := by
        rw [tracePoint, show (1 / 2 + (s.re - 1 / 2) : ℝ) = s.re by ring]
        exact Complex.re_add_im s
      calc ‖sourceCompletion hW s‖
          = ‖sourceCompletion hW (tracePoint (s.re - 1 / 2) s.im)‖ := by rw [hp]
        _ ≤ ‖sourceCompletion hW (tracePoint (3 / 2) s.im)‖ :=
          norm_sourceCompletion_le_right hW (by linarith) (by linarith) _
        _ ≤ BG := hBG s.im him'
        _ ≤ max BG 0 := le_max_left _ _
    have hquot : ‖sourceCompletion hW s / (s * (s - 1))‖ ≤ 8 * max BG 0 := by
      rw [norm_div, div_le_iff₀ (by linarith : 0 < ‖s * (s - 1)‖)]
      have hd' := mul_le_mul_of_nonneg_left hden (le_max_right BG 0)
      nlinarith
    rw [sourceRemainder, bigEG_eq hs0 hs1]
    calc ‖sourceCompletion hW s / (s * (s - 1)) -
          betaG (sourceCompletion hW) * Gammaℝ (s - 1)‖
        ≤ ‖sourceCompletion hW s / (s * (s - 1))‖ +
          ‖betaG (sourceCompletion hW)‖ * ‖Gammaℝ (s - 1)‖ := by
            rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ 8 * max BG 0 + ‖betaG (sourceCompletion hW)‖ * max BΓ 0 := by
        exact add_le_add hquot (mul_le_mul_of_nonneg_left
          ((hBΓ s hmem).trans (le_max_left _ _)) (norm_nonneg _))
      _ ≤ _ := le_max_right _ _
  · exact (hBE s (Complex.mem_reProdIm.mpr ⟨⟨le_of_not_ge hre, hs2⟩, him'⟩)).trans
      (le_max_left _ _)

/-- Uniform quadratic decay on the open critical strip, supplied by hW alone. -/
theorem exists_decay_sourceRemainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 →
      ‖sourceRemainder hW s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₁, N, hC₁, hB⟩ := FractionalMassRigidity.exists_bound_bigG_two
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ)
  obtain ⟨K, _, hK⟩ := exists_bound_pow_mul_exp_neg (N + 2)
  obtain ⟨CΓ, _, hΓ⟩ := exists_decay_Gammaℝ_sub_one
  obtain ⟨B, hBc⟩ := exists_bound_sourceRemainder_compact hW
  let A := C₁ * K + ‖betaG (sourceCompletion hW)‖ * CΓ
  refine ⟨max A (17 * max B 0), (by positivity), ?_⟩
  intro s hs hs2
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  by_cases him : 4 ≤ |s.im|
  · have hn0 : 4 ≤ ‖s‖ := him.trans (Complex.abs_im_le_norm s)
    have hn1 : 4 ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
      exact him.trans h
    have hs0 : s ≠ 0 := by intro h; rw [h, norm_zero] at hn0; norm_num at hn0
    have hs1 : s ≠ 1 := by intro h; rw [h, sub_self, norm_zero] at hn1; norm_num at hn1
    have hden : 1 ≤ ‖s * (s - 1)‖ := by rw [norm_mul]; nlinarith
    have hp : tracePoint (s.re - 1 / 2) s.im = s := by
      rw [tracePoint, show (1 / 2 + (s.re - 1 / 2) : ℝ) = s.re by ring]
      exact Complex.re_add_im s
    have hr : tracePoint (3 / 2) s.im = 2 + (s.im : ℂ) * I := by norm_num [tracePoint]
    have hg : ‖sourceCompletion hW s‖ ≤
        C₁ * ((|s.im| + 4) ^ N * Real.exp (-(Real.pi * |s.im| / 4))) := by
      have h := norm_sourceCompletion_le_right hW (by linarith : 0 < s.re - 1 / 2)
        (by linarith : s.re - 1 / 2 ≤ 3 / 2) s.im
      rw [hp, hr, sourceCompletion_eq_bigG hW (s := 2 + (s.im : ℂ) * I) (by simp)] at h
      exact h.trans (hB s.im)
    have hd := pow_mul_exp_neg_le_div hK (abs_nonneg s.im)
    rw [sq_abs] at hd
    rw [sourceRemainder, bigEG_eq hs0 hs1]
    calc ‖sourceCompletion hW s / (s * (s - 1)) -
          betaG (sourceCompletion hW) * Gammaℝ (s - 1)‖
        ≤ ‖sourceCompletion hW s / (s * (s - 1))‖ +
          ‖betaG (sourceCompletion hW)‖ * ‖Gammaℝ (s - 1)‖ := by
            rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ ‖sourceCompletion hW s‖ +
          ‖betaG (sourceCompletion hW)‖ * (CΓ / (1 + s.im ^ 2)) := by
        gcongr
        · rw [norm_div]; exact div_le_self (norm_nonneg _) hden
        · exact hΓ s hs.le hs2 him
      _ ≤ C₁ * (K / (1 + s.im ^ 2)) +
          ‖betaG (sourceCompletion hW)‖ * (CΓ / (1 + s.im ^ 2)) := by
        gcongr
        exact hg.trans (mul_le_mul_of_nonneg_left hd hC₁)
      _ = A / (1 + s.im ^ 2) := by dsimp [A]; ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have him' : |s.im| ≤ 4 := (lt_of_not_ge him).le
    have hb := (hBc s hs hs2 him').trans (le_max_left B 0)
    have hsq : s.im ^ 2 ≤ 16 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
    calc ‖sourceRemainder hW s‖ ≤ max B 0 := hb
      _ ≤ 17 * max B 0 / (1 + s.im ^ 2) := by
        rw [le_div_iff₀ hpos]
        nlinarith [le_max_right B 0]
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- The pole-subtracted trace retains the entire canonical boundary function. -/
def remainderTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℂ :=
  sourceTrace hW y / (tracePoint 0 y * (tracePoint 0 y - 1)) -
    betaG (sourceCompletion hW) * Gammaℝ (tracePoint 0 y - 1)

theorem tendsto_remainderTrace_ae {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ᵐ y : ℝ, Tendsto (fun x : ℝ => sourceRemainder hW (tracePoint x y))
      (𝓝[>] 0) (𝓝 (remainderTrace hW y)) := by
  filter_upwards [tendsto_sourceTrace_ae hW] with y hy
  have hp : Tendsto (fun x : ℝ => tracePoint x y) (𝓝[>] 0) (𝓝 (tracePoint 0 y)) := by
    have hc : Continuous (fun x : ℝ => tracePoint x y) := by unfold tracePoint; fun_prop
    exact hc.continuousAt.continuousWithinAt.tendsto
  have hr : (tracePoint 0 y).re = 1 / 2 := by simp
  have h0 : tracePoint 0 y ≠ 0 := by intro h; rw [h] at hr; norm_num at hr
  have h1 : tracePoint 0 y ≠ 1 := by intro h; rw [h] at hr; norm_num at hr
  have hden : Tendsto (fun x : ℝ => tracePoint x y * (tracePoint x y - 1))
      (𝓝[>] 0) (𝓝 (tracePoint 0 y * (tracePoint 0 y - 1))) :=
    hp.mul (hp.sub tendsto_const_nhds)
  have hg := (differentiableAt_Gammaℝ_sub_one (by rw [hr]; norm_num) h1).continuousAt.tendsto.comp hp
  have hlim : Tendsto (fun x : ℝ =>
      sourceCompletion hW (tracePoint x y) / (tracePoint x y * (tracePoint x y - 1)) -
        betaG (sourceCompletion hW) * Gammaℝ (tracePoint x y - 1))
      (𝓝[>] 0) (𝓝 (remainderTrace hW y)) :=
    (hy.div hden (mul_ne_zero h0 (sub_ne_zero.mpr h1))).sub (tendsto_const_nhds.mul hg)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds]
      with x (hx : 0 < x) hx1
  have h0x : tracePoint x y ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [tracePoint_re, Complex.zero_re] at he
    linarith
  have h1x : tracePoint x y ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [tracePoint_re, Complex.one_re] at he
    linarith
  exact (bigEG_eq h0x h1x).symm

theorem aestronglyMeasurable_remainderTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    AEStronglyMeasurable (remainderTrace hW) := by
  let F : ℝ → ℝ → ℂ := fun x y => if 0 < x then sourceRemainder hW (tracePoint x y) else 0
  have hF : ∀ x : ℝ, AEStronglyMeasurable (F x) := by
    intro x
    by_cases hx : 0 < x
    · simpa only [F, if_pos hx] using (continuous_sourceRemainder_slice hW hx).aestronglyMeasurable
    · simp only [F, if_neg hx]
      exact aestronglyMeasurable_const
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ)) hF
  filter_upwards [tendsto_remainderTrace_ae hW] with y hy
  refine hy.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  simp only [F, if_pos hx]

/-- The same source-derived decay constant controls the limiting trace. -/
theorem exists_decay_sourceRemainder_and_trace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 →
        ‖sourceRemainder hW s‖ ≤ C / (1 + s.im ^ 2)) ∧
      ∀ᵐ y : ℝ, ‖remainderTrace hW y‖ ≤ C / (1 + y ^ 2) := by
  obtain ⟨C, hC, hB⟩ := exists_decay_sourceRemainder hW
  refine ⟨C, hC, hB, ?_⟩
  filter_upwards [tendsto_remainderTrace_ae hW] with y hy
  apply le_of_tendsto hy.norm
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with x (hx : 0 < x) hx1
  have h := hB (tracePoint x y) (by simp; linarith) (by simp; linarith)
  simpa [tracePoint] using h

theorem integrable_remainderTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Integrable (remainderTrace hW) := by
  obtain ⟨C, _, _, hB⟩ := exists_decay_sourceRemainder_and_trace hW
  refine (integrable_inv_one_add_sq.const_mul C).mono'
    (aestronglyMeasurable_remainderTrace hW) ?_
  simpa only [div_eq_mul_inv] using hB

/-- Global L1 passage for the pole-subtracted actual producer. -/
theorem tendsto_integral_norm_remainderTrace_sub {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Tendsto (fun x : ℝ => ∫ y : ℝ,
      ‖sourceRemainder hW (tracePoint x y) - remainderTrace hW y‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hE, he⟩ := exists_decay_sourceRemainder_and_trace hW
  have hm : ∀ᶠ x in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun y : ℝ => ‖sourceRemainder hW (tracePoint x y) - remainderTrace hW y‖) := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact ((continuous_sourceRemainder_slice hW hx).aestronglyMeasurable.sub
      (aestronglyMeasurable_remainderTrace hW)).norm
  have hb : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ᵐ y : ℝ,
      ‖‖sourceRemainder hW (tracePoint x y) - remainderTrace hW y‖‖ ≤
        2 * (C / (1 + y ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
        with x (hx : 0 < x) hx1
    filter_upwards [he] with y hy
    have h := hE (tracePoint x y) (by simp; linarith) (by simp; linarith)
    have h' : ‖sourceRemainder hW (tracePoint x y)‖ ≤ C / (1 + y ^ 2) :=
      by simpa [tracePoint] using h
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by linarith)
  have hi : Integrable (fun y : ℝ => 2 * (C / (1 + y ^ 2))) := by
    simpa only [div_eq_mul_inv] using (integrable_inv_one_add_sq.const_mul C).const_mul 2
  have hl : ∀ᵐ y : ℝ, Tendsto
      (fun x : ℝ => ‖sourceRemainder hW (tracePoint x y) - remainderTrace hW y‖)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [tendsto_remainderTrace_ae hW] with y hy
    have hc : Tendsto (fun _ : ℝ => remainderTrace hW y) (𝓝[>] (0 : ℝ))
        (𝓝 (remainderTrace hW y)) := tendsto_const_nhds
    simpa using (hy.sub hc).norm
  simpa using tendsto_integral_filter_of_dominated_convergence
    (fun y => 2 * (C / (1 + y ^ 2))) hm hb hi hl

/-- The actual source admits the weighted contour shift onto its measurable
critical trace, without any boundary-continuity or atomicity hypothesis. -/
theorem integral_sourceRemainder_eq_boundary {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ, (r : ℂ) ^ (-tracePoint 1 y / 2) * sourceRemainder hW (tracePoint 1 y)) =
      ∫ y : ℝ, (r : ℂ) ^ (-tracePoint 0 y / 2) * remainderTrace hW y := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hw : Continuous (fun s : ℂ => (r : ℂ) ^ (-s / 2)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hr0)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (1 / 2 : ℝ) (3 / 2)) (hw.comp Complex.continuous_ofReal).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hweight : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖(r : ℂ) ^ (-s / 2)‖ ≤ M := by
    intro s hs hs2
    have hn : ‖(r : ℂ) ^ (-s / 2)‖ = ‖(r : ℂ) ^ (-(s.re : ℂ) / 2)‖ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_cpow_eq_rpow_re_of_pos hr]
      simp
    rw [hn]
    exact (hB s.re ⟨hs, hs2⟩).trans (le_max_left _ _)
  obtain ⟨C, _, hE⟩ := exists_decay_sourceRemainder hW
  let H : ℂ → ℂ := fun s => (r : ℂ) ^ (-s / 2) * sourceRemainder hW s
  have hHd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ H s := by
    intro s hs
    exact ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hr0)).mul
      ((differentiableOn_sourceRemainder hW).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs))
  have hHb : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 →
      ‖H s‖ ≤ (M * C) / (1 + s.im ^ 2) := by
    intro s hs hs2
    calc ‖H s‖ = ‖(r : ℂ) ^ (-s / 2)‖ * ‖sourceRemainder hW s‖ := norm_mul _ _
      _ ≤ M * (C / (1 + s.im ^ 2)) :=
        mul_le_mul (hweight s hs.le hs2) (hE s hs hs2) (norm_nonneg _) hM
      _ = _ := by ring
  have hshift : ∀ x : ℝ, 0 < x → x ≤ 1 →
      (∫ y : ℝ, H (tracePoint x y)) = ∫ y : ℝ, H (tracePoint 1 y) := by
    intro x hx hx1
    have hmem : ∀ s : ℂ, s.re ∈ uIcc (1 / 2 + x) (1 / 2 + 1 : ℝ) →
        1 / 2 < s.re ∧ s.re ≤ 3 / 2 := by
      intro s hs
      rcases Set.mem_uIcc.mp hs with hs | hs <;> constructor <;> linarith [hs.1, hs.2]
    exact GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay
      (fun s hs => hHd s (hmem s hs).1)
      (fun s hs => hHb s (hmem s hs).1 (hmem s hs).2)
  have hm : ∀ᶠ x in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun y : ℝ => H (tracePoint x y)) := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact ((hw.comp (by unfold tracePoint; fun_prop)).mul
      (continuous_sourceRemainder_slice hW hx)).aestronglyMeasurable
  have hb : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ᵐ y : ℝ,
      ‖H (tracePoint x y)‖ ≤ (M * C) / (1 + y ^ 2) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
        with x (hx : 0 < x) hx1
    exact Eventually.of_forall fun y => by
      have h := hHb (tracePoint x y) (by simp; linarith) (by simp; linarith)
      simpa [tracePoint] using h
  have hi : Integrable (fun y : ℝ => (M * C) / (1 + y ^ 2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (M * C)
  have hl : ∀ᵐ y : ℝ, Tendsto (fun x : ℝ => H (tracePoint x y)) (𝓝[>] 0)
      (𝓝 ((r : ℂ) ^ (-tracePoint 0 y / 2) * remainderTrace hW y)) := by
    filter_upwards [tendsto_remainderTrace_ae hW] with y hy
    have hp : Tendsto (fun x : ℝ => tracePoint x y) (𝓝[>] 0) (𝓝 (tracePoint 0 y)) := by
      have hc : Continuous (fun x : ℝ => tracePoint x y) := by unfold tracePoint; fun_prop
      exact hc.continuousAt.continuousWithinAt.tendsto
    exact ((hw.tendsto _).comp hp).mul hy
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun y => (M * C) / (1 + y ^ 2)) hm hb hi hl
  have hc : Tendsto (fun x : ℝ => ∫ y : ℝ, H (tracePoint x y)) (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, H (tracePoint 1 y))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
        with x (hx : 0 < x) hx1
    exact (hshift x hx hx1.le).symm
  exact tendsto_nhds_unique hc ht

end RHTower.WeilWorkSettledPhase
