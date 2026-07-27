import GaloisForLFunctions.RHTower.MobiusCausalBoundaryEnergy

/-!
# Boundary bounds for the coupled causal multiplier itself

The same three-region analysis that bounds the parameter derivative bounds the multiplier:

```text
‖M_ω(iτ)‖ ≤ K·1_{|τ|≤9} + C·log⁸|τ|/|τ|·1_{|τ|>9}      (0 < ω ≤ ω₀, τ ≠ 0).
```

Near the origin the pole-unit form `M_ω(z) = [Z(1+z)q_ω(z) - q_ω(0)]/z` is used, so only first
derivatives of the entire pole unit enter.
-/

open MeasureTheory Filter Topology Complex Metric

namespace RHTower

noncomputable section

/-! ### The near-origin bound -/

/-- The denominator of the shifted pole-unit quotient. -/
def poleMDen (ω : ℝ) (z : ℂ) : ℂ :=
  (1 + (ω : ℂ) + z) * zetaPoleUnit (1 + 2 * (ω : ℂ) + z)

/-- Its `z`-derivative. -/
def poleMDenDeriv (ω : ℝ) (z : ℂ) : ℂ :=
  zetaPoleUnit (1 + 2 * (ω : ℂ) + z) +
    (1 + (ω : ℂ) + z) * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + z)

theorem mobiusCausalQ_eq_div (ω : ℝ) (z : ℂ) :
    mobiusCausalQ ω z = (2 * (ω : ℂ) + z) / poleMDen ω z := rfl

theorem hasDerivAt_poleMDen (ω : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => poleMDen ω w) (poleMDenDeriv ω z) z := by
  have hZ := hasDerivAt_zetaPoleUnit_comp ω z
  have ha : HasDerivAt (fun w : ℂ => 1 + (ω : ℂ) + w) 1 z := hasDerivAt_shift (1 + (ω : ℂ)) z
  have h := ha.mul hZ
  refine h.congr_deriv ?_
  rw [poleMDenDeriv]
  ring

/-- **Uniform near-origin bound for the multiplier.** -/
theorem exists_near_origin_multiplier_bound :
    ∃ δ ω₀ C : ℝ, 0 < δ ∧ 0 < ω₀ ∧ 0 ≤ C ∧
      ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ → ∀ z : ℂ, 0 ≤ z.re → z ≠ 0 → ‖z‖ ≤ δ →
        ‖mobiusCausalMultiplier ω z‖ ≤ C := by
  obtain ⟨ρ, Cb, hρpos, hρ8, hCb1, hbd⟩ := exists_poleUnit_ball_bounds
  have hCb0 : (0 : ℝ) < Cb := by linarith
  refine ⟨ρ / 4, ρ / 8, Cb * (2 * (2 * Cb) * (3 * Cb) / (1 / 4 : ℝ) ^ 2) + Cb,
    by linarith, by linarith, by positivity, ?_⟩
  intro ω hω hωle z hzre hz0 hzδ
  have hznorm : (0 : ℝ) < ‖z‖ := by
    rw [norm_pos_iff]
    exact hz0
  -- membership facts
  have hmemZ : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → (1 : ℂ) + 2 * (ω : ℂ) + w ∈ closedBall (1 : ℂ) ρ := by
    intro w hw
    have h1 : dist ((1 : ℂ) + 2 * (ω : ℂ) + w) 1 = ‖2 * (ω : ℂ) + w‖ := by
      rw [dist_eq_norm]
      ring_nf
    rw [Metric.mem_closedBall, h1]
    have h2 : ‖2 * (ω : ℂ) + w‖ ≤ 2 * ω + ‖w‖ := by
      refine le_trans (norm_add_le _ _) ?_
      have hn : ‖2 * ((ω : ℝ) : ℂ)‖ = 2 * ω := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
        norm_num
      rw [hn]
    linarith
  have hmem1 : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → (1 : ℂ) + w ∈ closedBall (1 : ℂ) ρ := by
    intro w hw
    have h1 : dist ((1 : ℂ) + w) 1 = ‖w‖ := by
      rw [dist_eq_norm]
      ring_nf
    rw [Metric.mem_closedBall, h1]
    linarith
  have halb : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → (1 : ℝ) / 2 ≤ ‖1 + (ω : ℂ) + w‖ := by
    intro w hw
    have hre : ((1 : ℂ) + (ω : ℂ) + w).re = 1 + ω + w.re := by simp [Complex.add_re]
    have hwre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h1 : ((1 : ℂ) + (ω : ℂ) + w).re ≤ ‖1 + (ω : ℂ) + w‖ := Complex.re_le_norm _
    have h2 : -w.re ≤ ‖w‖ := by
      have := abs_le.1 hwre
      linarith [this.1]
    rw [hre] at h1
    have hρ32 : ρ / 4 ≤ 1 / 32 := by linarith
    linarith
  have haub : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → ‖1 + (ω : ℂ) + w‖ ≤ 2 := by
    intro w hw
    have h1 : ‖1 + (ω : ℂ) + w‖ ≤ ‖(1 : ℂ) + (ω : ℂ)‖ + ‖w‖ := norm_add_le _ _
    have h2 : ‖(1 : ℂ) + (ω : ℂ)‖ ≤ 1 + ω := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
    have : ω ≤ ρ / 8 := hωle
    linarith
  have huub : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → ‖2 * (ω : ℂ) + w‖ ≤ 1 / 2 := by
    intro w hw
    have h2 : ‖2 * (ω : ℂ) + w‖ ≤ 2 * ω + ‖w‖ := by
      refine le_trans (norm_add_le _ _) ?_
      have hn : ‖2 * ((ω : ℝ) : ℂ)‖ = 2 * ω := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
        norm_num
      rw [hn]
    have : ω ≤ ρ / 8 := hωle
    linarith
  -- denominator bounds
  have hdenlb : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → (1 / 4 : ℝ) ≤ ‖poleMDen ω w‖ := by
    intro w hw
    obtain ⟨hZlb, -, -, -⟩ := hbd _ (hmemZ w hw)
    have ha := halb w hw
    have e1 : ‖poleMDen ω w‖ = ‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ := by
      rw [poleMDen, norm_mul]
    rw [e1]
    nlinarith [norm_nonneg (1 + (ω : ℂ) + w), norm_nonneg (zetaPoleUnit (1 + 2 * (ω : ℂ) + w))]
  have hdenub : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → ‖poleMDen ω w‖ ≤ 2 * Cb := by
    intro w hw
    obtain ⟨-, hZ, -, -⟩ := hbd _ (hmemZ w hw)
    have ha := haub w hw
    have e1 : ‖poleMDen ω w‖ = ‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ := by
      rw [poleMDen, norm_mul]
    rw [e1]
    exact mul_le_mul ha hZ (norm_nonneg _) (by norm_num)
  have hdendb : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → ‖poleMDenDeriv ω w‖ ≤ 3 * Cb := by
    intro w hw
    obtain ⟨-, hZ, hZ', -⟩ := hbd _ (hmemZ w hw)
    have ha := haub w hw
    rw [poleMDenDeriv]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖(1 + (ω : ℂ) + w) * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ ≤ 2 * Cb := by
      rw [norm_mul]
      exact mul_le_mul ha hZ' (norm_nonneg _) (by norm_num)
    linarith
  -- the numerator moves by exactly ‖z‖
  have hnumdiff : ‖(2 * (ω : ℂ) + z) - (2 * (ω : ℂ) + 0)‖ ≤ 3 * Cb * ‖z‖ := by
    have h : (2 * (ω : ℂ) + z) - (2 * (ω : ℂ) + 0) = z := by ring
    rw [h]
    nlinarith [hznorm, hCb1]
  have hzball : z ∈ closedBall (0 : ℂ) (ρ / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hzδ
  have h0ball : (0 : ℂ) ∈ closedBall (0 : ℂ) (ρ / 4) := by
    rw [Metric.mem_closedBall, dist_self]
    linarith
  have hmvD : ‖poleMDen ω z - poleMDen ω 0‖ ≤ 3 * Cb * ‖z‖ := by
    have h := HTGeometry.norm_sub_le_of_hasDerivAt_ball (f := fun w : ℂ => poleMDen ω w)
      (f' := fun w : ℂ => poleMDenDeriv ω w) (c := (0 : ℂ)) (r := ρ / 4) (C := 3 * Cb)
      (fun w => hasDerivAt_poleMDen ω w)
      (fun w hw => hdendb w (by rwa [Metric.mem_closedBall, dist_zero_right] at hw))
      h0ball hzball
    simpa using h
  have hmvZ : ‖zetaPoleUnit (1 + z) - 1‖ ≤ Cb * ‖z‖ := by
    have h := HTGeometry.norm_sub_le_of_hasDerivAt_ball (f := fun w : ℂ => zetaPoleUnit (1 + w))
      (f' := fun w : ℂ => deriv zetaPoleUnit (1 + w)) (c := (0 : ℂ)) (r := ρ / 4) (C := Cb)
      (fun w => hasDerivAt_zetaPoleUnit_one_add w)
      (fun w hw => (hbd _ (hmem1 w (by rwa [Metric.mem_closedBall, dist_zero_right] at hw))).2.2.1)
      h0ball hzball
    simpa [zetaPoleUnit_one] using h
  -- the quotient difference
  have hq : ‖mobiusCausalQ ω z - mobiusCausalQ ω 0‖
      ≤ 2 * (2 * Cb) * (3 * Cb * ‖z‖) / (1 / 4 : ℝ) ^ 2 := by
    rw [mobiusCausalQ_eq_div, mobiusCausalQ_eq_div]
    refine HTGeometry.norm_div_sub_div_le (by norm_num)
      (hdenlb z hzδ) (hdenlb 0 (by simpa using le_of_lt (by linarith : (0 : ℝ) < ρ / 4)))
      ?_ (hdenub 0 (by simpa using le_of_lt (by linarith : (0 : ℝ) < ρ / 4)))
      hnumdiff hmvD (by positivity)
    · have hn : ‖2 * ((ω : ℝ) : ℂ) + 0‖ = 2 * ω := by
        rw [add_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
        norm_num
      rw [hn]
      have : ω ≤ ρ / 8 := hωle
      nlinarith
  have hq0 : ‖mobiusCausalQ ω 0‖ ≤ 1 := by
    rw [mobiusCausalQ_eq_div, norm_div]
    have h1 : ‖2 * ((ω : ℝ) : ℂ) + 0‖ ≤ 1 / 4 := by
      rw [add_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
      have : ω ≤ ρ / 8 := hωle
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2]
      linarith
    have h2 := hdenlb 0 (by simpa using le_of_lt (by linarith : (0 : ℝ) < ρ / 4))
    rw [div_le_one (by linarith)]
    linarith
  have hZub : ‖zetaPoleUnit (1 + z)‖ ≤ Cb := (hbd _ (hmem1 z hzδ)).2.1
  -- assemble
  have hsplit : mobiusCausalNumerator ω z
      = zetaPoleUnit (1 + z) * (mobiusCausalQ ω z - mobiusCausalQ ω 0) +
        (zetaPoleUnit (1 + z) - 1) * mobiusCausalQ ω 0 := by
    rw [mobiusCausalNumerator]
    ring
  rw [mobiusCausalMultiplier_eq_numerator_div hω hzre hz0, norm_div, hsplit]
  have hnorm : ‖zetaPoleUnit (1 + z) * (mobiusCausalQ ω z - mobiusCausalQ ω 0) +
      (zetaPoleUnit (1 + z) - 1) * mobiusCausalQ ω 0‖
      ≤ Cb * (2 * (2 * Cb) * (3 * Cb * ‖z‖) / (1 / 4 : ℝ) ^ 2) + Cb * ‖z‖ * 1 := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖zetaPoleUnit (1 + z)‖ * ‖mobiusCausalQ ω z - mobiusCausalQ ω 0‖
        ≤ Cb * (2 * (2 * Cb) * (3 * Cb * ‖z‖) / (1 / 4 : ℝ) ^ 2) :=
      mul_le_mul hZub hq (norm_nonneg _) (by positivity)
    have h2 : ‖zetaPoleUnit (1 + z) - 1‖ * ‖mobiusCausalQ ω 0‖ ≤ Cb * ‖z‖ * 1 :=
      mul_le_mul hmvZ hq0 (norm_nonneg _) (by positivity)
    linarith
  rw [div_le_iff₀ hznorm]
  have hfin : Cb * (2 * (2 * Cb) * (3 * Cb * ‖z‖) / (1 / 4 : ℝ) ^ 2) + Cb * ‖z‖ * 1
      = (Cb * (2 * (2 * Cb) * (3 * Cb) / (1 / 4 : ℝ) ^ 2) + Cb) * ‖z‖ := by
    ring
  rw [← hfin]
  exact hnorm

/-! ### The reciprocal zeta factor at the critical parameter -/

theorem tendsto_inv_riemannZeta_one_add_two_mul :
    Tendsto (fun ω : ℝ => (riemannZeta (1 + 2 * (ω : ℂ)))⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hbase := tendsto_inv_riemannZeta_one_add_two_mul_div
  have hω : Tendsto (fun ω : ℝ => ((ω : ℝ) : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous fun ω : ℝ => ((ω : ℝ) : ℂ) := Complex.continuous_ofReal
    have h := hc.tendsto (0 : ℝ)
    rw [Complex.ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hmul := hω.mul hbase
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω0
  have hωpos : (0 : ℝ) < ω := hω0
  have hωne : ((ω : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hωpos
  field_simp

theorem exists_inv_zeta_real_bound :
    ∃ ω₂ : ℝ, 0 < ω₂ ∧ ∀ ω : ℝ, 0 < ω → ω ≤ ω₂ →
      ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖ ≤ 1 := by
  have h := tendsto_inv_riemannZeta_one_add_two_mul
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (riemannZeta (1 + 2 * (ω : ℂ)))⁻¹ ∈ Metric.ball (0 : ℂ) 1 :=
    h.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := hev
  refine ⟨ε / 2, by linarith, fun ω hω hωle => ?_⟩
  have hdist : dist ω (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hω]
    linarith
  have hmem := hε hdist hω
  rw [Metric.mem_ball, dist_zero_right] at hmem
  linarith

/-! ### The mid-range and far-field bounds -/

theorem exists_midRange_zeta_bounds (ω₀ δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ midRangeSet ω₀ δ,
      ‖riemannZeta s‖ ≤ C ∧ ‖(riemannZeta s)⁻¹‖ ≤ C := by
  have hcomp := isCompact_midRangeSet ω₀ δ
  have hana : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
    have hdiffOn : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
      intro s hs
      exact (differentiableAt_riemannZeta (by simpa using hs)).differentiableWithinAt
    exact hdiffOn.analyticOnNhd isOpen_compl_singleton
  have hmemc : ∀ s ∈ midRangeSet ω₀ δ, s ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro s hs
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using midRangeSet_ne_one hδ hs
  have hζcont : ContinuousOn riemannZeta (midRangeSet ω₀ δ) := by
    intro s hs
    exact ((hana s (hmemc s hs)).continuousAt).continuousWithinAt
  have hinvcont : ContinuousOn (fun s : ℂ => (riemannZeta s)⁻¹) (midRangeSet ω₀ δ) :=
    hζcont.inv₀ (fun s hs => riemannZeta_ne_zero_midRangeSet hs)
  obtain ⟨C1, hC1⟩ := hcomp.exists_bound_of_continuousOn hζcont
  obtain ⟨C2, hC2⟩ := hcomp.exists_bound_of_continuousOn hinvcont
  refine ⟨max (max C1 C2) 0, le_max_right _ _, fun s hs => ⟨?_, ?_⟩⟩
  · exact le_trans (hC1 s hs) (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact le_trans (hC2 s hs) (le_trans (le_max_right _ _) (le_max_left _ _))

theorem exists_mid_range_multiplier_bound {ω₀ δ : ℝ} (hω₀ : 0 < ω₀) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ →
      ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖ ≤ 1 →
      ∀ τ : ℝ, δ ≤ |τ| → |τ| ≤ 9 →
        ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC0, hCb⟩ := exists_midRange_zeta_bounds ω₀ δ hδ
  refine ⟨C * C + 1 / δ, by positivity, ?_⟩
  intro ω hω hωle hζinv τ hτδ hτ9
  set z : ℂ := (τ : ℂ) * Complex.I with hzdef
  have hzim : z.im = τ := by rw [hzdef]; simp
  have hznorm : ‖z‖ = |τ| := by
    rw [hzdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hmem1 : (1 : ℂ) + z ∈ midRangeSet ω₀ δ := by
    have him : ((1 : ℂ) + z).im = τ := by simp [Complex.add_im, hzim]
    refine ⟨by rw [hzdef]; simp, by rw [hzdef]; simp; linarith, by rw [him]; exact hτδ,
      by rw [him]; exact hτ9⟩
  have hmem2 : (1 : ℂ) + 2 * (ω : ℂ) + z ∈ midRangeSet ω₀ δ := by
    have hre : ((1 : ℂ) + 2 * (ω : ℂ) + z).re = 1 + 2 * ω := by
      rw [hzdef]; simp [Complex.add_re, Complex.mul_re]
    have him : ((1 : ℂ) + 2 * (ω : ℂ) + z).im = τ := by
      rw [hzdef]; simp [Complex.add_im, Complex.mul_im]
    exact ⟨by rw [hre]; linarith, by rw [hre]; linarith, by rw [him]; exact hτδ,
      by rw [him]; exact hτ9⟩
  have hlin_lb1 : (1 : ℝ) ≤ ‖1 + (ω : ℂ) + z‖ := by
    have h1 : ((1 : ℂ) + (ω : ℂ) + z).re ≤ ‖1 + (ω : ℂ) + z‖ := Complex.re_le_norm _
    have h2 : ((1 : ℂ) + (ω : ℂ) + z).re = 1 + ω := by
      rw [hzdef]; simp [Complex.add_re]
    rw [h2] at h1
    linarith
  have hlinpos : (0 : ℝ) < ‖1 + (ω : ℂ) + z‖ := by linarith
  have hω1 : (1 : ℝ) ≤ ‖1 + (ω : ℂ)‖ := by
    have h1 : ((1 : ℂ) + (ω : ℂ)).re ≤ ‖1 + (ω : ℂ)‖ := Complex.re_le_norm _
    have h2 : ((1 : ℂ) + (ω : ℂ)).re = 1 + ω := by simp [Complex.add_re]
    rw [h2] at h1
    linarith
  have hfirst : ‖riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z))‖
      ≤ C * C := by
    have hsplit : ‖riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z))‖
        = ‖riemannZeta (1 + z)‖ * ‖1 + (ω : ℂ) + z‖⁻¹ *
          ‖(riemannZeta (1 + 2 * (ω : ℂ) + z))⁻¹‖ := by
      rw [norm_div, norm_mul, norm_inv, div_eq_mul_inv, mul_inv]
      ring
    rw [hsplit]
    have hinvlin : ‖1 + (ω : ℂ) + z‖⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hlin_lb1
    have hstep : ‖riemannZeta (1 + z)‖ * ‖1 + (ω : ℂ) + z‖⁻¹ ≤ C * 1 :=
      mul_le_mul (hCb _ hmem1).1 hinvlin (by positivity) hC0
    rw [mul_one] at hstep
    exact mul_le_mul hstep (hCb _ hmem2).2 (norm_nonneg _) hC0
  have hsecond : ‖1 / ((1 + (ω : ℂ)) * z * riemannZeta (1 + 2 * (ω : ℂ)))‖ ≤ 1 / δ := by
    have hrw : (1 : ℂ) / ((1 + (ω : ℂ)) * z * riemannZeta (1 + 2 * (ω : ℂ)))
        = ((1 + (ω : ℂ))⁻¹ * z⁻¹) * (riemannZeta (1 + 2 * (ω : ℂ)))⁻¹ := by
      rw [one_div, mul_inv, mul_inv]
    rw [hrw, norm_mul, norm_mul, norm_inv, norm_inv, hznorm]
    have h1 : ‖1 + (ω : ℂ)‖⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hω1
    have h2 : |τ|⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hτδ
    have h3 : ‖1 + (ω : ℂ)‖⁻¹ * |τ|⁻¹ ≤ 1 * δ⁻¹ :=
      mul_le_mul h1 h2 (by positivity) (by norm_num)
    have h4 : ‖1 + (ω : ℂ)‖⁻¹ * |τ|⁻¹ * ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖
        ≤ (1 * δ⁻¹) * 1 := mul_le_mul h3 hζinv (norm_nonneg _) (by positivity)
    calc ‖1 + (ω : ℂ)‖⁻¹ * |τ|⁻¹ * ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖
        ≤ (1 * δ⁻¹) * 1 := h4
      _ = 1 / δ := by rw [one_mul, mul_one, one_div]
  rw [mobiusCausalMultiplier]
  refine le_trans (norm_sub_le _ _) ?_
  linarith

/-- **The far-field bound for the multiplier**, in the same shape as the derivative bound. -/
theorem norm_mobiusCausalMultiplier_far_le {ω : ℝ} (hω : 0 < ω) (hω1 : 2 * ω ≤ 1)
    (hζinv : ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖ ≤ 1) {τ : ℝ} (hτ : 9 ≤ |τ|) :
    ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I)‖
      ≤ farFieldConstant * Real.log |τ| ^ 26 / |τ| := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  have hL2 : 2 < Real.log |τ| := two_lt_log_abs hτ
  have hL0 : (0 : ℝ) < Real.log |τ| := by linarith
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log |τ| := by linarith
  set z : ℂ := (τ : ℂ) * Complex.I with hzdef
  have hzim : z.im = τ := by rw [hzdef]; simp
  have hznorm : ‖z‖ = |τ| := by
    rw [hzdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hlin_lb : |τ| ≤ ‖1 + (ω : ℂ) + z‖ := by
    have h1 : |((1 : ℂ) + (ω : ℂ) + z).im| ≤ ‖1 + (ω : ℂ) + z‖ := Complex.abs_im_le_norm _
    have h2 : ((1 : ℂ) + (ω : ℂ) + z).im = τ := by simp [Complex.add_im, hzim]
    rw [h2] at h1
    exact h1
  have hlin_lb1 : (1 : ℝ) ≤ ‖1 + (ω : ℂ) + z‖ := by
    have h1 : ((1 : ℂ) + (ω : ℂ) + z).re ≤ ‖1 + (ω : ℂ) + z‖ := Complex.re_le_norm _
    have h2 : ((1 : ℂ) + (ω : ℂ) + z).re = 1 + ω := by
      rw [hzdef]; simp [Complex.add_re]
    rw [h2] at h1
    linarith
  have hω1n : (1 : ℝ) ≤ ‖1 + (ω : ℂ)‖ := by
    have h1 : ((1 : ℂ) + (ω : ℂ)).re ≤ ‖1 + (ω : ℂ)‖ := Complex.re_le_norm _
    have h2 : ((1 : ℂ) + (ω : ℂ)).re = 1 + ω := by simp [Complex.add_re]
    rw [h2] at h1
    linarith
  have hζ1 : ‖riemannZeta (1 + z)‖ ≤ Real.log |τ| + 5 := by
    have hre : ((1 : ℂ) + z).re = 1 := by rw [hzdef]; simp [Complex.add_re]
    have him : ((1 : ℂ) + z).im = τ := by simp [Complex.add_im, hzim]
    have h := norm_riemannZeta_le_log_add (s := 1 + z) (by rw [hre]) (by rw [hre]; norm_num)
      (by rw [him]; linarith)
    rwa [him] at h
  have hinv : ‖(riemannZeta (1 + 2 * (ω : ℂ) + z))⁻¹‖
      ≤ 26 / zetaLowerA * Real.log |τ| ^ 7 := norm_inv_riemannZeta_shift_le hω hω1 hτ
  have hfirst : ‖riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z))‖
      ≤ (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) := by
    have hsplit : ‖riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z))‖
        = ‖riemannZeta (1 + z)‖ * ‖1 + (ω : ℂ) + z‖⁻¹ *
          ‖(riemannZeta (1 + 2 * (ω : ℂ) + z))⁻¹‖ := by
      rw [norm_div, norm_mul, norm_inv, div_eq_mul_inv, mul_inv]
      ring
    rw [hsplit]
    have hb1 : ‖1 + (ω : ℂ) + z‖⁻¹ ≤ |τ|⁻¹ := inv_anti₀ hτ0 hlin_lb
    have hstep1 : ‖riemannZeta (1 + z)‖ * ‖1 + (ω : ℂ) + z‖⁻¹
        ≤ (Real.log |τ| + 5) * |τ|⁻¹ :=
      mul_le_mul hζ1 hb1 (by positivity) (by linarith)
    exact mul_le_mul hstep1 hinv (norm_nonneg _) (by positivity)
  have hsecond : ‖1 / ((1 + (ω : ℂ)) * z * riemannZeta (1 + 2 * (ω : ℂ)))‖ ≤ |τ|⁻¹ := by
    have hrw : (1 : ℂ) / ((1 + (ω : ℂ)) * z * riemannZeta (1 + 2 * (ω : ℂ)))
        = ((1 + (ω : ℂ))⁻¹ * z⁻¹) * (riemannZeta (1 + 2 * (ω : ℂ)))⁻¹ := by
      rw [one_div, mul_inv, mul_inv]
    rw [hrw, norm_mul, norm_mul, norm_inv, norm_inv, hznorm]
    have h1 : ‖1 + (ω : ℂ)‖⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hω1n
    have h3 : ‖1 + (ω : ℂ)‖⁻¹ * |τ|⁻¹ ≤ 1 * |τ|⁻¹ :=
      mul_le_mul h1 (le_refl _) (by positivity) (by norm_num)
    have h4 : ‖1 + (ω : ℂ)‖⁻¹ * |τ|⁻¹ * ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖
        ≤ (1 * |τ|⁻¹) * 1 := mul_le_mul h3 hζinv (norm_nonneg _) (by positivity)
    calc ‖1 + (ω : ℂ)‖⁻¹ * |τ|⁻¹ * ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖
        ≤ (1 * |τ|⁻¹) * 1 := h4
      _ = |τ|⁻¹ := by rw [one_mul, mul_one]
  have hmain : ‖mobiusCausalMultiplier ω z‖
      ≤ (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) + |τ|⁻¹ := by
    rw [mobiusCausalMultiplier]
    refine le_trans (norm_sub_le _ _) ?_
    linarith
  -- closing arithmetic
  have hL26 : (1 : ℝ) ≤ Real.log |τ| ^ 26 := one_le_pow₀ hL1
  have hstep1 : Real.log |τ| + 5 ≤ 4 * Real.log |τ| := by linarith
  have hbound : (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) + |τ|⁻¹
      ≤ farFieldConstant * Real.log |τ| ^ 26 / |τ| := by
    have hτinv : (0 : ℝ) < |τ|⁻¹ := by positivity
    have hfac1 : (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7)
        ≤ 4 * Real.log |τ| * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) := by
      have hnn : (0 : ℝ) ≤ |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) := by positivity
      nlinarith
    have hid : 4 * Real.log |τ| * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7)
        = (104 / zetaLowerA) * Real.log |τ| ^ 8 * |τ|⁻¹ := by ring
    have hpow : Real.log |τ| ^ 8 ≤ Real.log |τ| ^ 26 :=
      pow_le_pow_right₀ hL1 (by norm_num)
    have hstep2 : (104 / zetaLowerA) * Real.log |τ| ^ 8 * |τ|⁻¹
        ≤ (104 / zetaLowerA) * Real.log |τ| ^ 26 * |τ|⁻¹ := by
      have hnn : (0 : ℝ) ≤ (104 / zetaLowerA) := by positivity
      have h1 : (104 / zetaLowerA) * Real.log |τ| ^ 8 ≤ (104 / zetaLowerA) * Real.log |τ| ^ 26 :=
        mul_le_mul_of_nonneg_left hpow hnn
      exact mul_le_mul_of_nonneg_right h1 (le_of_lt hτinv)
    have hlast : |τ|⁻¹ ≤ 3 * Real.log |τ| ^ 26 * |τ|⁻¹ := by
      have h1 : (1 : ℝ) ≤ 3 * Real.log |τ| ^ 26 := by linarith
      nlinarith [hτinv]
    have hsum : farFieldConstant * Real.log |τ| ^ 26 / |τ|
        = (104 / zetaLowerA * (1 + 4496 / zetaLowerA ^ 2)) * Real.log |τ| ^ 26 * |τ|⁻¹ +
          3 * Real.log |τ| ^ 26 * |τ|⁻¹ := by
      rw [farFieldConstant, div_eq_mul_inv]
      ring
    have hmid : (104 / zetaLowerA) * Real.log |τ| ^ 26 * |τ|⁻¹
        ≤ (104 / zetaLowerA * (1 + 4496 / zetaLowerA ^ 2)) * Real.log |τ| ^ 26 * |τ|⁻¹ := by
      have hextra : (1 : ℝ) ≤ 1 + 4496 / zetaLowerA ^ 2 := by
        have hp : (0 : ℝ) < 4496 / zetaLowerA ^ 2 := by positivity
        linarith
      have hnn : (0 : ℝ) ≤ Real.log |τ| ^ 26 * |τ|⁻¹ := by positivity
      have h104 : (0 : ℝ) < 104 / zetaLowerA := by positivity
      have hcoef : (104 / zetaLowerA) ≤ (104 / zetaLowerA * (1 + 4496 / zetaLowerA ^ 2)) := by
        nlinarith
      calc (104 / zetaLowerA) * Real.log |τ| ^ 26 * |τ|⁻¹
          = (104 / zetaLowerA) * (Real.log |τ| ^ 26 * |τ|⁻¹) := by ring
        _ ≤ (104 / zetaLowerA * (1 + 4496 / zetaLowerA ^ 2)) * (Real.log |τ| ^ 26 * |τ|⁻¹) :=
            mul_le_mul_of_nonneg_right hcoef hnn
        _ = (104 / zetaLowerA * (1 + 4496 / zetaLowerA ^ 2)) * Real.log |τ| ^ 26 * |τ|⁻¹ := by
            ring
    rw [hsum]
    linarith [hid ▸ hfac1]
  linarith

/-! ### The uniform majorant and the critical limit of the multiplier -/

/-- **The uniform boundary bound for the multiplier.** -/
theorem exists_uniform_multiplier_bound :
    ∃ ω₀ K : ℝ, 0 < ω₀ ∧ 0 ≤ K ∧
      ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ → ∀ τ : ℝ, τ ≠ 0 →
        ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I)‖ ≤ boundaryMajorant K τ := by
  obtain ⟨δ, ω₀n, Cn, hδ, hω₀n, hCn, hnear⟩ := exists_near_origin_multiplier_bound
  obtain ⟨ω₂, hω₂, hinvζ⟩ := exists_inv_zeta_real_bound
  have hδ' : 0 < min δ 9 := lt_min hδ (by norm_num)
  have hω₀ : 0 < min (min ω₀n ω₂) (1 / 2 : ℝ) := lt_min (lt_min hω₀n hω₂) (by norm_num)
  obtain ⟨Cm, hCm, hmid⟩ :=
    exists_mid_range_multiplier_bound (ω₀ := min (min ω₀n ω₂) (1 / 2 : ℝ)) (δ := min δ 9) hω₀ hδ'
  refine ⟨min (min ω₀n ω₂) (1 / 2 : ℝ), max Cn Cm, hω₀, le_trans hCn (le_max_left _ _), ?_⟩
  intro ω hω hωle τ hτ
  have hωn : ω ≤ ω₀n := le_trans hωle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hω2 : ω ≤ ω₂ := le_trans hωle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hωhalf : 2 * ω ≤ 1 := by
    have : ω ≤ 1 / 2 := le_trans hωle (min_le_right _ _)
    linarith
  have hζinv := hinvζ ω hω hω2
  have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hτ
  have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
  have hznorm : ‖(τ : ℂ) * Complex.I‖ = |τ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  by_cases hcase1 : |τ| ≤ min δ 9
  · have hle : ‖(τ : ℂ) * Complex.I‖ ≤ δ := by
      rw [hznorm]
      exact le_trans hcase1 (min_le_left _ _)
    have h := hnear ω hω hωn ((τ : ℂ) * Complex.I) hzre hz0 hle
    have h9 : |τ| ≤ 9 := le_trans hcase1 (min_le_right _ _)
    rw [boundaryMajorant_near h9]
    exact le_trans h (le_max_left _ _)
  · rw [not_le] at hcase1
    by_cases hcase2 : |τ| ≤ 9
    · have h := hmid ω hω hωle hζinv τ (le_of_lt hcase1) hcase2
      rw [boundaryMajorant_near hcase2]
      exact le_trans h (le_max_right _ _)
    · rw [not_le] at hcase2
      have h := norm_mobiusCausalMultiplier_far_le hω hωhalf hζinv (le_of_lt hcase2)
      rw [boundaryMajorant_far hcase2]
      exact h

/-- **The critical limit of the multiplier, pointwise.** -/
theorem tendsto_mobiusCausalMultiplier {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    Tendsto (fun ω : ℝ => mobiusCausalMultiplier ω z) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (1 / (1 + z))) := by
  have h1z : (1 : ℂ) + z ≠ 1 := one_add_ne_one hz0
  have h1z0 : (1 : ℂ) + z ≠ 0 := one_add_ne_zero hz
  have hζ0 : riemannZeta (1 + z) ≠ 0 := riemannZeta_one_add_ne_zero hz
  have hζcont : ContinuousAt riemannZeta (1 + z) :=
    (differentiableAt_riemannZeta h1z).continuousAt
  have hshift : Tendsto (fun ω : ℝ => (1 : ℂ) + 2 * (ω : ℂ) + z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 + z)) := by
    have hc : Continuous fun ω : ℝ => (1 : ℂ) + 2 * (ω : ℂ) + z := by fun_prop
    have h0 : (1 : ℂ) + 2 * ((0 : ℝ) : ℂ) + z = 1 + z := by push_cast; ring
    have h := hc.tendsto (0 : ℝ)
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun ω : ℝ => (1 : ℂ) + (ω : ℂ) + z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 + z)) := by
    have hc : Continuous fun ω : ℝ => (1 : ℂ) + (ω : ℂ) + z := by fun_prop
    have h0 : (1 : ℂ) + ((0 : ℝ) : ℂ) + z = 1 + z := by push_cast; ring
    have h := hc.tendsto (0 : ℝ)
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hζs : Tendsto (fun ω : ℝ => riemannZeta (1 + 2 * (ω : ℂ) + z))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (riemannZeta (1 + z))) := hζcont.tendsto.comp hshift
  have hprodne : (1 + z) * riemannZeta (1 + z) ≠ 0 := mul_ne_zero h1z0 hζ0
  have hA : Tendsto (fun ω : ℝ =>
      riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)))) :=
    tendsto_const_nhds.div (hlin.mul hζs) hprodne
  have hlin2 : Tendsto (fun ω : ℝ => (1 + (ω : ℂ)) * z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds z) := by
    have hc : Continuous fun ω : ℝ => (1 + (ω : ℂ)) * z := by fun_prop
    have h0 : (1 + ((0 : ℝ) : ℂ)) * z = z := by push_cast; ring
    have h := hc.tendsto (0 : ℝ)
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun ω : ℝ => 1 / ((1 + (ω : ℂ)) * z * riemannZeta (1 + 2 * (ω : ℂ))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hinv := tendsto_inv_riemannZeta_one_add_two_mul
    have hprod := ((tendsto_const_nhds (x := (1 : ℂ))).div hlin2 hz0).mul hinv
    rw [mul_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ω hω0
    have hωpos : (0 : ℝ) < ω := hω0
    have hω1 : (1 : ℂ) + (ω : ℂ) ≠ 0 := one_add_ofReal_ne_zero hωpos
    have hζ : riemannZeta (1 + 2 * (ω : ℂ)) ≠ 0 := riemannZeta_one_add_two_mul_ne_zero hωpos
    simp only [Pi.div_apply]
    field_simp
  have hsub := hA.sub hB
  have hval : riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 0 = 1 / (1 + z) := by
    rw [sub_zero]
    field_simp
  rw [hval] at hsub
  exact hsub

theorem continuousOn_mobiusCausalMultiplier_line {ω : ℝ} (hω : 0 < ω) :
    ContinuousOn (fun τ : ℝ => mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I))
      {t : ℝ | t ≠ 0} := by
  intro τ hτ0
  have hτ : τ ≠ 0 := hτ0
  have hne1 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := line_ne_one (by simp) hτ
  have hne2 : (1 : ℂ) + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := by
    have h := line_ne_one (c := (1 : ℂ) + 2 * (ω : ℂ)) (by simp) hτ
    simpa [add_assoc] using h
  have hz : ContinuousAt (fun t : ℝ => ((t : ℂ) * Complex.I)) τ := by
    have : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I)) := by continuity
    exact this.continuousAt
  have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hτ
  have hA : ContinuousAt (fun t : ℝ => riemannZeta (1 + (t : ℂ) * Complex.I)) τ :=
    continuousAt_zeta_line hne1
  have hC : ContinuousAt (fun t : ℝ => riemannZeta (1 + 2 * (ω : ℂ) + (t : ℂ) * Complex.I)) τ := by
    have := continuousAt_zeta_line (c := (1 : ℂ) + 2 * (ω : ℂ)) (τ := τ) (by
      simpa [add_assoc] using hne2)
    simpa [add_assoc] using this
  have hlin : ContinuousAt (fun t : ℝ => 1 + (ω : ℂ) + (t : ℂ) * Complex.I) τ := by
    have := continuousAt_line ((1 : ℂ) + (ω : ℂ)) τ
    simpa [add_assoc] using this
  have hlin0 : (1 : ℂ) + (ω : ℂ) + (τ : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) + (ω : ℂ) + (τ : ℂ) * Complex.I).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero] at hre
    linarith
  have hζ0 : riemannZeta ((1 : ℂ) + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, Complex.I_re,
      Complex.I_im, mul_one]
    linarith
  have hω0 : (1 : ℂ) + (ω : ℂ) ≠ 0 := one_add_ofReal_ne_zero hω
  have hζr : riemannZeta (1 + 2 * (ω : ℂ)) ≠ 0 := riemannZeta_one_add_two_mul_ne_zero hω
  have hcont : ContinuousAt (fun t : ℝ => mobiusCausalMultiplier ω ((t : ℂ) * Complex.I)) τ := by
    have h1 : ContinuousAt (fun t : ℝ =>
        riemannZeta (1 + (t : ℂ) * Complex.I) /
          ((1 + (ω : ℂ) + (t : ℂ) * Complex.I) *
            riemannZeta (1 + 2 * (ω : ℂ) + (t : ℂ) * Complex.I))) τ :=
      hA.div (hlin.mul hC) (mul_ne_zero hlin0 hζ0)
    have h2 : ContinuousAt (fun t : ℝ =>
        1 / ((1 + (ω : ℂ)) * ((t : ℂ) * Complex.I) * riemannZeta (1 + 2 * (ω : ℂ)))) τ :=
      continuousAt_const.div ((continuousAt_const.mul hz).mul continuousAt_const)
        (mul_ne_zero (mul_ne_zero hω0 hz0) hζr)
    exact h1.sub h2
  exact hcont.continuousWithinAt

/-- **The card's `(3)` on the multiplier side.**  The coupled causal multiplier converges to
`1/(1+z)` in the boundary `L²` (i.e. `H²`) norm. -/
theorem tendsto_boundary_multiplier_energy :
    Tendsto (fun ω : ℝ => ∫ τ : ℝ, ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I) -
        1 / (1 + (τ : ℂ) * Complex.I)‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨ω₀, K, hω₀, hK, hbound⟩ := exists_uniform_multiplier_bound
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ω ∧ ω ≤ ω₀ := by
    filter_upwards [Ioc_mem_nhdsGT hω₀] with ω hω
    exact ⟨hω.1, hω.2⟩
  have hlimfun : ∀ τ : ℝ, τ ≠ 0 →
      ‖1 / (1 + (τ : ℂ) * Complex.I)‖ ≤ boundaryMajorant K τ := by
    intro τ hτ
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
    have hlim := (tendsto_mobiusCausalMultiplier hzre hz0).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [hev] with ω hω
    exact hbound ω hω.1 hω.2 τ hτ
  have hcontlim : Continuous (fun τ : ℝ => 1 / (1 + (τ : ℂ) * Complex.I)) := by
    have hne : ∀ τ : ℝ, (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 0 := by
      intro τ h
      have hre : ((1 : ℂ) + (τ : ℂ) * Complex.I).re = 0 := by rw [h]; simp
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero] at hre
      linarith
    have hc : Continuous (fun τ : ℝ => (1 : ℂ) + (τ : ℂ) * Complex.I) := by continuity
    exact continuous_const.div hc hne
  have hmeas : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (fun τ : ℝ =>
        ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I) -
          1 / (1 + (τ : ℂ) * Complex.I)‖ ^ 2) volume := by
    filter_upwards [hev] with ω hω
    have h1 := aestronglyMeasurable_of_continuousOn_ne_zero
      (continuousOn_mobiusCausalMultiplier_line hω.1)
    have h2 : AEStronglyMeasurable (fun τ : ℝ => 1 / (1 + (τ : ℂ) * Complex.I)) volume :=
      hcontlim.aestronglyMeasurable
    exact ((h1.sub h2).norm.pow 2)
  have hdom : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ᵐ τ : ℝ,
      ‖‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I) -
        1 / (1 + (τ : ℂ) * Complex.I)‖ ^ 2‖ ≤ boundaryBound K τ := by
    filter_upwards [hev] with ω hω
    filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
    have hτ : τ ≠ 0 := hτmem
    have h1 := hbound ω hω.1 hω.2 τ hτ
    have h2 := hlimfun τ hτ
    have h3 : ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I) -
        1 / (1 + (τ : ℂ) * Complex.I)‖ ≤ 2 * boundaryMajorant K τ := by
      refine le_trans (norm_sub_le _ _) ?_
      linarith
    have h4 : (0 : ℝ) ≤ ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I) -
        1 / (1 + (τ : ℂ) * Complex.I)‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), boundaryBound_eq K τ]
    calc ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I) -
          1 / (1 + (τ : ℂ) * Complex.I)‖ ^ 2
        ≤ (2 * boundaryMajorant K τ) ^ 2 := pow_le_pow_left₀ h4 h3 2
      _ = 4 * boundaryMajorant K τ ^ 2 := by ring
  have hlim : ∀ᵐ τ : ℝ, Tendsto (fun ω : ℝ =>
      ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I) - 1 / (1 + (τ : ℂ) * Complex.I)‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
    have hτ : τ ≠ 0 := hτmem
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
    have hpt := tendsto_mobiusCausalMultiplier hzre hz0
    have h := ((hpt.sub (tendsto_const_nhds
      (x := 1 / (1 + (τ : ℂ) * Complex.I)))).norm.pow 2)
    simpa using h
  have hDCT := tendsto_integral_filter_of_dominated_convergence (boundaryBound K) hmeas hdom
    (integrable_boundaryBound K) hlim
  simpa using hDCT

end

end RHTower
