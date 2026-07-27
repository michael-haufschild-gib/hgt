import GaloisForLFunctions.RHTower.MobiusCausalBoundaryMajorant

/-!
# Boundary convergence of the parameter derivative and Fisher flatness

Dominated convergence on the boundary line upgrades the pointwise critical limit `(4)` to
convergence of the boundary energies:

```text
∫ ‖∂_ω M_ω(iτ) - M₀′(iτ)‖² dτ → 0        (ω → 0+),
(4ω)² ∫ ‖∂_ω M_ω(iτ)‖² dτ → 0 .
```

The first is the `H²` right differentiability of the coupled causal source at the critical
parameter; the second is the Fisher-scaled flatness — the assembled causal derivative carries no
Fisher-scale energy in the limit.
-/

open MeasureTheory Filter Topology Complex

namespace RHTower

noncomputable section

/-- The boundary majorant of the parameter derivative. -/
def boundaryMajorant (K : ℝ) (τ : ℝ) : ℝ :=
  Set.indicator boundaryNear (fun _ => K) τ +
    Set.indicator boundaryFar (fun t => farFieldConstant * Real.log |t| ^ 26 / |t|) τ

theorem boundaryMajorant_near {K τ : ℝ} (hτ : |τ| ≤ 9) :
    boundaryMajorant K τ = K := by
  have h1 : τ ∈ boundaryNear := hτ
  have h2 : τ ∉ boundaryFar := by
    intro h
    have : (9 : ℝ) < |τ| := h
    linarith
  rw [boundaryMajorant, Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]

theorem boundaryMajorant_far {K τ : ℝ} (hτ : 9 < |τ|) :
    boundaryMajorant K τ = farFieldConstant * Real.log |τ| ^ 26 / |τ| := by
  have h1 : τ ∉ boundaryNear := by
    intro h
    have : |τ| ≤ 9 := h
    linarith
  have h2 : τ ∈ boundaryFar := hτ
  rw [boundaryMajorant, Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]

theorem boundaryMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (τ : ℝ) : 0 ≤ boundaryMajorant K τ := by
  by_cases hτ : |τ| ≤ 9
  · rw [boundaryMajorant_near hτ]
    exact hK
  · rw [not_le] at hτ
    rw [boundaryMajorant_far hτ]
    have h1 : (0 : ℝ) ≤ farFieldConstant := farFieldConstant_nonneg
    have h2 : (0 : ℝ) < |τ| := by linarith
    have h3 : (0 : ℝ) ≤ Real.log |τ| := Real.log_nonneg (by linarith)
    positivity

theorem boundaryBound_eq (K τ : ℝ) :
    boundaryBound K τ = 4 * boundaryMajorant K τ ^ 2 := by
  by_cases hτ : |τ| ≤ 9
  · have h1 : τ ∈ boundaryNear := hτ
    have h2 : τ ∉ boundaryFar := by
      intro h
      have : (9 : ℝ) < |τ| := h
      linarith
    rw [boundaryBound, Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero,
      boundaryMajorant_near hτ]
  · rw [not_le] at hτ
    have h1 : τ ∉ boundaryNear := by
      intro h
      have : |τ| ≤ 9 := h
      linarith
    have h2 : τ ∈ boundaryFar := hτ
    rw [boundaryBound, Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add,
      boundaryMajorant_far hτ]

/-- **The uniform boundary bound**: the parameter derivative is dominated on the boundary line by
a fixed square-integrable majorant. -/
theorem exists_uniform_boundary_bound :
    ∃ ω₀ K : ℝ, 0 < ω₀ ∧ 0 ≤ K ∧
      ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ → ∀ τ : ℝ, τ ≠ 0 →
        ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ≤ boundaryMajorant K τ := by
  obtain ⟨δ, ω₀n, Cn, hδ, hω₀n, hCn, hnear⟩ := exists_near_origin_bound
  obtain ⟨ω₁, hω₁, hpole⟩ := exists_pole_factor_bound
  have hδ' : 0 < min δ 9 := lt_min hδ (by norm_num)
  have hω₀ : 0 < min (min ω₀n ω₁) (1 / 2 : ℝ) :=
    lt_min (lt_min hω₀n hω₁) (by norm_num)
  obtain ⟨Cm, hCm, hmid⟩ :=
    exists_mid_range_bound (ω₀ := min (min ω₀n ω₁) (1 / 2 : ℝ)) (δ := min δ 9) hω₀ hδ'
  refine ⟨min (min ω₀n ω₁) (1 / 2 : ℝ), max Cn Cm, hω₀, le_trans hCn (le_max_left _ _), ?_⟩
  intro ω hω hωle τ hτ
  have hωn : ω ≤ ω₀n := le_trans hωle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hω1 : ω ≤ ω₁ := le_trans hωle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hωhalf : 2 * ω ≤ 1 := by
    have : ω ≤ 1 / 2 := le_trans hωle (min_le_right _ _)
    linarith
  have hKω := hpole ω hω hω1
  have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hτ
  have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
  have hznorm : ‖(τ : ℂ) * Complex.I‖ = |τ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hτ0 : (0 : ℝ) < |τ| := abs_pos.2 hτ
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
    · have h := hmid ω hω hωle hKω τ (le_of_lt hcase1) hcase2
      rw [boundaryMajorant_near hcase2]
      exact le_trans h (le_max_right _ _)
    · rw [not_le] at hcase2
      have h := norm_mobiusCausalMultiplierDeriv_far_le hω hωhalf hKω (le_of_lt hcase2)
      rw [boundaryMajorant_far hcase2]
      exact h

/-! ### Measurability on the boundary line -/

theorem aestronglyMeasurable_of_continuousOn_ne_zero {f : ℝ → ℂ}
    (hf : ContinuousOn f {t : ℝ | t ≠ 0}) : AEStronglyMeasurable f volume := by
  have hmeas : MeasurableSet {t : ℝ | t ≠ 0} := (measurableSet_singleton (0 : ℝ)).compl
  have h := hf.aestronglyMeasurable (μ := volume) hmeas
  have hae : ∀ᵐ t : ℝ, t ∈ {t : ℝ | t ≠ 0} := by
    rw [ae_iff]
    have hset : {t : ℝ | ¬(t ∈ {t : ℝ | t ≠ 0})} = {(0 : ℝ)} := by
      ext t
      simp
    rw [hset]
    exact Real.volume_singleton
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h

theorem continuousAt_line (c : ℂ) (τ : ℝ) :
    ContinuousAt (fun t : ℝ => c + (t : ℂ) * Complex.I) τ := by
  have : Continuous (fun t : ℝ => c + (t : ℂ) * Complex.I) := by
    continuity
  exact this.continuousAt

theorem continuousAt_zeta_line {c : ℂ} {τ : ℝ} (h : c + (τ : ℂ) * Complex.I ≠ 1) :
    ContinuousAt (fun t : ℝ => riemannZeta (c + (t : ℂ) * Complex.I)) τ := by
  have h1 : ContinuousAt riemannZeta (c + (τ : ℂ) * Complex.I) :=
    (differentiableAt_riemannZeta h).continuousAt
  exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => c + (t : ℂ) * Complex.I)
    h1 (continuousAt_line c τ)

theorem continuousAt_deriv_zeta_line {c : ℂ} {τ : ℝ} (h : c + (τ : ℂ) * Complex.I ≠ 1) :
    ContinuousAt (fun t : ℝ => deriv riemannZeta (c + (t : ℂ) * Complex.I)) τ := by
  have hana : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
    have hdiffOn : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
      intro s hs
      exact (differentiableAt_riemannZeta (by simpa using hs)).differentiableWithinAt
    exact hdiffOn.analyticOnNhd isOpen_compl_singleton
  have hmem : c + (τ : ℂ) * Complex.I ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using h
  have h1 : ContinuousAt (deriv riemannZeta) (c + (τ : ℂ) * Complex.I) :=
    (hana _ hmem).deriv.continuousAt
  exact ContinuousAt.comp (g := deriv riemannZeta) (f := fun t : ℝ => c + (t : ℂ) * Complex.I)
    h1 (continuousAt_line c τ)

theorem line_ne_one {c : ℂ} (hc : c.im = 0) {τ : ℝ} (hτ : τ ≠ 0) :
    c + (τ : ℂ) * Complex.I ≠ 1 := by
  intro h
  have him : (c + (τ : ℂ) * Complex.I).im = (1 : ℂ).im := by rw [h]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, zero_add, Complex.one_im, hc] at him
  exact hτ (by linarith [him])

theorem continuousOn_mobiusCausalMultiplierDeriv_line {ω : ℝ} (hω : 0 < ω) :
    ContinuousOn (fun τ : ℝ => mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I))
      {t : ℝ | t ≠ 0} := by
  intro τ hτ0
  have hτ : τ ≠ 0 := hτ0
  have hne1 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := line_ne_one (by simp) hτ
  have hne2 : (1 : ℂ) + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := by
    have h := line_ne_one (c := (1 : ℂ) + 2 * (ω : ℂ)) (by simp) hτ
    simpa [add_assoc] using h
  -- the pieces
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
  have hD : ContinuousAt
      (fun t : ℝ => deriv riemannZeta (1 + 2 * (ω : ℂ) + (t : ℂ) * Complex.I)) τ := by
    have := continuousAt_deriv_zeta_line (c := (1 : ℂ) + 2 * (ω : ℂ)) (τ := τ) (by
      simpa [add_assoc] using hne2)
    simpa [add_assoc] using this
  have hlin : ContinuousAt (fun t : ℝ => 1 + (ω : ℂ) + (t : ℂ) * Complex.I) τ := by
    have := continuousAt_line ((1 : ℂ) + (ω : ℂ)) τ
    simpa [add_assoc] using this
  have hlin0 : (1 : ℂ) + (ω : ℂ) + (τ : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) + (ω : ℂ) + (τ : ℂ) * Complex.I).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero] at hre
    linarith
  have hζ0 : riemannZeta ((1 : ℂ) + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, Complex.I_re,
      Complex.I_im, mul_one]
    linarith
  have hcont : ContinuousAt
      (fun t : ℝ => mobiusCausalMultiplierDeriv ω ((t : ℂ) * Complex.I)) τ := by
    have h1 : ContinuousAt (fun t : ℝ =>
        riemannZeta (1 + (t : ℂ) * Complex.I) /
          ((1 + (ω : ℂ) + (t : ℂ) * Complex.I) *
            riemannZeta (1 + 2 * (ω : ℂ) + (t : ℂ) * Complex.I))) τ :=
      hA.div (hlin.mul hC) (mul_ne_zero hlin0 hζ0)
    have h2 : ContinuousAt (fun t : ℝ =>
        -(1 / (1 + (ω : ℂ) + (t : ℂ) * Complex.I)) -
          2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + (t : ℂ) * Complex.I) /
            riemannZeta (1 + 2 * (ω : ℂ) + (t : ℂ) * Complex.I)) τ :=
      ((continuousAt_const.div hlin hlin0).neg).sub ((continuousAt_const.mul hD).div hC hζ0)
    have h3 : ContinuousAt (fun t : ℝ =>
        1 / ((t : ℂ) * Complex.I) *
          ((riemannZeta (1 + 2 * (ω : ℂ)) +
              2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
            ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2)) τ :=
      (continuousAt_const.div hz hz0).mul continuousAt_const
    exact ((h1.mul h2).add h3)
  exact hcont.continuousWithinAt

theorem continuousOn_mobiusCausalFlatDeriv_line :
    ContinuousOn (fun τ : ℝ => mobiusCausalFlatDeriv ((τ : ℂ) * Complex.I)) {t : ℝ | t ≠ 0} := by
  intro τ hτ0
  have hτ : τ ≠ 0 := hτ0
  have hne1 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := line_ne_one (by simp) hτ
  have hz : ContinuousAt (fun t : ℝ => ((t : ℂ) * Complex.I)) τ := by
    have : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I)) := by continuity
    exact this.continuousAt
  have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hτ
  have hlin : ContinuousAt (fun t : ℝ => 1 + (t : ℂ) * Complex.I) τ := continuousAt_line 1 τ
  have hlin0 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) + (τ : ℂ) * Complex.I).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero] at hre
    linarith
  have hA : ContinuousAt (fun t : ℝ => riemannZeta (1 + (t : ℂ) * Complex.I)) τ :=
    continuousAt_zeta_line hne1
  have hD : ContinuousAt (fun t : ℝ => deriv riemannZeta (1 + (t : ℂ) * Complex.I)) τ :=
    continuousAt_deriv_zeta_line hne1
  have hζ0 : riemannZeta ((1 : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
    linarith
  have hcont : ContinuousAt (fun t : ℝ => mobiusCausalFlatDeriv ((t : ℂ) * Complex.I)) τ := by
    have h1 : ContinuousAt (fun t : ℝ => -(1 / (1 + (t : ℂ) * Complex.I) ^ 2)) τ :=
      (continuousAt_const.div (hlin.pow 2) (pow_ne_zero 2 hlin0)).neg
    have h2 : ContinuousAt (fun t : ℝ =>
        2 * deriv riemannZeta (1 + (t : ℂ) * Complex.I) /
          ((1 + (t : ℂ) * Complex.I) * riemannZeta (1 + (t : ℂ) * Complex.I))) τ :=
      (continuousAt_const.mul hD).div (hlin.mul hA) (mul_ne_zero hlin0 hζ0)
    have h3 : ContinuousAt (fun t : ℝ => 2 / ((t : ℂ) * Complex.I)) τ :=
      continuousAt_const.div hz hz0
    exact (h1.sub h2).sub h3
  exact hcont.continuousWithinAt

/-! ### Boundary convergence and Fisher flatness -/

/-- **The card's `(9)`.**  The boundary derivatives converge in the `H²` (boundary `L²`) norm. -/
theorem tendsto_boundary_deriv_energy :
    Tendsto (fun ω : ℝ => ∫ τ : ℝ, ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I) -
        mobiusCausalFlatDeriv ((τ : ℂ) * Complex.I)‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨ω₀, K, hω₀, hK, hbound⟩ := exists_uniform_boundary_bound
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ω ∧ ω ≤ ω₀ := by
    filter_upwards [Ioc_mem_nhdsGT hω₀] with ω hω
    exact ⟨hω.1, hω.2⟩
  -- the flat derivative obeys the same majorant
  have hflat : ∀ τ : ℝ, τ ≠ 0 →
      ‖mobiusCausalFlatDeriv ((τ : ℂ) * Complex.I)‖ ≤ boundaryMajorant K τ := by
    intro τ hτ
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
    have hlim := (tendsto_mobiusCausalMultiplierDeriv hzre hz0).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [hev] with ω hω
    exact hbound ω hω.1 hω.2 τ hτ
  have hmeas : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (fun τ : ℝ =>
        ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I) -
          mobiusCausalFlatDeriv ((τ : ℂ) * Complex.I)‖ ^ 2) volume := by
    filter_upwards [hev] with ω hω
    have h1 := aestronglyMeasurable_of_continuousOn_ne_zero
      (continuousOn_mobiusCausalMultiplierDeriv_line hω.1)
    have h2 := aestronglyMeasurable_of_continuousOn_ne_zero
      continuousOn_mobiusCausalFlatDeriv_line
    exact ((h1.sub h2).norm.pow 2)
  have hdom : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ᵐ τ : ℝ,
      ‖‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I) -
        mobiusCausalFlatDeriv ((τ : ℂ) * Complex.I)‖ ^ 2‖ ≤ boundaryBound K τ := by
    filter_upwards [hev] with ω hω
    filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
    have hτ : τ ≠ 0 := hτmem
    have h1 := hbound ω hω.1 hω.2 τ hτ
    have h2 := hflat τ hτ
    have h3 : ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I) -
        mobiusCausalFlatDeriv ((τ : ℂ) * Complex.I)‖ ≤ 2 * boundaryMajorant K τ := by
      refine le_trans (norm_sub_le _ _) ?_
      linarith
    have h4 : (0 : ℝ) ≤ ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I) -
        mobiusCausalFlatDeriv ((τ : ℂ) * Complex.I)‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), boundaryBound_eq K τ]
    calc ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I) -
          mobiusCausalFlatDeriv ((τ : ℂ) * Complex.I)‖ ^ 2
        ≤ (2 * boundaryMajorant K τ) ^ 2 := by
          exact pow_le_pow_left₀ h4 h3 2
      _ = 4 * boundaryMajorant K τ ^ 2 := by ring
  have hlim : ∀ᵐ τ : ℝ, Tendsto (fun ω : ℝ =>
      ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I) -
        mobiusCausalFlatDeriv ((τ : ℂ) * Complex.I)‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
    have hτ : τ ≠ 0 := hτmem
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
    have hpt := tendsto_mobiusCausalMultiplierDeriv hzre hz0
    have h := ((hpt.sub (tendsto_const_nhds
      (x := mobiusCausalFlatDeriv ((τ : ℂ) * Complex.I)))).norm.pow 2)
    simpa using h
  have hDCT := tendsto_integral_filter_of_dominated_convergence (boundaryBound K) hmeas hdom
    (integrable_boundaryBound K) hlim
  simpa using hDCT

theorem boundaryBound_nonneg (K τ : ℝ) : 0 ≤ boundaryBound K τ := by
  rw [boundaryBound_eq K τ]
  positivity

/-- The boundary energy of the parameter derivative is bounded uniformly near the critical
parameter. -/
theorem integrable_boundary_deriv_sq {ω₀ K : ℝ}
    (hbound : ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ → ∀ τ : ℝ, τ ≠ 0 →
      ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ≤ boundaryMajorant K τ)
    {ω : ℝ} (hω : 0 < ω) (hωle : ω ≤ ω₀) :
    Integrable (fun τ : ℝ => ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2) := by
  refine Integrable.mono (integrable_boundaryBound K) ?_ ?_
  · exact ((aestronglyMeasurable_of_continuousOn_ne_zero
      (continuousOn_mobiusCausalMultiplierDeriv_line hω)).norm.pow 2)
  · filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
    have hτ : τ ≠ 0 := hτmem
    have h1 := hbound ω hω hωle τ hτ
    have h2 : (0 : ℝ) ≤ ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ := norm_nonneg _
    have hsq : ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2
        ≤ boundaryMajorant K τ ^ 2 := pow_le_pow_left₀ h2 h1 2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (boundaryBound_nonneg K τ), boundaryBound_eq K τ]
    nlinarith [sq_nonneg (boundaryMajorant K τ)]

/-- **The card's `(10)`--`(11)`: Fisher-scaled causal flatness.**  With `ε = σ-1 = 2ω` and
`∂_σ = ∂_ω/2`, the scaled derivative `4ε ∂_σ = 4ω ∂_ω` carries no boundary energy in the limit. -/
theorem tendsto_fisher_scaled_boundary_energy :
    Tendsto (fun ω : ℝ => (4 * ω) ^ 2 *
        ∫ τ : ℝ, ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨ω₀, K, hω₀, hK, hbound⟩ := exists_uniform_boundary_bound
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ω ∧ ω ≤ ω₀ := by
    filter_upwards [Ioc_mem_nhdsGT hω₀] with ω hω
    exact ⟨hω.1, hω.2⟩
  have hE0 : (0 : ℝ) ≤ ∫ τ : ℝ, boundaryBound K τ :=
    integral_nonneg fun τ => boundaryBound_nonneg K τ
  have hupper : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (4 * ω) ^ 2 * ∫ τ : ℝ, ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2
        ≤ (4 * ω) ^ 2 * ∫ τ : ℝ, boundaryBound K τ := by
    filter_upwards [hev] with ω hω
    have hint := integrable_boundary_deriv_sq hbound hω.1 hω.2
    have hmono : (∫ τ : ℝ, ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2)
        ≤ ∫ τ : ℝ, boundaryBound K τ := by
      refine integral_mono_ae hint (integrable_boundaryBound K) ?_
      filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
      have hτ : τ ≠ 0 := hτmem
      have h1 := hbound ω hω.1 hω.2 τ hτ
      have h2 : (0 : ℝ) ≤ ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ := norm_nonneg _
      have hsq : ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2
          ≤ boundaryMajorant K τ ^ 2 := pow_le_pow_left₀ h2 h1 2
      have hbb : boundaryBound K τ = 4 * boundaryMajorant K τ ^ 2 := boundaryBound_eq K τ
      show ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2 ≤ boundaryBound K τ
      rw [hbb]
      nlinarith [sq_nonneg (boundaryMajorant K τ)]
    have hpos : (0 : ℝ) ≤ (4 * ω) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hmono hpos
  have hlower : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (0 : ℝ) ≤ (4 * ω) ^ 2 * ∫ τ : ℝ, ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2 := by
    filter_upwards [hev] with ω hω
    have hnn : (0 : ℝ) ≤ ∫ τ : ℝ, ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2 :=
      integral_nonneg fun τ => by positivity
    positivity
  have hzero : Tendsto (fun ω : ℝ => (4 * ω) ^ 2 * ∫ τ : ℝ, boundaryBound K τ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous (fun ω : ℝ => (4 * ω) ^ 2 * ∫ τ : ℝ, boundaryBound K τ) := by
      continuity
    have h := hc.tendsto (0 : ℝ)
    have h0 : (4 * (0 : ℝ)) ^ 2 * (∫ τ : ℝ, boundaryBound K τ) = 0 := by norm_num
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero hlower hupper

end

end RHTower
