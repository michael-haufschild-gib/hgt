import GaloisForLFunctions.RHTower.ZetaSelfReturnThresholdIsTheDistanceToNonvanishingTargets

/-!
# The orbit of `ζ` approaches every analytic target with the Hurwitz threshold

Voronin universality says that `ζ(· + iτ)` approximates every target analytic and nonvanishing
near a strip disc `D = closedBall z₀ r` at positive lower density of heights, and the exclusion
law says that a target with a zero inside `D` is approximated only on a density-zero set of
heights.  This file states the complete law for an arbitrary target `h` (zeros allowed): with

  `d(h) = targetNonvanishingDistance h z₀ r`,

the uniform distance on `D` from `h` to the functions analytic and nonvanishing near `D`,

* for `ε > d(h)` the heights at which `ζ(· + iτ)` is within `ε` of `h` on `D` have positive lower
  density (`exists_pos_density_zetaTargetReturnSet_of_distance_lt`);
* for `ε < d(h)` every such height carries a zero of `ζ` in `D + iτ`
  (`exists_zero_of_mem_zetaTargetReturnSet_of_lt_distance`), so these heights lie in the zero
  shadow and have measure `≤ T^θ`, `θ < 1`, by the Ingham–Huxley zero-density estimate
  (`exists_volume_zetaTargetReturnSet_le_rpow_of_lt_distance`, through the reusable
  `exists_volume_le_rpow_of_subset_zetaZeroShadow`);
* for `h` analytic near `D` and not identically zero on the open disc, `d(h) = 0` iff `h` has no
  zero in the open disc (`targetNonvanishingDistance_eq_zero_iff`): scaled copies of `h` are
  admissible targets converging to `h` when the open disc is zero-free, while a zero inside keeps
  every admissible target away by half the minimum of `|h|` on a small circle around it.

So the approach of the orbit to any analytic target is governed by one number, the Hurwitz
distance `d(h)`: linear return measure above it, power-saving return measure below it
(`zetaTargetReturnSet_volume_dichotomy`), and `d(h) = 0` exactly for the targets without zeros
in the open disc (`exists_pos_density_zetaTargetReturnSet_iff_forall_ne_zero`).  The self-target
`h = ζ` is the special case `zetaNonvanishingDistance`.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-! ## 1. The Hurwitz distance of a target -/

/-- The admissible tolerances of a target `h`: `ε` such that some function analytic and
nonvanishing near `closedBall z₀ r` is within `ε` of `h` uniformly on the closed disc. -/
def targetNonvanishingTolerances (h : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) : Set ℝ :=
  {ε | ∃ g ∈ nonvanishingDiscTargets z₀ r, ∀ z ∈ closedBall z₀ r, ‖h z - g z‖ < ε}

/-- The Hurwitz distance of a target `h` on `closedBall z₀ r`: the infimum of its admissible
tolerances. -/
def targetNonvanishingDistance (h : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) : ℝ :=
  sInf (targetNonvanishingTolerances h z₀ r)

theorem zetaNonvanishingTolerances_eq (z₀ : ℂ) (r : ℝ) :
    zetaNonvanishingTolerances z₀ r = targetNonvanishingTolerances riemannZeta z₀ r := rfl

theorem zetaNonvanishingDistance_eq (z₀ : ℂ) (r : ℝ) :
    zetaNonvanishingDistance z₀ r = targetNonvanishingDistance riemannZeta z₀ r := rfl

theorem targetNonvanishingTolerances_upward {h : ℂ → ℂ} {z₀ : ℂ} {r ε ε' : ℝ}
    (hε : ε ∈ targetNonvanishingTolerances h z₀ r) (hle : ε ≤ ε') :
    ε' ∈ targetNonvanishingTolerances h z₀ r := by
  obtain ⟨g, hg, hc⟩ := hε
  exact ⟨g, hg, fun z hz => (hc z hz).trans_le hle⟩

theorem pos_of_mem_targetNonvanishingTolerances {h : ℂ → ℂ} {z₀ : ℂ} {r ε : ℝ} (hr : 0 ≤ r)
    (hε : ε ∈ targetNonvanishingTolerances h z₀ r) : 0 < ε := by
  obtain ⟨g, -, hc⟩ := hε
  exact (norm_nonneg _).trans_lt (hc z₀ (mem_closedBall_self hr))

theorem bddBelow_targetNonvanishingTolerances (h : ℂ → ℂ) (z₀ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    BddBelow (targetNonvanishingTolerances h z₀ r) :=
  ⟨0, fun _ hε => (pos_of_mem_targetNonvanishingTolerances hr hε).le⟩

theorem nonempty_targetNonvanishingTolerances {h : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hh : ContinuousOn h (closedBall z₀ r)) :
    (targetNonvanishingTolerances h z₀ r).Nonempty := by
  have hc : ContinuousOn (fun z => h z - 1) (closedBall z₀ r) := hh.sub continuousOn_const
  obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ r).exists_bound_of_continuousOn hc
  refine ⟨C + 1, fun _ => 1, ⟨1, one_pos, analyticOnNhd_const, fun _ _ => one_ne_zero⟩,
    fun z hz => ?_⟩
  linarith [hC z hz]

theorem targetNonvanishingDistance_nonneg (h : ℂ → ℂ) (z₀ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ targetNonvanishingDistance h z₀ r :=
  Real.sInf_nonneg fun _ hε => (pos_of_mem_targetNonvanishingTolerances hr hε).le

theorem mem_targetNonvanishingTolerances_of_distance_lt {h : ℂ → ℂ} {z₀ : ℂ} {r ε : ℝ}
    (hh : ContinuousOn h (closedBall z₀ r)) (hε : targetNonvanishingDistance h z₀ r < ε) :
    ε ∈ targetNonvanishingTolerances h z₀ r := by
  obtain ⟨ε₁, hε₁, hlt⟩ := exists_lt_of_csInf_lt (nonempty_targetNonvanishingTolerances hh) hε
  exact targetNonvanishingTolerances_upward hε₁ hlt.le

theorem not_mem_targetNonvanishingTolerances_of_lt_distance {h : ℂ → ℂ} {z₀ : ℂ} {r ε : ℝ}
    (hr : 0 ≤ r) (hε : ε < targetNonvanishingDistance h z₀ r) :
    ε ∉ targetNonvanishingTolerances h z₀ r := fun hmem =>
  absurd (csInf_le (bddBelow_targetNonvanishingTolerances h z₀ hr) hmem) (not_le.mpr hε)

/-! ## 2. Below the threshold: returns are zero shadows, hence power-saving rare -/

/-- Below the threshold, every `ε`-return height of the target carries a zero of `ζ` in the
translated closed disc. -/
theorem exists_zero_of_mem_zetaTargetReturnSet_of_lt_distance {h : ℂ → ℂ} {z₀ : ℂ} {r ε τ : ℝ}
    (hr : 0 < r) (h1 : z₀.re + r < 1) (hε : ε < targetNonvanishingDistance h z₀ r)
    (hτ : τ ∈ zetaTargetReturnSet h (closedBall z₀ r) ε) :
    ∃ z ∈ closedBall z₀ r, riemannZeta (z + τ * I) = 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = r + (1 - z₀.re - r) / 2 := ⟨_, rfl⟩
  have hrR : r < R := by rw [hR]; linarith
  have hR1 : z₀.re + R < 1 := by rw [hR]; linarith
  obtain ⟨η, hη, hηR, hne⟩ := exists_pos_ball_ne_zero_of_closedBall hrR
    (continuousOn_riemannZeta_shift_closedBall hR1 τ) hno
  apply not_mem_targetNonvanishingTolerances_of_lt_distance hr.le hε
  refine ⟨fun z => riemannZeta (z + τ * I),
    ⟨η, hη, analyticOnNhd_riemannZeta_shift (by linarith) τ, hne⟩, fun z hz => ?_⟩
  rw [norm_sub_rev]
  exact hτ z hz

/-- **Sets in the zero shadow are power-saving rare.**  If `γ + R ⊆ zetaZeroShadow σ 2` with
`½ < σ < 1`, then `|R ∩ [0, T]| ≤ T^θ` for some `θ < 1` and all large `T`. -/
theorem exists_volume_le_rpow_of_subset_zetaZeroShadow {R : Set ℝ} {σ γ₀ : ℝ} (hσ : 1 / 2 < σ)
    (hσ1 : σ < 1) (hsub : R ⊆ (fun τ => γ₀ + τ) ⁻¹' zetaZeroShadow σ 2) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume (R ∩ Icc 0 T) ≤ ENNReal.ofReal (T ^ θ) := by
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = 1 - inghamHuxleyExponent σ * (1 - σ) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; linarith [inghamHuxleyExponent_mul_lt_one hσ]
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = min 1 g := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; exact lt_min one_pos hg0
  have hε'1 : ε' ≤ 1 := by rw [hε']; exact min_le_left _ _
  obtain ⟨C, hC, B, T₁, hT₁, hshadow⟩ :=
    exists_volume_zetaZeroShadow_le_inghamHuxley hσ hσ1.le hε'0 hε'1
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (inghamHuxleyExponent σ + ε') * (1 - σ) := ⟨_, rfl⟩
  rw [← hE] at hshadow
  have hA := inghamHuxleyExponent_mem hσ
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg (by linarith [hA.1]) (by linarith)
  have hE2 : E ≤ 2 := by rw [hE]; nlinarith [hA.2]
  have hEg : E ≤ 1 - g / 2 := by
    have hεg : ε' ≤ g := by rw [hε']; exact min_le_right _ _
    have h12 : 1 - σ ≤ 1 / 2 := by linarith
    have h0' : 0 ≤ 1 - σ := by linarith
    have : ε' * (1 - σ) ≤ g / 2 := by nlinarith
    rw [hE]; nlinarith
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow B (c := g / 4) (by positivity) (12 * 2 ^ B * C))
  -- the dyadic window bound
  have hwindow : ∀ T : ℝ, max (max (2 * T₁) T₂) (max (2 * |γ₀|) 1) ≤ T →
      volume (R ∩ Icc T (2 * T)) ≤ ENNReal.ofReal (T ^ (1 - g / 4)) := by
    intro T hT
    have hT1 : 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
    have hTT₁ : 2 * T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
    have hTT₂ : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
    have hTγ : 2 * |γ₀| ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
    have hT0 : 0 < T := by linarith
    obtain ⟨W, hW⟩ : ∃ W : ℝ, W = C * (1 + Real.log (2 * T)) ^ B * (2 * T) ^ E := ⟨_, rfl⟩
    have hW0 : 0 ≤ W := by
      rw [hW]
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T)
      positivity
    have hwin : ∀ a : ℝ, T / 2 ≤ a → a ≤ 2 * T →
        volume (zetaZeroShadow σ 2 ∩ Icc a (2 * a)) ≤ ENNReal.ofReal W := fun a ha1 ha2 =>
      hW ▸ volume_window_le_of_le hC hE0 hshadow hTT₁ (by linarith) ha1 ha2
    calc volume (R ∩ Icc T (2 * T))
        ≤ _ := volume_inter_Icc_le_three_windows hsub hTγ
      _ ≤ ENNReal.ofReal W + ENNReal.ofReal W + ENNReal.ofReal W :=
          add_le_add (add_le_add (hwin _ le_rfl (by linarith)) (hwin _ (by linarith) (by linarith)))
            (hwin _ (by linarith) le_rfl)
      _ = ENNReal.ofReal (3 * W) := by
          rw [← ENNReal.ofReal_add hW0 hW0, ← ENNReal.ofReal_add (by linarith) hW0]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (T ^ (1 - g / 4)) := by
          apply ENNReal.ofReal_le_ofReal
          have hW' := three_mul_window_bound_le (B := B) hC hE2 hT1
          rw [← hW] at hW'
          have habs := hT₂ T hTT₂
          have hsplit : T ^ (g / 4) * T ^ E = T ^ (g / 4 + E) := (Real.rpow_add hT0 _ _).symm
          have hfinal : T ^ (g / 4 + E) ≤ T ^ (1 - g / 4) :=
            Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
          have hTE0 : 0 ≤ T ^ E := by positivity
          calc 3 * W ≤ 12 * 2 ^ B * C * (1 + Real.log T) ^ B * T ^ E := hW'
            _ ≤ T ^ (g / 4) * T ^ E := by gcongr
            _ = T ^ (g / 4 + E) := hsplit
            _ ≤ T ^ (1 - g / 4) := hfinal
  obtain ⟨T₀, hT₀⟩ := exists_forall_volume_inter_Icc_zero_le_rpow_of_window (by linarith)
    (le_trans (le_max_right _ _) (le_max_right _ _)) hwindow
    (show 1 - g / 4 < 1 - g / 8 by linarith)
  exact ⟨1 - g / 8, by linarith, T₀, hT₀⟩

/-- Below the threshold the target-return heights, shifted by `Im z₀`, lie in the zero shadow. -/
theorem zetaTargetReturnSet_subset_shadow_of_lt_distance {h : ℂ → ℂ} {z₀ : ℂ} {r ε : ℝ}
    (hr : 0 < r) (h1 : z₀.re + r < 1) (hr2 : r ≤ 2)
    (hε : ε < targetNonvanishingDistance h z₀ r) :
    zetaTargetReturnSet h (closedBall z₀ r) ε ⊆
      (fun τ => z₀.im + τ) ⁻¹' zetaZeroShadow (z₀.re - r) 2 := by
  intro τ hτ
  obtain ⟨z, hz, hz0⟩ := exists_zero_of_mem_zetaTargetReturnSet_of_lt_distance hr h1 hε hτ
  have hzn := mem_closedBall_iff_norm.mp hz
  have hre := abs_le.mp ((abs_re_le_norm (z - z₀)).trans hzn)
  have him := abs_le.mp ((abs_im_le_norm (z - z₀)).trans hzn)
  rw [sub_re] at hre
  rw [sub_im] at him
  refine ⟨z + τ * I, hz0, ?_, ?_⟩
  · simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    linarith [hre.1]
  · simp only [add_im, mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, add_zero]
    rw [abs_le]
    constructor <;> linarith [him.1, him.2]

/-- **Below the threshold the target returns are power-saving rare.** -/
theorem exists_volume_zetaTargetReturnSet_le_rpow_of_lt_distance {h : ℂ → ℂ} {z₀ : ℂ} {r ε : ℝ}
    (hr : 0 < r) (h0 : 1 / 2 < z₀.re - r) (h1 : z₀.re + r < 1)
    (hε : ε < targetNonvanishingDistance h z₀ r) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume (zetaTargetReturnSet h (closedBall z₀ r) ε ∩ Icc 0 T) ≤ ENNReal.ofReal (T ^ θ) :=
  exists_volume_le_rpow_of_subset_zetaZeroShadow h0 (by linarith)
    (zetaTargetReturnSet_subset_shadow_of_lt_distance hr h1 (by linarith) hε)

/-! ## 3. Above the threshold: positive density from universality -/

/-- **Above the threshold the target returns have positive lower density.** -/
theorem exists_pos_density_zetaTargetReturnSet_of_distance_lt {h : ℂ → ℂ} {z₀ : ℂ} {r ε : ℝ}
    (hr : 0 < r) (h0 : 1 / 2 < z₀.re - 2 * r) (h1 : z₀.re + 2 * r < 1)
    (hh : ContinuousOn h (closedBall z₀ r)) (hε : targetNonvanishingDistance h z₀ r < ε) :
    ∃ c > 0, ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (c * T) ≤ volume (zetaTargetReturnSet h (closedBall z₀ r) ε ∩ Icc 0 T) := by
  obtain ⟨ε₁, hε₁S, hε₁⟩ := exists_lt_of_csInf_lt (nonempty_targetNonvanishingTolerances hh) hε
  obtain ⟨g, ⟨η, hη, hg, hg0⟩, hclose⟩ := hε₁S
  obtain ⟨η', hη'⟩ : ∃ η' : ℝ, η' = min η r := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; exact lt_min hη hr
  have hη'η : η' ≤ η := by rw [hη']; exact min_le_left _ _
  have hη'r : η' ≤ r := by rw [hη']; exact min_le_right _ _
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = r + η' / 2 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℝ, R₂ = (r + η') / ρ := ⟨_, rfl⟩
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ℝ, r₁ = r / ρ := ⟨_, rfl⟩
  have hρR₂ : ρ * R₂ = r + η' := by rw [hR₂]; field_simp
  have hρr₁ : ρ * r₁ = r := by rw [hr₁]; field_simp
  have hR₂1 : 1 < R₂ := by rw [hR₂, lt_div_iff₀ hρ0, hρ]; linarith
  have hr₁0 : 0 < r₁ := by rw [hr₁]; positivity
  have hr₁1 : r₁ < 1 := by rw [hr₁, div_lt_one hρ0, hρ]; linarith
  have hball : ball z₀ (ρ * R₂) ⊆ ball z₀ (r + η) := ball_subset_ball (by rw [hρR₂]; linarith)
  obtain ⟨c, hc, hT⟩ := exists_pos_density_zetaTargetReturnSet_of_analyticOnNhd z₀ hρ0
    (by linarith) (by rw [hρ]; linarith) (by rw [hρ]; linarith) hR₂1 (hg.mono hball)
    (fun z hz => hg0 z (hball hz)) hr₁0 hr₁1 (by rw [hρr₁]; exact h0) (by rw [hρr₁]; exact h1)
    (sub_pos.mpr hε₁)
  rw [hρr₁] at hT
  refine ⟨c, hc, ?_⟩
  filter_upwards [hT] with T hT
  refine hT.trans (measure_mono (inter_subset_inter_left _ fun τ hτ z hz => ?_))
  have h1' : ‖riemannZeta (z + τ * I) - g z‖ < ε - ε₁ := hτ z hz
  have h2' := hclose z hz
  calc ‖riemannZeta (z + τ * I) - h z‖
      = ‖(riemannZeta (z + τ * I) - g z) + (g z - h z)‖ := by ring_nf
    _ ≤ ‖riemannZeta (z + τ * I) - g z‖ + ‖g z - h z‖ := norm_add_le _ _
    _ < (ε - ε₁) + ε₁ := by rw [norm_sub_rev (g z)]; exact add_lt_add h1' h2'
    _ = ε := by ring

/-- **The target-return dichotomy.**  For any target continuous on the closed disc, with doubled
closure in the strip: linear return measure above `d(h)`, at most `T^θ` below `d(h)`. -/
theorem zetaTargetReturnSet_volume_dichotomy {h : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < z₀.re - 2 * r) (h1 : z₀.re + 2 * r < 1)
    (hh : ContinuousOn h (closedBall z₀ r)) (ε : ℝ) :
    (targetNonvanishingDistance h z₀ r < ε → ∃ c > 0, ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (c * T) ≤ volume (zetaTargetReturnSet h (closedBall z₀ r) ε ∩ Icc 0 T)) ∧
    (ε < targetNonvanishingDistance h z₀ r → ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume (zetaTargetReturnSet h (closedBall z₀ r) ε ∩ Icc 0 T) ≤ ENNReal.ofReal (T ^ θ)) :=
  ⟨exists_pos_density_zetaTargetReturnSet_of_distance_lt hr h0 h1 hh,
    exists_volume_zetaTargetReturnSet_le_rpow_of_lt_distance hr (by linarith) (by linarith)⟩

/-! ## 4. The threshold vanishes exactly off the zeros of the target -/

/-- If the analytic target has no zero in the open disc, its Hurwitz distance vanishes: scaled
copies `z ↦ h(z₀ + λ(z − z₀))`, `λ ↑ 1`, are admissible and converge uniformly to `h`. -/
theorem targetNonvanishingDistance_eq_zero_of_zeroFree {h : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (hh : AnalyticOnNhd ℂ h (ball z₀ R)) (hzf : ∀ z ∈ ball z₀ r, h z ≠ 0) :
    targetNonvanishingDistance h z₀ r = 0 := by
  have hcont : ContinuousOn h (closedBall z₀ r) := fun z hz =>
    (hh z (closedBall_subset_ball hrR hz)).continuousAt.continuousWithinAt
  refine le_antisymm ?_ (targetNonvanishingDistance_nonneg h z₀ hr.le)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  rw [zero_add]
  refine lt_of_le_of_lt (csInf_le (bddBelow_targetNonvanishingTolerances h z₀ hr.le) ?_)
    (half_lt_self hε)
  have hunif := (isCompact_closedBall z₀ r).uniformContinuousOn_of_continuous hcont
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp hunif (ε / 2) (half_pos hε)
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = max (1 / 2) (1 - δ / (2 * r)) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlam1 : lam < 1 := by
    rw [hlam]
    have : 0 < δ / (2 * r) := by positivity
    exact max_lt (by norm_num) (by linarith)
  have hlamδ : (1 - lam) * r ≤ δ / 2 := by
    have h2 : 1 - lam ≤ δ / (2 * r) := by
      rw [hlam]; linarith [le_max_right (1 / 2) (1 - δ / (2 * r))]
    calc (1 - lam) * r ≤ δ / (2 * r) * r := mul_le_mul_of_nonneg_right h2 hr.le
      _ = δ / 2 := by field_simp
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, φ = fun z => z₀ + (lam : ℂ) * (z - z₀) := ⟨_, rfl⟩
  have hφdist : ∀ z, ‖φ z - z₀‖ = lam * ‖z - z₀‖ := by
    intro z
    rw [hφ]
    simp only
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam0.le]
  have hφball : ∀ z ∈ ball z₀ (r / lam), φ z ∈ ball z₀ r := by
    intro z hz
    rw [mem_ball_iff_norm] at hz ⊢
    rw [hφdist]
    calc lam * ‖z - z₀‖ < lam * (r / lam) := by gcongr
      _ = r := by field_simp
  have hφdiff : ∀ z, DifferentiableAt ℂ φ z := by
    intro z
    rw [hφ]
    exact ((differentiableAt_id.sub_const z₀).const_mul (lam : ℂ)).const_add z₀
  have hrlam : r < r / lam := by rw [lt_div_iff₀ hlam0]; nlinarith
  refine ⟨fun z => h (φ z), ⟨r / lam - r, by linarith, ?_, ?_⟩, fun z hz => ?_⟩
  · rw [show r + (r / lam - r) = r / lam by ring]
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
    have hmem := ball_subset_ball hrR.le (hφball z hz)
    exact ((hh _ hmem).differentiableAt.comp z (hφdiff z)).differentiableWithinAt
  · rw [show r + (r / lam - r) = r / lam by ring]
    exact fun z hz => hzf _ (hφball z hz)
  · have hzn := mem_closedBall_iff_norm.mp hz
    have hz' : φ z ∈ closedBall z₀ r := by
      rw [mem_closedBall_iff_norm, hφdist]
      calc lam * ‖z - z₀‖ ≤ 1 * r := by gcongr
        _ = r := one_mul r
    have hd : dist z (φ z) < δ := by
      rw [dist_eq_norm]
      have : z - φ z = ((1 - lam : ℝ) : ℂ) * (z - z₀) := by rw [hφ]; simp only; push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      calc (1 - lam) * ‖z - z₀‖ ≤ (1 - lam) * r := by gcongr
        _ ≤ δ / 2 := hlamδ
        _ < δ := half_lt_self hδ
    have := hδ' z hz (φ z) hz' hd
    rwa [dist_eq_norm] at this

/-- An analytic target that is not identically zero near a point where it vanishes has a small
circle around that point on which it is bounded away from zero. -/
theorem exists_sphere_norm_ge_of_analyticAt_of_not_eventually_zero {h : ℂ → ℂ} {w : ℂ}
    (hw : AnalyticAt ℂ h w) (hne : ¬ ∀ᶠ z in 𝓝 w, h z = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s > 0, s ≤ δ ∧ ∃ m > 0, ∀ z ∈ sphere w s, m ≤ ‖h z‖ := by
  rcases hw.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · exact absurd h0 hne
  obtain ⟨R₁, hR₁, hball⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp h0)
  obtain ⟨R₂, hR₂, han⟩ := Metric.eventually_nhds_iff_ball.mp hw.eventually_analyticAt
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min δ (min (R₁ / 2) (R₂ / 2)) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact lt_min hδ (lt_min (by linarith) (by linarith))
  have hsδ : s ≤ δ := by rw [hs]; exact min_le_left _ _
  have hsR₁ : s < R₁ := by
    rw [hs]
    linarith [min_le_left (R₁ / 2) (R₂ / 2), min_le_right δ (min (R₁ / 2) (R₂ / 2))]
  have hsR₂ : s < R₂ := by
    rw [hs]
    linarith [min_le_right (R₁ / 2) (R₂ / 2), min_le_right δ (min (R₁ / 2) (R₂ / 2))]
  have hsph : ∀ z ∈ sphere w s, h z ≠ 0 := by
    intro z hz
    have hzs := mem_sphere.mp hz
    refine hball z (by rw [mem_ball, hzs]; exact hsR₁) fun hzw => ?_
    rw [Set.mem_singleton_iff] at hzw
    rw [hzw, dist_self] at hzs
    linarith
  have hcont : ContinuousOn (fun z => ‖h z‖) (sphere w s) := fun z hz =>
    ((han z (by rw [mem_ball, mem_sphere.mp hz]; exact hsR₂)).continuousAt.norm).continuousWithinAt
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere w s).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hs0.le) hcont
  exact ⟨s, hs0, hsδ, ‖h z₁‖, norm_pos_iff.mpr (hsph z₁ hz₁), fun z hz => isMinOn_iff.mp hmin z hz⟩

/-- A zero of the analytic target in the open disc keeps its Hurwitz distance positive, provided
the target is not identically zero on the open disc. -/
theorem targetNonvanishingDistance_pos_of_zero {h : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (hh : AnalyticOnNhd ℂ h (ball z₀ R)) (hnz : ∃ z ∈ ball z₀ r, h z ≠ 0)
    {w : ℂ} (hw : w ∈ ball z₀ r) (hw0 : h w = 0) :
    0 < targetNonvanishingDistance h z₀ r := by
  have hcont : ContinuousOn h (closedBall z₀ r) := fun z hz =>
    (hh z (closedBall_subset_ball hrR hz)).continuousAt.continuousWithinAt
  -- `h` is not locally zero at `w`: otherwise it vanishes on the whole open disc
  have hne : ¬ ∀ᶠ z in 𝓝 w, h z = 0 := by
    intro hev
    obtain ⟨z₁, hz₁, hz₁0⟩ := hnz
    have hzero : Set.EqOn h 0 (ball z₀ r) :=
      (hh.mono (ball_subset_ball hrR.le)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball z₀ r).isPreconnected hw hev
    exact hz₁0 (hzero hz₁)
  have hwd : dist w z₀ < r := mem_ball.mp hw
  obtain ⟨s, hs, hsδ, m, hm0, hm⟩ := exists_sphere_norm_ge_of_analyticAt_of_not_eventually_zero
    (hh w (ball_subset_ball hrR.le hw)) hne (show 0 < r - dist w z₀ by linarith)
  have hsub : closedBall w s ⊆ closedBall z₀ r := closedBall_subset_closedBall' (by linarith)
  by_contra hd
  have hd0 : targetNonvanishingDistance h z₀ r = 0 :=
    le_antisymm (not_lt.mp hd) (targetNonvanishingDistance_nonneg h z₀ hr.le)
  obtain ⟨g, ⟨η, hη, hg, hg0⟩, hclose⟩ := mem_targetNonvanishingTolerances_of_distance_lt hcont
    (show targetNonvanishingDistance h z₀ r < m / 2 by rw [hd0]; positivity)
  have hball : closedBall z₀ r ⊆ ball z₀ (r + η) := closedBall_subset_ball (by linarith)
  have hdiff : DifferentiableOn ℂ g (closedBall w s) := fun z hz =>
    (hg z (hball (hsub hz))).differentiableAt.differentiableWithinAt
  have hsph : ∀ z ∈ sphere w s, ‖g w‖ < ‖g z‖ := by
    intro z hzs
    have h1' := hclose w (hsub (mem_closedBall_self hs.le))
    have h2' := hclose z (hsub (sphere_subset_closedBall hzs))
    have h3' := hm z hzs
    have h4 := norm_sub_norm_le (h z) (g z)
    rw [hw0, zero_sub, norm_neg] at h1'
    linarith
  obtain ⟨z, hz, hgz⟩ := DeBruijn.exists_zero_of_norm_lt_sphere_on hs hdiff hsph
  exact hg0 z (hball (hsub (ball_subset_closedBall hz))) hgz

/-- **The Hurwitz distance of an analytic target vanishes exactly off its zeros.** -/
theorem targetNonvanishingDistance_eq_zero_iff {h : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (hh : AnalyticOnNhd ℂ h (ball z₀ R)) (hnz : ∃ z ∈ ball z₀ r, h z ≠ 0) :
    targetNonvanishingDistance h z₀ r = 0 ↔ ∀ z ∈ ball z₀ r, h z ≠ 0 := by
  constructor
  · intro hd z hz hz0
    exact absurd hd (targetNonvanishingDistance_pos_of_zero hr hrR hh hnz hz hz0).ne'
  · exact targetNonvanishingDistance_eq_zero_of_zeroFree hr hrR hh

/-- **Universality with its exact threshold.**  For an analytic target `h` on a neighbourhood of
the disc, not identically zero on the open disc, with doubled closure in the strip: the orbit
approximates `h` at positive lower density for every tolerance iff `h` has no zero in the open
disc. -/
theorem exists_pos_density_zetaTargetReturnSet_iff_forall_ne_zero {h : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (h0 : 1 / 2 < z₀.re - 2 * r) (h1 : z₀.re + 2 * r < 1) (hrR : r < R)
    (hh : AnalyticOnNhd ℂ h (ball z₀ R)) (hnz : ∃ z ∈ ball z₀ r, h z ≠ 0) :
    (∀ ε > 0, ∃ c > 0, ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (c * T) ≤
      volume (zetaTargetReturnSet h (closedBall z₀ r) ε ∩ Icc 0 T)) ↔
    ∀ z ∈ ball z₀ r, h z ≠ 0 := by
  have hcont : ContinuousOn h (closedBall z₀ r) := fun z hz =>
    (hh z (closedBall_subset_ball hrR hz)).continuousAt.continuousWithinAt
  rw [← targetNonvanishingDistance_eq_zero_iff hr hrR hh hnz]
  constructor
  · intro hall
    by_contra hd
    have hd0 : 0 < targetNonvanishingDistance h z₀ r :=
      lt_of_le_of_ne (targetNonvanishingDistance_nonneg h z₀ hr.le) (Ne.symm hd)
    obtain ⟨θ, hθ, T₀, hT₀⟩ := exists_volume_zetaTargetReturnSet_le_rpow_of_lt_distance hr
      (by linarith) (by linarith) (half_lt_self hd0)
    obtain ⟨κ, hκ, hev⟩ := hall _ (half_pos hd0)
    obtain ⟨T, hT1, hT2, hT3, hT4⟩ := (hev.and ((eventually_ge_atTop T₀).and
      ((eventually_rpow_lt_const_mul_atTop hθ hκ).and (eventually_ge_atTop 0)))).exists
    have hle := hT1.trans (hT₀ T hT2)
    rw [ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hT4 θ)] at hle
    linarith
  · intro hd ε hε
    exact exists_pos_density_zetaTargetReturnSet_of_distance_lt hr h0 h1 hcont
      (by rw [hd]; exact hε)

end

end RHTower
