import GaloisForLFunctions.HTGeometry.TranscendentalEntireOrderOne
import GaloisForLFunctions.Bottcher.EntirePolyGrowth
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The Casorati–Weierstrass dichotomy at infinity

A function holomorphic on a neighbourhood `{R < ‖z‖}` of infinity either has polynomial growth there
or has dense image on every neighbourhood of infinity.

If the image of `{R' < ‖z‖}` misses a disc `B(w₀, ε)`, the function `u ↦ 1/(g(1/u) - w₀)` is bounded
by `1/ε` on a punctured disc, so it extends holomorphically across `0`.  The extension does not
vanish identically, so it has a zero of finite order `n` at `0`; hence `|g(z) - w₀| ≤ C |z|^n` near
infinity.

For an entire function polynomial growth means being a polynomial, so a transcendental entire
function has dense image on every neighbourhood of infinity.
-/

open Filter Topology Metric Set

namespace GaloisForLFunctions.HTGeometry

/-- **Casorati–Weierstrass at infinity.** -/
theorem polyBound_or_dense_image {g : ℂ → ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g {z | R < ‖z‖}) :
    (∃ (C : ℝ) (n : ℕ) (R' : ℝ), ∀ z : ℂ, R' < ‖z‖ → ‖g z‖ ≤ C * ‖z‖ ^ n) ∨
      ∀ R' : ℝ, Dense (g '' {z | R' < ‖z‖}) := by
  by_cases hd : ∀ R' : ℝ, Dense (g '' {z | R' < ‖z‖})
  · exact Or.inr hd
  left
  push Not at hd
  obtain ⟨R', hR'⟩ := hd
  rw [Metric.dense_iff] at hR'
  push Not at hR'
  obtain ⟨w₀, ε, hε, hmiss⟩ := hR'
  set R₁ := max R' (max R 0) + 1 with hR₁
  have hR₁pos : 0 < R₁ := by positivity
  have hfar : ∀ z : ℂ, R₁ < ‖z‖ → ε ≤ ‖g z - w₀‖ := by
    intro z hz
    by_contra hlt
    push Not at hlt
    have hz' : R' < ‖z‖ := lt_of_le_of_lt (by rw [hR₁]; linarith [le_max_left R' (max R 0)]) hz
    have : g z ∈ ball w₀ ε ∩ g '' {z | R' < ‖z‖} :=
      ⟨by rw [mem_ball, dist_eq_norm]; exact hlt, mem_image_of_mem g hz'⟩
    rw [hmiss] at this
    exact this
  -- the reciprocal at the origin
  set h : ℂ → ℂ := fun u => 1 / (g u⁻¹ - w₀) with hh
  set ρ : ℝ := 1 / R₁ with hρ
  have hρpos : 0 < ρ := by positivity
  have hmemfar : ∀ u : ℂ, u ∈ ball (0 : ℂ) ρ \ {0} → R₁ < ‖u⁻¹‖ := by
    intro u hu
    have hu0 : u ≠ 0 := hu.2
    have hu1 : ‖u‖ < ρ := by simpa using hu.1
    rw [norm_inv]
    have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    rw [hρ] at hu1
    rw [lt_inv_comm₀ hR₁pos hupos]
    simpa using hu1
  have hdiff : DifferentiableOn ℂ h (ball (0 : ℂ) ρ \ {0}) := by
    intro u hu
    have hfar' := hmemfar u hu
    have hRR₁ : R ≤ R₁ := by
      have h1 := le_max_left R 0
      have h2 := le_max_right R' (max R 0)
      rw [hR₁]; linarith
    have hR : R < ‖u⁻¹‖ := lt_of_le_of_lt hRR₁ hfar'
    have hgd : DifferentiableAt ℂ g u⁻¹ :=
      hg.differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hR)
    have hne : g u⁻¹ - w₀ ≠ 0 := by
      intro h0
      have := hfar _ hfar'
      rw [h0, norm_zero] at this
      linarith
    exact ((((hgd.comp u (differentiableAt_inv hu.2)).sub_const w₀).inv hne).const_mul
      (1 : ℂ) |>.congr_of_eventuallyEq (Eventually.of_forall fun v => by simp [hh])).differentiableWithinAt
  have hbdd : BddAbove (norm ∘ h '' (ball (0 : ℂ) ρ \ {0})) := by
    refine ⟨1 / ε, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    simp only [Function.comp_apply, hh, one_div, norm_inv]
    exact inv_anti₀ hε (hfar _ (hmemfar u hu))
  set H := Function.update h 0 ((𝓝[≠] (0 : ℂ)).limUnder h) with hH
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) ρ) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hρpos) hdiff hbdd
  have hHa : AnalyticAt ℂ H 0 :=
    hHd.analyticAt (ball_mem_nhds 0 hρpos)
  have hHne : ∀ u : ℂ, u ∈ ball (0 : ℂ) ρ \ {0} → H u ≠ 0 := by
    intro u hu
    rw [hH, Function.update_of_ne hu.2]
    simp only [hh, one_div, ne_eq, inv_eq_zero]
    intro h0
    have := hfar _ (hmemfar u hu)
    rw [h0, norm_zero] at this
    linarith
  have hnot : ¬ ∀ᶠ u in 𝓝 (0 : ℂ), H u = 0 := by
    intro hev
    obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff_ball.mp hev
    set u : ℂ := ((min r ρ / 2 : ℝ) : ℂ) with hu
    have hupos : 0 < min r ρ / 2 := by positivity
    have hunorm : ‖u‖ = min r ρ / 2 := by
      rw [hu, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hupos]
    have hur : u ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_zero_right, hunorm]
      linarith [min_le_left r ρ]
    have huρ : u ∈ ball (0 : ℂ) ρ \ {0} := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_zero_right, hunorm]; linarith [min_le_right r ρ]
      · intro h0; rw [mem_singleton_iff] at h0; rw [h0, norm_zero] at hunorm; linarith
    exact hHne u huρ (hsub u hur)
  obtain ⟨n, k, hka, hk0, hHeq⟩ := hHa.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnot
  -- a lower bound for `H` near `0`
  have hkev : ∀ᶠ u in 𝓝 (0 : ℂ), ‖k 0‖ / 2 ≤ ‖k u‖ := by
    have hc := hka.continuousAt.norm
    have : ∀ᶠ u in 𝓝 (0 : ℂ), ‖k 0‖ / 2 < ‖k u‖ :=
      hc.eventually (lt_mem_nhds (by linarith [norm_pos_iff.mpr hk0]))
    filter_upwards [this] with u hu using hu.le
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff_ball.mp (hHeq.and hkev)
  set c := ‖k 0‖ / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith [norm_pos_iff.mpr hk0]
  set R₂ := max (1 / min δ ρ) 1 with hR₂
  refine ⟨‖w₀‖ + 1 / c, n, R₂, fun z hz => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz.le
  have hzpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hmin : 0 < min δ ρ := lt_min hδ hρpos
  have hzinv : ‖z⁻¹‖ < min δ ρ := by
    rw [norm_inv]
    have : 1 / min δ ρ < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
    rw [inv_lt_comm₀ hzpos hmin]
    simpa using this
  have hzδ : z⁻¹ ∈ ball (0 : ℂ) δ := by
    rw [mem_ball, dist_zero_right]; exact lt_of_lt_of_le hzinv (min_le_left _ _)
  have hzρ : z⁻¹ ∈ ball (0 : ℂ) ρ \ {0} := by
    refine ⟨?_, by simpa using hz0⟩
    rw [mem_ball, dist_zero_right]; exact lt_of_lt_of_le hzinv (min_le_right _ _)
  obtain ⟨hHz, hkz⟩ := hδsub _ hzδ
  have hHval : H z⁻¹ = 1 / (g z - w₀) := by
    rw [hH, Function.update_of_ne hzρ.2, hh]
    simp
  have hlower : c * ‖z‖⁻¹ ^ n ≤ ‖H z⁻¹‖ := by
    rw [hHz, sub_zero, norm_smul, norm_pow, norm_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left hkz (by positivity)
  rw [hHval, one_div, norm_inv] at hlower
  have hgpos : 0 < ‖g z - w₀‖ := by
    have := hfar z (lt_of_le_of_lt (by
      have h1 : R₁ = 1 / ρ := by rw [hρ]; field_simp
      have h2 : 1 / ρ ≤ 1 / min δ ρ := one_div_le_one_div_of_le hmin (min_le_right _ _)
      linarith [le_max_left (1 / min δ ρ) 1]) hz)
    linarith
  have hupper : ‖g z - w₀‖ ≤ ‖z‖ ^ n / c := by
    rw [inv_pow] at hlower
    have hpos1 : 0 < c * (‖z‖ ^ n)⁻¹ := by positivity
    have := inv_anti₀ hpos1 hlower
    rw [inv_inv, mul_inv, inv_inv] at this
    calc ‖g z - w₀‖ ≤ c⁻¹ * ‖z‖ ^ n := this
      _ = ‖z‖ ^ n / c := by ring
  have hzn1 : 1 ≤ ‖z‖ ^ n := one_le_pow₀ hz1
  calc ‖g z‖ ≤ ‖w₀‖ + ‖g z - w₀‖ := by
        calc ‖g z‖ = ‖w₀ + (g z - w₀)‖ := by ring_nf
          _ ≤ ‖w₀‖ + ‖g z - w₀‖ := norm_add_le _ _
    _ ≤ ‖w₀‖ * ‖z‖ ^ n + ‖z‖ ^ n / c := by nlinarith [norm_nonneg w₀]
    _ = (‖w₀‖ + 1 / c) * ‖z‖ ^ n := by ring

/-- **A transcendental entire function has dense image near infinity.** -/
theorem dense_image_of_transcendentalEntire {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    (R : ℝ) : Dense (f '' {z | R < ‖z‖}) := by
  rcases polyBound_or_dense_image (R := 0) (hf.1.differentiableOn) with
    ⟨C, n, R', hbound⟩ | hd
  · exfalso
    apply hf.2
    -- a global polynomial bound from the bound near infinity and compactness
    set R₀ := max R' 1 with hR₀
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R₀).exists_bound_of_continuousOn
      hf.1.continuous.continuousOn
    refine Bottcher.exists_polynomial_of_entire_polyGrowth (C := max C 0 * R₀ ^ n + max B 0)
      (n := n) hf.1 fun z => ?_
    have hmax1 : 1 ≤ max 1 ‖z‖ := le_max_left _ _
    have hpow1 : 1 ≤ (max 1 ‖z‖) ^ n := one_le_pow₀ hmax1
    have hR₀0 : (0 : ℝ) ≤ R₀ := by rw [hR₀]; positivity
    have hC0 : 0 ≤ max C 0 * R₀ ^ n := mul_nonneg (le_max_right _ _) (pow_nonneg hR₀0 n)
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    by_cases hz : ‖z‖ ≤ R₀
    · have hfz := hB z (by rw [mem_closedBall, dist_zero_right]; exact hz)
      calc ‖f z‖ ≤ max B 0 := hfz.trans (le_max_left _ _)
        _ ≤ max C 0 * R₀ ^ n + max B 0 := by linarith
        _ = (max C 0 * R₀ ^ n + max B 0) * 1 := by ring
        _ ≤ (max C 0 * R₀ ^ n + max B 0) * (max 1 ‖z‖) ^ n :=
          mul_le_mul_of_nonneg_left hpow1 (by linarith)
    · push Not at hz
      have hzR' : R' < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
      have h1 := hbound z hzR'
      have hz1 : 1 < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
      have hmaxz : max 1 ‖z‖ = ‖z‖ := max_eq_right hz1.le
      rw [hmaxz]
      have hR₀1 : 1 ≤ R₀ ^ n := one_le_pow₀ (le_max_right _ _)
      have hzn : 0 ≤ ‖z‖ ^ n := by positivity
      calc ‖f z‖ ≤ C * ‖z‖ ^ n := h1
        _ ≤ max C 0 * ‖z‖ ^ n := mul_le_mul_of_nonneg_right (le_max_left _ _) hzn
        _ = max C 0 * 1 * ‖z‖ ^ n := by ring
        _ ≤ max C 0 * R₀ ^ n * ‖z‖ ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR₀1 (le_max_right _ _)) hzn
        _ ≤ (max C 0 * R₀ ^ n + max B 0) * ‖z‖ ^ n :=
          mul_le_mul_of_nonneg_right (by linarith) hzn
  · exact hd R

end GaloisForLFunctions.HTGeometry
