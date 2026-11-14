import GaloisForLFunctions.HTGeometry.ComplexAnalysis.BallPowerMass
import GaloisForLFunctions.HTGeometry.AnalyticRootFactor

/-!
# Strong unique continuation for entire functions in the local L² sense

A nonzero entire function factors at each point as a finite power times an analytic unit.
The unit is bounded below on a small disk, so the local squared mass has a positive polynomial
lower bound. Consequently infinite-order local L² vanishing forces the function to vanish
identically. This is the zero-potential case of strong unique continuation for `∂̄`.

Local mass is written in the translated coordinate `a+z`. Natural inverse powers suffice in
the flatness definition, since they are cofinal among all positive real inverse powers.
-/

open Complex MeasureTheory Filter Topology Set Metric

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Infinite-order local squared-mass vanishing at a point. -/
def L2FlatAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∀ k : ℕ, Tendsto
    (fun r : ℝ => (∫ z in ball (0 : ℂ) r, ‖f (a + z)‖ ^ 2) / r ^ k)
    (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- A nonzero entire function has a positive power-law lower bound for its local squared mass. -/
theorem exists_power_lower_mass_of_entire {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ z, f z ≠ 0) :
    ∃ (k : ℕ) (c δ : ℝ), 0 < c ∧ 0 < δ ∧
      ∀ r : ℝ, 0 < r → r < δ →
        c * r ^ k ≤ ∫ z in ball (0 : ℂ) r, ‖f z‖ ^ 2 := by
  have hlocal : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 := by
    intro hz
    obtain ⟨w, hw⟩ := hne
    exact hw (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ 0) hz (mem_univ w))
  obtain ⟨m, g, hg, hg0, hfac⟩ := exists_pow_factor_of_root hf (mem_univ 0) hlocal
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr
    fun z => (hg z (mem_univ z)).continuousAt
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr
    fun z => (hf z (mem_univ z)).continuousAt
  have hgnorm : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hnear : {z : ℂ | ‖g 0‖ / 2 < ‖g z‖} ∈ 𝓝 0 :=
    (isOpen_lt continuous_const hgcont.norm).mem_nhds (by simpa using half_lt_self hgnorm)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨2 * m + 2, (‖g 0‖ / 2) ^ 2 * Real.pi / (m + 1), δ,
    by positivity, hδ, ?_⟩
  intro r hr hrδ
  have hintf : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball (0 : ℂ) r) :=
    ((hfcont.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  have hintg : IntegrableOn (fun z : ℂ => (‖g 0‖ / 2) ^ 2 * ‖z‖ ^ (2 * m))
      (ball (0 : ℂ) r) :=
    ((continuous_const.mul (continuous_norm.pow _)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  have hle : (∫ z in ball (0 : ℂ) r, (‖g 0‖ / 2) ^ 2 * ‖z‖ ^ (2 * m)) ≤
      ∫ z in ball (0 : ℂ) r, ‖f z‖ ^ 2 := by
    apply integral_mono_ae hintg hintf
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hgz : ‖g 0‖ / 2 ≤ ‖g z‖ := le_of_lt (hsub (ball_subset_ball hrδ.le hz))
    rw [hfac z (mem_univ z), sub_zero, norm_mul, norm_pow, mul_pow, ← pow_mul,
      Nat.mul_comm m 2]
    rw [mul_comm (‖z‖ ^ (2 * m))]
    gcongr
  rw [integral_const_mul,
    integral_ball_norm_even_pow m ⟨r, hr.le⟩] at hle
  convert hle using 1 <;> ring

/-- Infinite-order local L² vanishing annihilates an entire function. -/
theorem eq_zero_of_entire_l2FlatAt {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {a : ℂ} (hflat : L2FlatAt f a) :
    f = 0 := by
  by_contra hne
  have hsome : ∃ z, f (a + z) ≠ 0 := by
    by_contra hn
    apply hne
    funext w
    have hz := not_exists.mp hn (w - a)
    simpa only [add_sub_cancel, not_not, Pi.zero_apply] using hz
  have hshift : AnalyticOnNhd ℂ (fun z => f (a + z)) univ := by
    intro z _
    exact (hf (a + z) (mem_univ _)).comp (analyticAt_const.add analyticAt_id)
  obtain ⟨k, c, δ, hc, hδ, hbound⟩ := exists_power_lower_mass_of_entire hshift hsome
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < δ :=
    nhdsWithin_le_nhds (eventually_lt_nhds hδ)
  have hle : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      c ≤ (∫ z in ball (0 : ℂ) r, ‖f (a + z)‖ ^ 2) / r ^ k := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrδ
    exact (le_div_iff₀ (pow_pos hr k)).mpr (hbound r hr hrδ)
  have hc0 : c ≤ 0 := le_of_tendsto (hflat k) hle
  exact (not_le_of_gt hc) hc0

/-- For entire functions, local L² flatness at any point is equivalent to global vanishing. -/
theorem l2FlatAt_iff_eq_zero_of_entire {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (a : ℂ) : L2FlatAt f a ↔ f = 0 := by
  constructor
  · exact eq_zero_of_entire_l2FlatAt hf
  · rintro rfl k
    simpa only [Pi.zero_apply, norm_zero, zero_pow two_ne_zero,
      integral_zero, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))

end GaloisForLFunctions.HTGeometry
