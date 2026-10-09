import GaloisForLFunctions.HTGeometry.PolynomialReciprocalPowerCoordinate
import GaloisForLFunctions.HTGeometry.OrderedPolynomialRootTransport
import GaloisForLFunctions.HTGeometry.CircleRootPaths

open Polynomial Filter Topology Set Metric
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- Actual infinity chart and one large circle capturing all its polynomial root lifts. -/
structure PolynomialExteriorPowerChart {n : ℕ} (v : Parameter n) where
  chart : OpenPartialHomeomorph ℂ ℂ
  radius : ℝ
  radius_pos : 0 < radius
  source_zero : (0 : ℂ) ∈ chart.source
  chart_zero : chart 0 = 0
  analytic_source : AnalyticOnNhd ℂ chart chart.source
  analytic_inverse : AnalyticOnNhd ℂ chart.symm chart.target
  target_disk : closedBall (0 : ℂ) radius ⊆ chart.target
  reciprocal_power : ∀ w ∈ chart.source, w ≠ 0 →
    (chart w) ^ (n + 2) = ((additivePolynomial v).eval w⁻¹)⁻¹
  circle_avoid : ∀ t j, positiveCirclePath 0 (radius ^ (n + 2))⁻¹ t ≠ valuesWithConstant v j
  roots_outside : ∀ t z, (additivePolynomial v).eval z =
      positiveCirclePath 0 (radius ^ (n + 2))⁻¹ t → z ≠ 0 ∧ z⁻¹ ∈ chart.source

/-- Every actual parameter admits a large avoiding circle entirely controlled by its infinity chart. -/
theorem exists_polynomialExteriorPowerChart {n : ℕ} (v : Parameter n) :
    Nonempty (PolynomialExteriorPowerChart v) := by
  let P := additivePolynomial v
  obtain ⟨e, he0, _, hezero, hean, heinv, _, hepower⟩ :=
    exists_polynomial_reciprocal_power_coordinate (monic_additivePolynomial v)
      (by rw [natDegree_additivePolynomial]; omega) (U := univ) (by simp)
  obtain ⟨ε, hε, hεsource⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  have htarget0 : (0 : ℂ) ∈ e.target := hezero ▸ e.map_source he0
  obtain ⟨η, hη, hηtarget⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds htarget0)
  have hcompact : IsCompact ((fun z : ℂ => ‖P.eval z‖) '' closedBall 0 ε⁻¹) :=
    (isCompact_closedBall (0 : ℂ) ε⁻¹).image P.continuous.norm
  obtain ⟨M₁, hM₁⟩ := hcompact.bddAbove
  obtain ⟨M₂, hM₂⟩ := (finite_range (fun j : Fin (n + 1) => ‖valuesWithConstant v j‖)).isCompact.bddAbove
  let M := 1 + |M₁| + |M₂|
  have hM : 0 < M := by dsimp [M]; positivity
  have hM₁lt : M₁ < M := by dsimp [M]; linarith [le_abs_self M₁, abs_nonneg M₂]
  have hM₂lt : M₂ < M := by dsimp [M]; linarith [le_abs_self M₂, abs_nonneg M₁]
  have hnear : ∀ᶠ r : ℝ in 𝓝 0, r ^ (n + 2) < 1 / M := by
    have hsmall : ∀ᶠ s : ℝ in 𝓝 (0 ^ (n + 2)), s < 1 / M := by
      apply isOpen_Iio.mem_nhds
      simp only [zero_pow (by omega : n + 2 ≠ 0)]
      exact one_div_pos.mpr hM
    exact ((continuous_pow (n + 2) : Continuous (fun r : ℝ => r ^ (n + 2))).tendsto 0).eventually hsmall
  obtain ⟨δ, hδ, hδpower⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨r, hr, hrmin⟩ := exists_between (lt_min hη hδ)
  have hrη := (lt_min_iff.mp hrmin).1
  have hrδ := (lt_min_iff.mp hrmin).2
  have hrpower : r ^ (n + 2) < 1 / M := hδpower (by
    simpa [mem_ball, Real.dist_eq, abs_of_pos hr] using hrδ)
  let R := (r ^ (n + 2))⁻¹
  have hR : 0 < R := inv_pos.mpr (pow_pos hr _)
  have hMR : M < R := by
    change M < (r ^ (n + 2))⁻¹
    rw [← one_div]
    apply (lt_div_iff₀ (pow_pos hr _)).mpr
    have hm := (lt_div_iff₀ hM).mp hrpower
    nlinarith
  have hcircle : ∀ t : I, ‖positiveCirclePath 0 R t‖ = R := by
    intro t
    simp only [positiveCirclePath_apply, norm_circleMap_zero, abs_of_pos hR]
  have hav : ∀ t j, positiveCirclePath 0 R t ≠ valuesWithConstant v j := by
    intro t j h
    have hb := hM₂ ⟨j, rfl⟩
    have he : R = ‖valuesWithConstant v j‖ := (hcircle t).symm.trans (congrArg norm h)
    linarith
  have hout : ∀ t z, P.eval z = positiveCirclePath 0 R t → z ≠ 0 ∧ z⁻¹ ∈ e.source := by
    intro t z hz
    have hnorm : ε⁻¹ < ‖z‖ := by
      by_contra! hle
      have hzball : z ∈ closedBall (0 : ℂ) ε⁻¹ := by
        simpa only [mem_closedBall, dist_zero_right] using hle
      have hb := hM₁ ⟨z, hzball, rfl⟩
      have he : ‖P.eval z‖ = R := (congrArg norm hz).trans (hcircle t)
      linarith
    have hz0 : z ≠ 0 := norm_pos_iff.mp ((inv_pos.mpr hε).trans hnorm)
    refine ⟨hz0, hεsource ?_⟩
    rw [mem_ball, dist_zero_right, norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr hz0) hε).mpr hnorm
  refine ⟨{
    chart := e
    radius := r
    radius_pos := hr
    source_zero := he0
    chart_zero := hezero
    analytic_source := hean
    analytic_inverse := heinv
    target_disk := ?_
    reciprocal_power := ?_
    circle_avoid := hav
    roots_outside := hout }⟩
  · intro z hz
    exact hηtarget (lt_of_le_of_lt hz hrη)
  · simpa only [natDegree_additivePolynomial] using hepower

/-- Every root over the selected circle has nonzero infinity coordinate. -/
theorem PolynomialExteriorPowerChart.coordinate_ne_zero {n : ℕ} {v : Parameter n}
    (D : PolynomialExteriorPowerChart v) {t : I} {z : ℂ}
    (hz : (additivePolynomial v).eval z = positiveCirclePath 0 (D.radius ^ (n + 2))⁻¹ t) :
    D.chart z⁻¹ ≠ 0 := by
  obtain ⟨hz0, hzs⟩ := D.roots_outside t z hz
  intro hzero
  have hi : z⁻¹ = 0 := D.chart.injOn hzs D.source_zero (hzero.trans D.chart_zero.symm)
  exact (inv_ne_zero hz0) hi

/-- Every root over the selected circle lies on the same coordinate circle. -/
theorem PolynomialExteriorPowerChart.norm_coordinate {n : ℕ} {v : Parameter n}
    (D : PolynomialExteriorPowerChart v) {t : I} {z : ℂ}
    (hz : (additivePolynomial v).eval z = positiveCirclePath 0 (D.radius ^ (n + 2))⁻¹ t) :
    ‖D.chart z⁻¹‖ = D.radius := by
  obtain ⟨hz0, hzs⟩ := D.roots_outside t z hz
  have hp := D.reciprocal_power z⁻¹ hzs (inv_ne_zero hz0)
  simp only [inv_inv, hz] at hp
  have hn := congrArg norm hp
  simp only [norm_pow, norm_inv, positiveCirclePath_apply, norm_circleMap_zero,
    abs_of_pos (inv_pos.mpr (pow_pos D.radius_pos _)), inv_inv] at hn
  exact (pow_left_inj₀ (norm_nonneg _) D.radius_pos.le (by omega : n + 2 ≠ 0)).mp hn

/-- The infinity coordinate is injective on every root fiber over the selected circle. -/
theorem PolynomialExteriorPowerChart.coordinate_injective {n : ℕ} {v : Parameter n}
    (D : PolynomialExteriorPowerChart v) (t : I) :
    Function.Injective (fun z : RootFiber v (positiveCirclePath 0 (D.radius ^ (n + 2))⁻¹ t) =>
      D.chart (z : ℂ)⁻¹) := by
  intro z w h
  have hi := D.chart.injOn (D.roots_outside t z z.property).2
    (D.roots_outside t w w.property).2 h
  apply Subtype.ext
  exact inv_injective hi

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
