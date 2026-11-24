import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Lines

/-! # The transition from absent Fourier lines to isometric divisor splitting -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology MeasureTheory

private theorem overlaps_nonempty (x t : ℝ) : (finiteFactorOverlaps x t).Nonempty := by
  rw [finiteFactorOverlaps_eq]
  exact ⟨_,∅,visibility_mem ∅ (box_exact ∅ 1) (box_supported ∅ 1) _⟩

/-- The equal-time wave overlaps itself on every factor, at every damping. -/
theorem finiteOverlapFloor_zero_time (x : ℝ) : finiteOverlapFloor x 0 = 1 := by
  have he : ∀ v ∈ finiteFactorOverlaps x 0, v = 1 := by
    rintro v ⟨A,B,h,rfl⟩
    exact overlap_at_zero h x
  obtain ⟨v,hv⟩ := overlaps_nonempty x 0
  have hset : finiteFactorOverlaps x 0 = {1} := by
    ext u
    constructor
    · exact fun hu => he u hu
    · rintro (rfl : u = 1)
      rwa [he v hv] at hv
  rw [finiteOverlapFloor,hset,csInf_singleton]

theorem finiteOverlapFloor_below {x t : ℝ} (hx : 0 < x) (hb : x ≤ 1/2) (ht : t ≠ 0) :
    finiteOverlapFloor x t = 0 := by
  have he := finite_overlap_infimum hx ht
  rw [if_neg (not_lt_of_ge hb)] at he
  exact he.csInf_eq (overlaps_nonempty x t)

/-- Below and at the threshold the single surviving time has measure zero in every Fourier average. -/
theorem overlapCoefficient_below {x : ℝ} (hx : 0 < x) (hb : x ≤ 1/2) (ω : ℝ) :
    overlapCoefficient x ω = 0 := by
  let f := fun t : ℝ => (finiteOverlapFloor x t : ℂ)^2 * bohrChar ω t
  have ht : Tendsto (windowAverage f) atTop (𝓝 0) := by
    apply (tendsto_const_nhds (x := (0:ℂ))).congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    have hi : (∫ t in (0:ℝ)..T, f t) = ∫ _ in (0:ℝ)..T, (0:ℂ) := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le hT] at ht
      simp [f,finiteOverlapFloor_below hx hb ht.1.ne']
    simp [windowAverage,hi]
  have hex : ∃ M, Tendsto (windowAverage f) atTop (𝓝 M) := ⟨0,ht⟩
  change bohrMean f = 0
  rw [bohrMean,dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec ht

/-- The constant Fourier line is present exactly in the square-summable wave regime. -/
theorem overlapCoefficient_zero_ne_iff {x : ℝ} (hx : 0 < x) :
    overlapCoefficient x 0 ≠ 0 ↔ 1/2 < x := by
  refine ⟨fun hn => lt_of_not_ge (fun hb => hn (overlapCoefficient_below hx hb 0)),overlapCoefficient_zero_ne⟩

/-- For every complex split parameter, the boundary of the measured constant line detects norm preservation. -/
theorem constant_line_tests_composition (s : ℂ) :
    (overlapCoefficient s.re 0 = 0 ∧ ∀ ε : ℝ, 0 < ε → overlapCoefficient (s.re+ε) 0 ≠ 0) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f q, T f q = split s f q := by
  rw [split_isometric_iff]
  have hz := overlapCoefficient_below (by positivity : (0:ℝ) < 1/2) le_rfl 0
  constructor
  · rintro ⟨hzero,hopen⟩
    apply le_antisymm (le_of_not_gt (fun h => overlapCoefficient_zero_ne h hzero))
    by_contra! hlt
    have hn := hopen (1/2-s.re) (sub_pos.mpr hlt)
    rw [show s.re+(1/2-s.re) = 1/2 by ring] at hn
    exact hn hz
  · intro hs
    rw [hs]
    exact ⟨hz,fun ε he => overlapCoefficient_zero_ne (lt_add_of_pos_right _ he)⟩

#print axioms finiteOverlapFloor_zero_time
#print axioms finiteOverlapFloor_below
#print axioms overlapCoefficient_below
#print axioms overlapCoefficient_zero_ne_iff
#print axioms constant_line_tests_composition

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
