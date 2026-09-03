import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarConstrainedSmoothCore

/-!
# Continuity of the pole-vanishing ground energy of the restricted Weil form

The pole-vanishing ground energy `μ₀(a)` is the infimum of the Rayleigh quotients of the exact
CCM restricted Weil form over nonzero pole-vanishing form-domain vectors at the aperture `a`.
It is well defined (a nonzero pole-vanishing smooth source exists, and the unconstrained ground
energy is a lower bound), antitone in the aperture, right continuous by the constrained floor
theorem of `CCMRestrictedWeilPolarConstrainedRightContinuity`, and left continuous because a
pole-vanishing near-minimizer can be taken smooth with compact support strictly inside the
aperture (constrained smooth-core density) and then restricted to every slightly smaller
aperture with the same Rayleigh quotient and the same vanishing pole coefficients.

This is Suzuki's continuity theorem (arXiv:2606.09096, Theorem 1.3) on the subspace where the
literature's positivity results at the aperture `√2` live.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

/-- Rayleigh quotients of nonzero pole-vanishing form-domain vectors. -/
def polarRayleighSet (a : SuzukiPositiveAperture) : Set ℝ :=
  {r | ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
    ccmArchimedeanFormToAperture a u ≠ 0 ∧
    r = ccmRestrictedWeilSourceQuadratic a u / ‖ccmArchimedeanFormToAperture a u‖ ^ 2}

/-- The pole-vanishing ground energy. -/
noncomputable def ccmRestrictedWeilPolarGroundEnergy (a : SuzukiPositiveAperture) : ℝ :=
  sInf (polarRayleighSet a)

theorem polarRayleighSet_nonempty (a : SuzukiPositiveAperture) : (polarRayleighSet a).Nonempty := by
  obtain ⟨g, hg, hne⟩ := exists_polarConstrained_smooth_ne_zero a
  exact ⟨_, g.toCCMFormVector, hg, hne, rfl⟩

theorem ccmRestrictedWeilGroundEnergy_mem_lowerBounds (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilGroundEnergy a ∈ lowerBounds (polarRayleighSet a) := by
  rintro r ⟨u, -, hne, rfl⟩
  have hpos : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    have := norm_pos_iff.mpr hne
    positivity
  rw [le_div_iff₀ hpos]
  exact ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u

theorem polarRayleighSet_bddBelow (a : SuzukiPositiveAperture) : BddBelow (polarRayleighSet a) :=
  ⟨_, ccmRestrictedWeilGroundEnergy_mem_lowerBounds a⟩

/-- The unconstrained ground energy is a lower bound for the pole-vanishing one. -/
theorem ccmRestrictedWeilGroundEnergy_le_polar (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilGroundEnergy a ≤ ccmRestrictedWeilPolarGroundEnergy a :=
  le_csInf (polarRayleighSet_nonempty a) (ccmRestrictedWeilGroundEnergy_mem_lowerBounds a)

theorem ccmRestrictedWeilPolarGroundEnergy_le_rayleigh (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (hne : ccmArchimedeanFormToAperture a u ≠ 0) :
    ccmRestrictedWeilPolarGroundEnergy a ≤
      ccmRestrictedWeilSourceQuadratic a u / ‖ccmArchimedeanFormToAperture a u‖ ^ 2 :=
  csInf_le (polarRayleighSet_bddBelow a) ⟨u, hu, hne, rfl⟩

/-- **The constrained Rayleigh floor.** -/
theorem ccmRestrictedWeilPolarGroundEnergy_mul_le (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) :
    ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  by_cases hne : ccmArchimedeanFormToAperture a u = 0
  · have hu0 : u = 0 := ccmArchimedeanFormToAperture_injective a (by rw [hne, map_zero])
    rw [hne, norm_zero, hu0, ccmRestrictedWeilSourceQuadratic_zero]
    simp
  · have hpos : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
      have := norm_pos_iff.mpr hne
      positivity
    have := ccmRestrictedWeilPolarGroundEnergy_le_rayleigh a u hu hne
    rwa [le_div_iff₀ hpos] at this

/-- A floor on constrained vectors is below the pole-vanishing ground energy. -/
theorem le_ccmRestrictedWeilPolarGroundEnergy_of_floor (a : SuzukiPositiveAperture) {m : ℝ}
    (hm : ∀ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u →
      m * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a u) :
    m ≤ ccmRestrictedWeilPolarGroundEnergy a := by
  refine le_csInf (polarRayleighSet_nonempty a) ?_
  rintro r ⟨u, hu, hne, rfl⟩
  have hpos : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    have := norm_pos_iff.mpr hne
    positivity
  rw [le_div_iff₀ hpos]
  exact hm u hu

/-- **Antitone in the aperture.** -/
theorem ccmRestrictedWeilPolarGroundEnergy_antitone {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) :
    ccmRestrictedWeilPolarGroundEnergy b ≤ ccmRestrictedWeilPolarGroundEnergy a := by
  refine le_csInf (polarRayleighSet_nonempty a) ?_
  rintro r ⟨u, hu, hne, rfl⟩
  obtain ⟨v, hvu⟩ := exists_ccmArchimedeanFormDomain_extension hab u
  have hv : IsPolarConstrained b v := (isPolarConstrained_iff_of_val_eq hab hvu).mpr hu
  have hvne : ccmArchimedeanFormToAperture b v ≠ 0 := by
    intro h0
    apply hne
    have := norm_ccmArchimedeanFormToAperture_eq_of_val_eq hvu
    rw [h0, norm_zero] at this
    exact norm_eq_zero.mp this.symm
  have := ccmRestrictedWeilPolarGroundEnergy_le_rayleigh b v hv hvne
  rwa [norm_ccmArchimedeanFormToAperture_eq_of_val_eq hvu,
    ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab hvu] at this

/-- **Right continuity along the canonical right apertures.** -/
theorem tendsto_ccmRestrictedWeilPolarGroundEnergy_suzukiRightAperture
    (a : SuzukiPositiveAperture) :
    Tendsto (fun n => ccmRestrictedWeilPolarGroundEnergy (suzukiRightAperture a n)) atTop
      (𝓝 (ccmRestrictedWeilPolarGroundEnergy a)) := by
  have hmono : Monotone
      (fun n => ccmRestrictedWeilPolarGroundEnergy (suzukiRightAperture a n)) := by
    intro m n hmn
    exact ccmRestrictedWeilPolarGroundEnergy_antitone (antitone_suzukiRightAperture a hmn)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_polarConstrained_floor_suzukiRightAperture a
    (ccmRestrictedWeilPolarGroundEnergy_mul_le a) (half_pos hε)
  have hk' : ccmRestrictedWeilPolarGroundEnergy a - ε / 2 ≤
      ccmRestrictedWeilPolarGroundEnergy (suzukiRightAperture a k) :=
    le_ccmRestrictedWeilPolarGroundEnergy_of_floor _ hk
  refine ⟨k, fun n hkn => ?_⟩
  have hlower : ccmRestrictedWeilPolarGroundEnergy a - ε / 2 ≤
      ccmRestrictedWeilPolarGroundEnergy (suzukiRightAperture a n) :=
    hk'.trans (hmono hkn)
  have hupper : ccmRestrictedWeilPolarGroundEnergy (suzukiRightAperture a n) ≤
      ccmRestrictedWeilPolarGroundEnergy a :=
    ccmRestrictedWeilPolarGroundEnergy_antitone (suzukiRightAperture_gt a n).le
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

/-- A pole-vanishing smooth strict-interior near-minimizer. -/
theorem exists_polarConstrained_smooth_rayleigh_lt (a : SuzukiPositiveAperture) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧
        ccmArchimedeanFormToAperture a g.toCCMFormVector ≠ 0 ∧
        ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector /
            ‖ccmArchimedeanFormToAperture a g.toCCMFormVector‖ ^ 2 <
          ccmRestrictedWeilPolarGroundEnergy a + ε := by
  obtain ⟨r, ⟨u, hu, hne, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (polarRayleighSet_nonempty a)
    (show sInf (polarRayleighSet a) < ccmRestrictedWeilPolarGroundEnergy a + ε / 2 by
      unfold ccmRestrictedWeilPolarGroundEnergy; linarith)
  -- continuity of the Rayleigh quotient at `u`
  let R : CCMArchimedeanFormDomain a → ℝ := fun v =>
    ccmRestrictedWeilSourceQuadratic a v / ‖ccmArchimedeanFormToAperture a v‖ ^ 2
  have hnorm0 : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≠ 0 := by
    have := norm_pos_iff.mpr hne
    positivity
  have hR : ContinuousAt R u := by
    refine ContinuousAt.div (continuous_ccmRestrictedWeilSourceQuadratic a).continuousAt ?_ hnorm0
    exact ((continuous_norm.comp (ccmArchimedeanFormToAperture a).continuous).pow 2).continuousAt
  have hN : ContinuousAt (fun v : CCMArchimedeanFormDomain a =>
      ‖ccmArchimedeanFormToAperture a v‖) u :=
    (continuous_norm.comp (ccmArchimedeanFormToAperture a).continuous).continuousAt
  obtain ⟨δ₁, hδ₁, hR'⟩ := Metric.continuousAt_iff.1 hR (ε / 2) (by linarith)
  have hnpos : 0 < ‖ccmArchimedeanFormToAperture a u‖ := norm_pos_iff.mpr hne
  obtain ⟨δ₂, hδ₂, hN'⟩ := Metric.continuousAt_iff.1 hN
    (‖ccmArchimedeanFormToAperture a u‖) hnpos
  obtain ⟨g, hg, hclose⟩ := exists_polarConstrained_smooth_close a u hu
    (lt_min hδ₁ hδ₂)
  have hdist : dist g.toCCMFormVector u < min δ₁ δ₂ := by
    rw [dist_eq_norm]; exact hclose
  have hgne : ccmArchimedeanFormToAperture a g.toCCMFormVector ≠ 0 := by
    intro h0
    have := hN' (lt_of_lt_of_le hdist (min_le_right _ _))
    rw [Real.dist_eq, h0, norm_zero, zero_sub, abs_neg, abs_of_pos hnpos] at this
    exact lt_irrefl _ this
  refine ⟨g, hg, hgne, ?_⟩
  have h1 := hR' (lt_of_lt_of_le hdist (min_le_left _ _))
  rw [Real.dist_eq] at h1
  have h2 := abs_lt.mp h1
  show R g.toCCMFormVector < _
  linarith [h2.2]

/-- **Left continuity.** -/
theorem exists_left_aperture_polarGroundEnergy_upper (a : SuzukiPositiveAperture) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ b : SuzukiPositiveAperture, b.1 < a.1 ∧
      ∀ c : SuzukiPositiveAperture, b.1 ≤ c.1 → c.1 ≤ a.1 →
        ccmRestrictedWeilPolarGroundEnergy c < ccmRestrictedWeilPolarGroundEnergy a + ε := by
  obtain ⟨g, hg, hgne, hgR⟩ := exists_polarConstrained_smooth_rayleigh_lt a hε
  obtain ⟨b, hba, hsupp⟩ := exists_strict_smaller_aperture_of_compact_tsupport a g
  refine ⟨b, hba, fun c hbc hca => ?_⟩
  have hsuppc : tsupport (g : ℝ → ℂ) ⊆ Ioo (-c.1) c.1 := by
    refine hsupp.trans ?_
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  let gc := g.restrictAperture c hsuppc
  have hval : g.toCCMFormVector.1 = gc.toCCMFormVector.1 :=
    (CCMComplexSmoothInteriorSource.restrictAperture_toCCMFormVector_val g c hsuppc).symm
  have hgc : IsPolarConstrained c gc.toCCMFormVector :=
    (isPolarConstrained_iff_of_val_eq hca hval).mp hg
  have hgcne : ccmArchimedeanFormToAperture c gc.toCCMFormVector ≠ 0 := by
    intro h0
    apply hgne
    have := norm_ccmArchimedeanFormToAperture_eq_of_val_eq hval
    rw [h0, norm_zero] at this
    exact norm_eq_zero.mp this
  have := ccmRestrictedWeilPolarGroundEnergy_le_rayleigh c gc.toCCMFormVector hgc hgcne
  rw [← norm_ccmArchimedeanFormToAperture_eq_of_val_eq hval,
    ← ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hca hval] at this
  exact lt_of_le_of_lt this hgR

/-- **Continuity of the pole-vanishing ground energy in the aperture** (Suzuki 2026, Theorem
1.3, on the pole-vanishing subspace). -/
theorem continuousAt_ccmRestrictedWeilPolarGroundEnergy (a : SuzukiPositiveAperture) :
    ContinuousAt ccmRestrictedWeilPolarGroundEnergy a := by
  refine Metric.continuousAt_iff.2 fun ε hε => ?_
  obtain ⟨b, hba, hleft⟩ := exists_left_aperture_polarGroundEnergy_upper a hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (tendsto_ccmRestrictedWeilPolarGroundEnergy_suzukiRightAperture a) ε hε
  let r := suzukiRightAperture a N
  have har : a.1 < r.1 := suzukiRightAperture_gt a N
  let δ := min (a.1 - b.1) (r.1 - a.1)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hba) (sub_pos.mpr har)
  refine ⟨δ, hδ, fun c hc => ?_⟩
  change dist c.1 a.1 < δ at hc
  rw [Real.dist_eq] at hc
  have hcLeft : b.1 < c.1 := by
    have hdist : |c.1 - a.1| < a.1 - b.1 := lt_of_lt_of_le hc (min_le_left _ _)
    linarith [neg_le_abs (c.1 - a.1)]
  have hcRight : c.1 < r.1 := by
    have hdist : |c.1 - a.1| < r.1 - a.1 := lt_of_lt_of_le hc (min_le_right _ _)
    linarith [le_abs_self (c.1 - a.1)]
  rw [Real.dist_eq, abs_lt]
  rcases le_or_gt c.1 a.1 with hca | hac
  · have h1 := hleft c hcLeft.le hca
    have h2 := ccmRestrictedWeilPolarGroundEnergy_antitone hca
    constructor <;> linarith
  · have h1 := ccmRestrictedWeilPolarGroundEnergy_antitone hac.le
    have h2 := ccmRestrictedWeilPolarGroundEnergy_antitone hcRight.le
    have h3 := hN N le_rfl
    rw [Real.dist_eq, abs_lt] at h3
    constructor <;> linarith [h3.1, h3.2]

/-- **Strict positivity of the pole-vanishing ground energy is an open condition.** -/
theorem eventually_ccmRestrictedWeilPolarGroundEnergy_pos {a : SuzukiPositiveAperture}
    (ha : 0 < ccmRestrictedWeilPolarGroundEnergy a) :
    ∀ᶠ c in 𝓝 a, 0 < ccmRestrictedWeilPolarGroundEnergy c :=
  (continuousAt_ccmRestrictedWeilPolarGroundEnergy a).eventually (lt_mem_nhds ha)

end RHTower
