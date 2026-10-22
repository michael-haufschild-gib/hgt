import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundEnergy
import GaloisForLFunctions.RHTower.Suzuki.SuzukiSmallApertureGroundEnergy

/-!
# Attainment of the pole-vanishing ground energy and the degeneracy threshold

The pole-vanishing ground energy `μ₀(a)` of the exact CCM restricted Weil form is attained by a
normalized pole-vanishing vector (compactness of the form embedding, no boundary escape needed
at a fixed aperture, closed sublevel sets, and injectivity of the embedding to identify the limit
across levels).  Combined with the corpus's small-aperture positivity of the full form, the
antitone continuity of `μ₀` yields the **degeneracy threshold law**: either `μ₀ > 0` at every
aperture, or there is a unique threshold aperture `a*` with `μ₀ > 0` below it, `μ₀(a*) = 0`, and
`μ₀ ≤ 0` above it; at `a*` the form is nonnegative on the pole-vanishing subspace and has a
normalized pole-vanishing null vector.  This is the pole-vanishing form of the Yoshida–Suzuki
degeneracy corollary, on the subspace where the literature's `√2` positivity lives.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

/-- Normalized pole-vanishing near-minimizers. -/
theorem exists_polarConstrained_normalized_near_min (a : SuzukiPositiveAperture) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧
      ccmRestrictedWeilSourceQuadratic a u < ccmRestrictedWeilPolarGroundEnergy a + ε := by
  obtain ⟨r, ⟨v, hv, hne, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (polarRayleighSet_nonempty a)
    (show sInf (polarRayleighSet a) < ccmRestrictedWeilPolarGroundEnergy a + ε by
      unfold ccmRestrictedWeilPolarGroundEnergy; linarith)
  have hr0 : 0 < ‖ccmArchimedeanFormToAperture a v‖ := norm_pos_iff.mpr hne
  refine ⟨((‖ccmArchimedeanFormToAperture a v‖ : ℂ)⁻¹) • v, hv.smul _, ?_, ?_⟩
  · rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact inv_mul_cancel₀ hr0.ne'
  · rw [ccmRestrictedWeilSourceQuadratic_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, inv_pow]
    have hpos : 0 < ‖ccmArchimedeanFormToAperture a v‖ ^ (2 : ℕ) := pow_pos hr0 2
    rw [inv_mul_lt_iff₀ hpos]
    have := hr
    rw [div_lt_iff₀ hpos] at this
    linarith

/-- **Attainment of the pole-vanishing ground energy.** -/
theorem exists_polarConstrained_groundState (a : SuzukiPositiveAperture) :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧
      ccmRestrictedWeilSourceQuadratic a u = ccmRestrictedWeilPolarGroundEnergy a := by
  have hseq : ∀ n : ℕ, ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧
      ccmRestrictedWeilSourceQuadratic a u <
        ccmRestrictedWeilPolarGroundEnergy a + 1 / ((n : ℝ) + 1) := fun n =>
    exists_polarConstrained_normalized_near_min a (by positivity)
  choose u huc hun huQ using hseq
  set μ := ccmRestrictedWeilPolarGroundEnergy a with hμ
  -- bounded form norm
  let radius := Real.sqrt (max 0 (μ + 1 + ‖ccmRestrictedWeilBoundedRemainder a‖))
  have hbound : ∀ n, ‖u n‖ ≤ radius := by
    intro n
    have hb := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass a (u n)
    rw [hun n] at hb
    simp only [one_pow, mul_one] at hb
    have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsq : ‖(u n).1‖ ^ (2 : ℕ) ≤ max 0 (μ + 1 + ‖ccmRestrictedWeilBoundedRemainder a‖) :=
      hb.trans (le_max_of_le_right (by linarith [huQ n]))
    have hnonneg : 0 ≤ max 0 (μ + 1 + ‖ccmRestrictedWeilBoundedRemainder a‖) := le_max_left _ _
    have hsqrt : 0 ≤ radius := Real.sqrt_nonneg _
    change ‖(u n).1‖ ≤ radius
    nlinarith [Real.sq_sqrt hnonneg, norm_nonneg (u n).1, hsqrt]
  have hmem : ∀ n, ccmArchimedeanFormToAperture a (u n) ∈
      closure (ccmArchimedeanFormToAperture a '' Metric.closedBall
        (0 : CCMArchimedeanFormDomain a) radius) := by
    intro n
    apply subset_closure
    refine ⟨u n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbound n
  obtain ⟨fstar, -, phi, hphi, hconv⟩ :=
    (isCompactOperator_ccmArchimedeanFormToAperture a
      |>.isCompact_closure_image_closedBall radius).tendsto_subseq hmem
  -- unit norm
  have hnorm : ‖fstar‖ = 1 := by
    have h1 : Tendsto (fun n => ‖ccmArchimedeanFormToAperture a (u (phi n))‖) atTop
        (𝓝 ‖fstar‖) := (continuous_norm.tendsto fstar).comp hconv
    have h2 : Tendsto (fun n => ‖ccmArchimedeanFormToAperture a (u (phi n))‖) atTop (𝓝 1) := by
      simp only [hun]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- constrained limit
  have hlimc : ∀ s : ℝ, (∀ k, inner ℂ (ccmPolarApertureVector a s)
      (ccmArchimedeanFormToAperture a (u k)) = 0) →
      inner ℂ (ccmPolarApertureVector a s) fstar = 0 := by
    intro s hs
    have h1 : Tendsto (fun n => inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (u (phi n)))) atTop
        (𝓝 (inner ℂ (ccmPolarApertureVector a s) fstar)) :=
      (continuous_const.inner continuous_id).tendsto fstar |>.comp hconv
    have h2 : Tendsto (fun n => inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (u (phi n)))) atTop (𝓝 0) := by
      simp only [hs]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- sublevel membership at every level
  have hlevel : ∀ k : ℕ, ∃ w : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormToAperture a w = fstar ∧
        ccmRestrictedWeilSourceQuadratic a w ≤ μ + 1 / ((k : ℝ) + 1) := by
    intro k
    refine (isClosed_ccmRestrictedWeilSource_sublevel a (μ + 1 / ((k : ℝ) + 1))).mem_of_tendsto
      hconv ?_
    rw [Filter.eventually_atTop]
    refine ⟨k, fun n hn => ⟨u (phi n), rfl, ?_⟩⟩
    have hφ : (k : ℝ) ≤ (phi n : ℝ) := by
      exact_mod_cast hn.trans (hphi.id_le n)
    have h1 : 1 / ((phi n : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith [huQ (phi n)]
  obtain ⟨w, hwJ, -⟩ := hlevel 0
  have hwQ : ccmRestrictedWeilSourceQuadratic a w ≤ μ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨w', hw'J, hw'Q⟩ := hlevel k
    have hww : w' = w := ccmArchimedeanFormToAperture_injective a (by rw [hw'J, hwJ])
    rw [hww] at hw'Q
    linarith
  have hwc : IsPolarConstrained a w := by
    unfold IsPolarConstrained
    rw [hwJ]
    exact ⟨hlimc _ fun k => (huc k).1, hlimc _ fun k => (huc k).2⟩
  have hwn : ‖ccmArchimedeanFormToAperture a w‖ = 1 := by rw [hwJ, hnorm]
  refine ⟨w, hwc, hwn, le_antisymm hwQ ?_⟩
  have := ccmRestrictedWeilPolarGroundEnergy_mul_le a w hwc
  rw [hwn, one_pow, mul_one] at this
  exact this

/-! ## The degeneracy threshold -/

theorem exists_small_aperture_polarGroundEnergy_pos :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : SuzukiPositiveAperture, a.1 < δ →
      0 < ccmRestrictedWeilPolarGroundEnergy a := by
  obtain ⟨δ, hδ, h⟩ := exists_suzukiSmallAperture_ccmGroundEnergy_pos
  exact ⟨δ, hδ, fun a ha => lt_of_lt_of_le (h a ha) (ccmRestrictedWeilGroundEnergy_le_polar a)⟩

theorem continuous_ccmRestrictedWeilPolarGroundEnergy :
    Continuous ccmRestrictedWeilPolarGroundEnergy :=
  continuous_iff_continuousAt.mpr continuousAt_ccmRestrictedWeilPolarGroundEnergy

/-- **The degeneracy threshold.**  If the pole-vanishing ground energy is nonpositive at some
aperture, there is a unique threshold `a*` at which it vanishes, with strict positivity below and
nonpositivity above. -/
theorem exists_polar_degeneracy_threshold {b : SuzukiPositiveAperture}
    (hb : ccmRestrictedWeilPolarGroundEnergy b ≤ 0) :
    ∃ astar : SuzukiPositiveAperture,
      ccmRestrictedWeilPolarGroundEnergy astar = 0 ∧
      (∀ c : SuzukiPositiveAperture, c.1 < astar.1 → 0 < ccmRestrictedWeilPolarGroundEnergy c) ∧
      (∀ c : SuzukiPositiveAperture, astar.1 < c.1 → ccmRestrictedWeilPolarGroundEnergy c ≤ 0) := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_aperture_polarGroundEnergy_pos
  -- the real-variable extension of `μ₀`, constant below `δ/2`
  have hhalf : 0 < δ / 2 := by positivity
  let ap : ℝ → SuzukiPositiveAperture := fun t => ⟨max t (δ / 2), lt_max_of_lt_right hhalf⟩
  have hap : Continuous ap := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_id.max continuous_const
  let F : ℝ → ℝ := fun t => ccmRestrictedWeilPolarGroundEnergy (ap t)
  have hF : Continuous F := continuous_ccmRestrictedWeilPolarGroundEnergy.comp hap
  let T : Set ℝ := {t | F t ≤ 0}
  have hTclosed : IsClosed T := isClosed_le hF continuous_const
  have hbT : b.1 ∈ T := by
    show ccmRestrictedWeilPolarGroundEnergy (ap b.1) ≤ 0
    have hb' : ap b.1 = b := by
      apply Subtype.ext
      show max b.1 (δ / 2) = b.1
      rw [max_eq_left]
      by_contra hlt
      push Not at hlt
      have := hsmall b (by linarith)
      linarith
    rw [hb']
    exact hb
  have hTbdd : δ ∈ lowerBounds T := by
    intro t ht
    by_contra hlt
    push Not at hlt
    have hpos : 0 < ccmRestrictedWeilPolarGroundEnergy (ap t) := by
      apply hsmall
      show max t (δ / 2) < δ
      exact max_lt hlt (by linarith)
    exact absurd ht (not_le.mpr hpos)
  have hTne : T.Nonempty := ⟨b.1, hbT⟩
  have hTbdd' : BddBelow T := ⟨δ, hTbdd⟩
  set s := sInf T with hs
  have hsT : s ∈ T := hTclosed.csInf_mem hTne hTbdd'
  have hδs : δ ≤ s := le_csInf hTne hTbdd
  have hspos : 0 < s := by linarith
  let astar : SuzukiPositiveAperture := ⟨s, hspos⟩
  have hap_s : ap s = astar := by
    apply Subtype.ext
    show max s (δ / 2) = s
    exact max_eq_left (by linarith)
  have hbelow : ∀ c : SuzukiPositiveAperture, c.1 < s → 0 < ccmRestrictedWeilPolarGroundEnergy c := by
    intro c hc
    by_contra hle
    push Not at hle
    have hcT : c.1 ∈ T := by
      show ccmRestrictedWeilPolarGroundEnergy (ap c.1) ≤ 0
      rcases le_or_gt (δ / 2) c.1 with h | h
      · have : ap c.1 = c := by
          apply Subtype.ext
          show max c.1 (δ / 2) = c.1
          exact max_eq_left h
        rw [this]; exact hle
      · exfalso
        have := hsmall c (by linarith)
        linarith
    have := csInf_le hTbdd' hcT
    linarith
  have hle0 : ccmRestrictedWeilPolarGroundEnergy astar ≤ 0 := by
    have h := hsT
    change ccmRestrictedWeilPolarGroundEnergy (ap s) ≤ 0 at h
    rwa [hap_s] at h
  have hge0 : 0 ≤ ccmRestrictedWeilPolarGroundEnergy astar := by
    by_contra hneg
    push Not at hneg
    have hev : ∀ᶠ c in 𝓝 astar, ccmRestrictedWeilPolarGroundEnergy c < 0 :=
      (continuousAt_ccmRestrictedWeilPolarGroundEnergy astar).eventually (gt_mem_nhds hneg)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    let c : SuzukiPositiveAperture := ⟨s - min (ε / 2) (s / 2), by
      have : min (ε / 2) (s / 2) ≤ s / 2 := min_le_right _ _
      linarith⟩
    have hcdist : dist c astar < ε := by
      change dist c.1 astar.1 < ε
      rw [Real.dist_eq]
      show |s - min (ε / 2) (s / 2) - s| < ε
      rw [show s - min (ε / 2) (s / 2) - s = -(min (ε / 2) (s / 2)) by ring, abs_neg,
        abs_of_nonneg (le_min (by positivity) (by positivity))]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hclt : c.1 < s := by
      show s - min (ε / 2) (s / 2) < s
      have : 0 < min (ε / 2) (s / 2) := lt_min (by positivity) (by positivity)
      linarith
    have h1 := hball hcdist
    have h2 := hbelow c hclt
    linarith
  refine ⟨astar, le_antisymm hle0 hge0, hbelow, fun c hc => ?_⟩
  have := ccmRestrictedWeilPolarGroundEnergy_antitone (a := astar) (b := c) hc.le
  linarith [le_antisymm hle0 hge0]

/-- **The degeneracy law.**  Either the pole-vanishing ground energy is positive at every
aperture, or some aperture carries a normalized pole-vanishing null vector of a form that is
nonnegative on the pole-vanishing subspace. -/
theorem polar_positivity_or_null_vector :
    (∀ a : SuzukiPositiveAperture, 0 < ccmRestrictedWeilPolarGroundEnergy a) ∨
    ∃ astar : SuzukiPositiveAperture, ∃ v : CCMArchimedeanFormDomain astar,
      IsPolarConstrained astar v ∧ ‖ccmArchimedeanFormToAperture astar v‖ = 1 ∧
      ccmRestrictedWeilSourceQuadratic astar v = 0 ∧
      ∀ w : CCMArchimedeanFormDomain astar, IsPolarConstrained astar w →
        0 ≤ ccmRestrictedWeilSourceQuadratic astar w := by
  by_cases hall : ∀ a : SuzukiPositiveAperture, 0 < ccmRestrictedWeilPolarGroundEnergy a
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨b, hb⟩ := hall
    obtain ⟨astar, hzero, -, -⟩ := exists_polar_degeneracy_threshold hb
    obtain ⟨v, hv, hvn, hvQ⟩ := exists_polarConstrained_groundState astar
    refine ⟨astar, v, hv, hvn, by rw [hvQ, hzero], fun w hw => ?_⟩
    have := ccmRestrictedWeilPolarGroundEnergy_mul_le astar w hw
    rw [hzero, zero_mul] at this
    exact this

end RHTower
