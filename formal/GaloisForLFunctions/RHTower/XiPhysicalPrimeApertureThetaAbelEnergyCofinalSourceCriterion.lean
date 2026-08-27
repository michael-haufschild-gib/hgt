import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyWeilSource

/-!
# Packet-stable physical theta--Abel source criterion

Existence of one favorable source rectangle is too weak for a converse.  This
module introduces the exact cofinal strengthening: after prescribing any
finite packet of multiplicity copies, an admissible rectangle containing that
packet must remain above one eventual aperture-independent floor.

Absolute convergence makes a sufficiently large prescribed packet control
every finite extension.  Combined with the physical-energy Landau divergence,
this packet-stable source lower bound is equivalent to RH.  The final unit
criterion is closed and premise-free.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- One cofinal admissible physical-energy source rectangle above a prescribed
real floor. -/
def XiPhysicalThetaAbelEnergySourceRectangleAbove
    (L A c a B : ℝ) (t : Finset XiZeroCopy) : Prop :=
  ∃ z₁ z₂ : ℂ,
    z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
    (∀ q ∈ t, q ∈ xiZeroCopyClosedRectangle z₁ z₂) ∧
    (∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I)) ∧
    (∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I)) ∧
    (∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I)) ∧
    (∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) ∧
    B ≤ (xiPhysicalThetaAbelEnergyNormalizedSourceContour
      L A c a z₁ z₂).re

/-- Packet-stable eventual lower boundedness of the exact physical-energy
continued source contours. -/
def XiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow
    (L A c : ℝ) : Prop :=
  ∃ B : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    L < Real.log n / 2 → ∀ t : Finset XiZeroCopy,
      XiPhysicalThetaAbelEnergySourceRectangleAbove
        L A c (Real.log n / 2) B t

/-- A cofinal physical source contour can simultaneously contain any
prescribed packet and approximate the complete Weil value. -/
theorem exists_admissible_physicalThetaAbelEnergySourceContour_containing_approximates_weil
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ)
    (t : Finset XiZeroCopy) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      (∀ q ∈ t, q ∈ xiZeroCopyClosedRectangle z₁ z₂) ∧
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₁.im * I)) ∧
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₂.im * I)) ∧
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₂.re : ℂ) + y * I)) ∧
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) ∧
      dist (xiPhysicalThetaAbelEnergyNormalizedSourceContour L A c a z₁ z₂)
        (xiWeilPolarization
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)) < epsilon := by
  let f : XiZeroCopy → ℂ := fun q =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
      (xiSpectralPoint q) ^ 2
  have hsum : Summable f :=
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_summable hA hc L a
  have hball : Metric.ball (∑' q, f q) epsilon ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨u, hu⟩ := hevent
  obtain ⟨z₁, z₂, hre, him, hpacket, hbot, htop, hright, hleft⟩ :=
    exists_admissible_rectangle_containing_xiZeroCopy_finset (t ∪ u)
  refine ⟨z₁, z₂, hre, him, ?_, hbot, htop, hright, hleft, ?_⟩
  · intro q hq
    rw [mem_xiZeroCopyClosedRectangle]
    apply Complex.mem_reProdIm.mpr
    rw [uIcc_of_le hre.le, uIcc_of_le him.le]
    exact ⟨⟨(hpacket q (Finset.mem_union_left u hq)).1.le,
        (hpacket q (Finset.mem_union_left u hq)).2.1.le⟩,
      ⟨(hpacket q (Finset.mem_union_left u hq)).2.2.1.le,
        (hpacket q (Finset.mem_union_left u hq)).2.2.2.le⟩⟩
  · have hcontour :=
      rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd L A c a)
        hre him hbot htop hright hleft
    have hsubset : u ≤ xiZeroCopyClosedRectangle z₁ z₂ := by
      intro q hq
      rw [mem_xiZeroCopyClosedRectangle]
      apply Complex.mem_reProdIm.mpr
      rw [uIcc_of_le hre.le, uIcc_of_le him.le]
      exact ⟨⟨(hpacket q (Finset.mem_union_right t hq)).1.le,
          (hpacket q (Finset.mem_union_right t hq)).2.1.le⟩,
        ⟨(hpacket q (Finset.mem_union_right t hq)).2.2.1.le,
          (hpacket q (Finset.mem_union_right t hq)).2.2.2.le⟩⟩
    have hnear := hu (xiZeroCopyClosedRectangle z₁ z₂) hsubset
    rw [Metric.mem_ball] at hnear
    have hfactor : (2 * Real.pi * I : ℂ) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact_mod_cast Real.pi_ne_zero
      · exact I_ne_zero
    rw [xiPhysicalThetaAbelEnergyNormalizedSourceContour, hcontour,
      xiWeilPolarization_physicalThetaAbelEnergy_eq_tsum_sq]
    rw [← mul_assoc, inv_mul_cancel₀ hfactor, one_mul]
    simpa only [f] using hnear

theorem xiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow_of_riemannHypothesis
    {L A c : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hRH : RiemannHypothesis) :
    XiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow L A c := by
  refine ⟨-1, 0, ?_⟩
  intro n _hn _hLn t
  obtain ⟨z₁, z₂, hre, him, ht, hbot, htop, hright, hleft, hdist⟩ :=
    exists_admissible_physicalThetaAbelEnergySourceContour_containing_approximates_weil
      hA hc L (Real.log n / 2) t (by norm_num : (0 : ℝ) < 1)
  refine ⟨z₁, z₂, hre, him, ht, hbot, htop, hright, hleft, ?_⟩
  have hweil : 0 ≤ (xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
        (Real.log n / 2))).re :=
    (riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH)
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform_squareSummable
        hA hc L (Real.log n / 2))
  rw [dist_eq] at hdist
  have habs := Complex.abs_re_le_norm
    (xiPhysicalThetaAbelEnergyNormalizedSourceContour
        L A c (Real.log n / 2) z₁ z₂ -
      xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2)))
  have hneg := neg_le_abs
    ((xiPhysicalThetaAbelEnergyNormalizedSourceContour
        L A c (Real.log n / 2) z₁ z₂).re -
      (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
          (Real.log n / 2))).re)
  change
    |(xiPhysicalThetaAbelEnergyNormalizedSourceContour
        L A c (Real.log n / 2) z₁ z₂).re -
      (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
          (Real.log n / 2))).re| ≤
      ‖xiPhysicalThetaAbelEnergyNormalizedSourceContour
          L A c (Real.log n / 2) z₁ z₂ -
        xiWeilPolarization
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
            (Real.log n / 2))‖ at habs
  linarith

theorem riemannHypothesis_of_xiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hsource : XiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow
      L A c) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨B, N₀, hB⟩ := hsource
  obtain ⟨n, hn, hLn, hweil⟩ :=
    not_riemannHypothesis_implies_physicalThetaAbelEnergy_weil_cofinally_unbounded_below
      hL hA hc hRH (B - 1) N₀
  let f : XiZeroCopy → ℂ := fun q =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2)
      (xiSpectralPoint q) ^ 2
  have hsum : Summable f :=
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_summable
      hA hc L (Real.log n / 2)
  have hball : Metric.ball (∑' q, f q) (1 / 2 : ℝ) ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ (by norm_num)
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) (1 / 2 : ℝ) :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨t, ht⟩ := hevent
  obtain ⟨z₁, z₂, hre, him, hcontains, hbot, htop, hright, hleft,
      hfloor⟩ := hB n hn hLn t
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd
        L A c (Real.log n / 2))
      hre him hbot htop hright hleft
  have hsubset : t ≤ xiZeroCopyClosedRectangle z₁ z₂ := by
    intro q hq
    exact hcontains q hq
  have hnear := ht (xiZeroCopyClosedRectangle z₁ z₂) hsubset
  rw [Metric.mem_ball] at hnear
  have hfactor : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  have hnormalize :
      xiPhysicalThetaAbelEnergyNormalizedSourceContour
          L A c (Real.log n / 2) z₁ z₂ =
        ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂, f q := by
    rw [xiPhysicalThetaAbelEnergyNormalizedSourceContour, hcontour,
      ← mul_assoc, inv_mul_cancel₀ hfactor, one_mul]
  rw [← hnormalize,
    ← xiWeilPolarization_physicalThetaAbelEnergy_eq_tsum_sq] at hnear
  rw [dist_eq] at hnear
  have hreal := Complex.re_le_norm
    (xiPhysicalThetaAbelEnergyNormalizedSourceContour
        L A c (Real.log n / 2) z₁ z₂ -
      xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2)))
  change
    (xiPhysicalThetaAbelEnergyNormalizedSourceContour
        L A c (Real.log n / 2) z₁ z₂).re -
      (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
          (Real.log n / 2))).re ≤
      ‖xiPhysicalThetaAbelEnergyNormalizedSourceContour
          L A c (Real.log n / 2) z₁ z₂ -
        xiWeilPolarization
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
          (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
            (Real.log n / 2))‖ at hreal
  linarith

/-- Exact packet-stable source-contour lower-bound criterion for RH. -/
theorem xiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow_iff_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow L A c ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow
      hL hA hc
  · exact xiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow_of_riemannHypothesis
      hA hc

/-- Closed, premise-free cofinal continued-source RH criterion. -/
theorem unitPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow_iff_riemannHypothesis :
    XiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow 1 1 1 ↔
      RiemannHypothesis := by
  exact xiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow_iff_riemannHypothesis
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower
