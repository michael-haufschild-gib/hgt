import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeContour

/-!
# Packet-stable direct-prime physical theta--Abel energy criterion

The cofinal admissible rectangles may be chosen to cross the unique centered
archimedean pole while their top remains below the next singular height.  On
those rectangles, the exact source contour is the literal continued-prime
flux contour plus one elementary positive square.

This removes the completed Gamma channel from the packet-stable source
criterion.  Eventual lower boundedness of these explicitly corrected direct
prime contours is equivalent to RH; the unit specialization is closed and
premise-free.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Pole-crossing admissible direct-prime rectangle above a real floor after
restoring the explicit archimedean residue. -/
def XiPhysicalThetaAbelEnergyCorrectedPrimeRectangleAbove
    (L A c a B : ℝ) (t : Finset XiZeroCopy) : Prop :=
  ∃ z₁ z₂ : ℂ,
    z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
    z₁.re < 0 ∧ 0 < z₂.re ∧
    z₁.im < -(1 / 2) ∧ -(1 / 2) < z₂.im ∧ z₂.im < 1 / 2 ∧
    (∀ q ∈ t, q ∈ xiZeroCopyClosedRectangle z₁ z₂) ∧
    (∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I)) ∧
    (∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I)) ∧
    (∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I)) ∧
    (∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) ∧
    B ≤ (xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour
      L A c a z₁ z₂).re

/-- Packet-stable eventual lower boundedness of the literal continued-prime
contours after the unique explicit archimedean residue is restored. -/
def XiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow
    (L A c : ℝ) : Prop :=
  ∃ B : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    L < Real.log n / 2 → ∀ t : Finset XiZeroCopy,
      XiPhysicalThetaAbelEnergyCorrectedPrimeRectangleAbove
        L A c (Real.log n / 2) B t

/-- Cofinal source approximation can be chosen to cross exactly the centered
archimedean pole needed by the explicit correction. -/
theorem exists_poleCrossing_admissible_physicalThetaAbelEnergySourceContour_containing_approximates_weil
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ)
    (t : Finset XiZeroCopy) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      z₁.re < 0 ∧ 0 < z₂.re ∧
      z₁.im < -(1 / 2) ∧ -(1 / 2) < z₂.im ∧ z₂.im < 1 / 2 ∧
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
      (xiSpectralPoint q) ^ (2 : ℕ)
  have hsum : Summable f :=
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_summable hA hc L a
  have hball : Metric.ball (∑' q, f q) epsilon ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨u, hu⟩ := hevent
  obtain ⟨z₁, z₂, hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
      hpacket, hbot, htop, hright, hleft⟩ :=
    exists_poleCrossing_admissible_rectangle_containing_xiZeroCopy_finset
      (t ∪ u)
  refine ⟨z₁, z₂, hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
    ?_, hbot, htop, hright, hleft, ?_⟩
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

theorem xiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow_of_riemannHypothesis
    {L A c : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hRH : RiemannHypothesis) :
    XiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow
      L A c := by
  refine ⟨-1, 0, ?_⟩
  intro n _hn _hLn t
  obtain ⟨z₁, z₂, hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
      ht, hbot, htop, hright, hleft, hdist⟩ :=
    exists_poleCrossing_admissible_physicalThetaAbelEnergySourceContour_containing_approximates_weil
      hA hc L (Real.log n / 2) t (by norm_num : (0 : ℝ) < 1)
  refine ⟨z₁, z₂, hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
    ht, hbot, htop, hright, hleft, ?_⟩
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
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c
          (Real.log n / 2)))
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
  rw [← xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_correctedPrime
    hbot htop hright hleft him hleftGeom hrightGeom hbelow habove htopGeom]
  linarith

theorem riemannHypothesis_of_xiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hprime : XiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow
      L A c) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow
    hL hA hc
  obtain ⟨B, N₀, hB⟩ := hprime
  refine ⟨B, N₀, ?_⟩
  intro n hn hLn t
  obtain ⟨z₁, z₂, hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
      ht, hbot, htop, hright, hleft, hfloor⟩ := hB n hn hLn t
  refine ⟨z₁, z₂, hre, him, ht, hbot, htop, hright, hleft, ?_⟩
  rw [xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_correctedPrime
    hbot htop hright hleft him hleftGeom hrightGeom hbelow habove htopGeom]
  exact hfloor

/-- Exact packet-stable direct-prime-contour lower-bound criterion for RH. -/
theorem xiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow_iff_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow
        L A c ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow
      hL hA hc
  · exact xiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow_of_riemannHypothesis
      hA hc

/-- Closed, premise-free, continued-prime-flux RH criterion. -/
theorem unitPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow_iff_riemannHypothesis :
    XiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow
      1 1 1 ↔ RiemannHypothesis := by
  exact
    xiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow_iff_riemannHypothesis
      (by norm_num) (by norm_num) (by norm_num)

end

end RHTower
