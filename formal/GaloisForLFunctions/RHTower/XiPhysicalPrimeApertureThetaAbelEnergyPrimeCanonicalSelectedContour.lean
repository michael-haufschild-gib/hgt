import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeCanonicalKillerTail

/-!
# A fixed canonical selected corrected-prime contour criterion

The packet-stable corrected-prime criterion quantifies existentially over admissible rectangles.
This module removes that final geometric choice.  For every physical scale and canonical copied-zero
radius, choose once and for all a pole-crossing admissible rectangle whose normalized source contour
is within one unit of complete Weil energy.  The corrected-prime residue identity transfers this
approximation to the literal prime contour plus its explicit elementary correction.

RH gives the selected array a uniform lower floor `-1`.  If RH is false, then below every real floor
and at arbitrarily late logarithmic scales, every radius of this fixed selected array lies below the
floor.  Thus both RH and its negation receive exact premise-free criteria with no remaining packet
or contour quantifier.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Specification of a pole-crossing admissible rectangle containing the canonical radius packet
and approximating complete physical theta--Abel Weil energy within one unit. -/
def XiPhysicalThetaAbelEnergyCanonicalApproxRectangleSpec
    (L A c a : ℝ) (m : ℕ) (z : ℂ × ℂ) : Prop :=
  z.1.re < z.2.re ∧ z.1.im < z.2.im ∧
  z.1.re < 0 ∧ 0 < z.2.re ∧
  z.1.im < -(1 / 2) ∧ -(1 / 2) < z.2.im ∧ z.2.im < 1 / 2 ∧
  (∀ q ∈ xiPhysicalThetaAbelEnergyCanonicalPacket m,
    q ∈ xiZeroCopyClosedRectangle z.1 z.2) ∧
  (∀ x ∈ uIcc z.1.re z.2.re,
    XiExplicitAdmissible ((x : ℂ) + z.1.im * I)) ∧
  (∀ x ∈ uIcc z.1.re z.2.re,
    XiExplicitAdmissible ((x : ℂ) + z.2.im * I)) ∧
  (∀ y ∈ uIcc z.1.im z.2.im,
    XiExplicitAdmissible ((z.2.re : ℂ) + y * I)) ∧
  (∀ y ∈ uIcc z.1.im z.2.im,
    XiExplicitAdmissible ((z.1.re : ℂ) + y * I)) ∧
  dist (xiPhysicalThetaAbelEnergyNormalizedSourceContour L A c a z.1 z.2)
    (xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)) < 1

/-- The canonical unit-approximation rectangle specification is inhabited at every radius and
physical scale. -/
theorem exists_canonicalApproxRectangleSpec
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) (m : ℕ) :
    ∃ z : ℂ × ℂ,
      XiPhysicalThetaAbelEnergyCanonicalApproxRectangleSpec L A c a m z := by
  obtain ⟨z₁, z₂, hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
      hpacket, hbot, htop, hright, hleft, hdist⟩ :=
    exists_poleCrossing_admissible_physicalThetaAbelEnergySourceContour_containing_approximates_weil
      hA hc L a (xiPhysicalThetaAbelEnergyCanonicalPacket m)
        (by norm_num : (0 : ℝ) < 1)
  exact ⟨(z₁, z₂), hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
    hpacket, hbot, htop, hright, hleft, hdist⟩

/-- Fixed selected admissible rectangle for one physical scale and canonical radius. -/
noncomputable def xiPhysicalThetaAbelEnergyCanonicalApproxRectangle
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) (m : ℕ) : ℂ × ℂ :=
  Classical.choose (exists_canonicalApproxRectangleSpec hA hc L a m)

/-- The fixed selected rectangle satisfies its complete geometric and approximation contract. -/
theorem xiPhysicalThetaAbelEnergyCanonicalApproxRectangle_spec
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) (m : ℕ) :
    XiPhysicalThetaAbelEnergyCanonicalApproxRectangleSpec L A c a m
      (xiPhysicalThetaAbelEnergyCanonicalApproxRectangle hA hc L a m) :=
  Classical.choose_spec (exists_canonicalApproxRectangleSpec hA hc L a m)

/-- Corrected literal prime-contour value on the fixed selected rectangle. -/
noncomputable def xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) (m : ℕ) : ℂ :=
  xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour L A c a
    (xiPhysicalThetaAbelEnergyCanonicalApproxRectangle hA hc L a m).1
    (xiPhysicalThetaAbelEnergyCanonicalApproxRectangle hA hc L a m).2

/-- Every fixed selected corrected-prime sample lies within one unit of complete physical
theta--Abel Weil energy. -/
theorem dist_canonicalCorrectedPrimeSample_weil_lt_one
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) (m : ℕ) :
    dist (xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample hA hc L a m)
      (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)) < 1 := by
  obtain ⟨hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
      _hpacket, hbot, htop, hright, hleft, hdist⟩ :=
    xiPhysicalThetaAbelEnergyCanonicalApproxRectangle_spec hA hc L a m
  rw [xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample,
    ← xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_correctedPrime
      hbot htop hright hleft him hleftGeom hrightGeom hbelow habove htopGeom]
  exact hdist

/-- Under RH, every radius and every physical scale of the fixed selected corrected-prime array is
strictly above `-1`. -/
theorem canonicalCorrectedPrimeSample_re_gt_neg_one_of_riemannHypothesis
    {L A c a : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hRH : RiemannHypothesis) (m : ℕ) :
    -1 < (xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample
      hA hc L a m).re := by
  let W : ℂ := xiWeilPolarization
    (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
    (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
  have hdist := dist_canonicalCorrectedPrimeSample_weil_lt_one hA hc L a m
  have hweil : 0 ≤ W.re :=
    (riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH)
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform_squareSummable hA hc L a)
  have habs := Complex.abs_re_le_norm
    (xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample hA hc L a m - W)
  change |(xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample
      hA hc L a m).re - W.re| ≤
    ‖xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample hA hc L a m - W‖ at habs
  rw [dist_eq] at hdist
  have hneg := neg_le_abs
    ((xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample hA hc L a m).re - W.re)
  dsimp only [W] at hdist hweil habs hneg ⊢
  linarith

/-- If RH is false, then below every floor and at arbitrarily late logarithmic scales, every
canonical radius of the fixed selected corrected-prime array lies below the floor. -/
theorem not_riemannHypothesis_implies_canonicalCorrectedPrimeSamples_allRadii_cofinally_unbounded_below
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hRH : ¬RiemannHypothesis) :
    ∀ B : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ,
      N₀ ≤ n ∧ L < Real.log n / 2 ∧
      ∀ m : ℕ,
        (xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample
          hA hc L (Real.log n / 2) m).re < B := by
  intro B N₀
  obtain ⟨n, hn, hLn, hweil⟩ :=
    not_riemannHypothesis_implies_physicalThetaAbelEnergy_weil_cofinally_unbounded_below
      hL hA hc hRH (B - 1) N₀
  refine ⟨n, hn, hLn, ?_⟩
  intro m
  let W : ℂ := xiWeilPolarization
    (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
    (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
  have hdist := dist_canonicalCorrectedPrimeSample_weil_lt_one
    hA hc L (Real.log n / 2) m
  rw [dist_eq] at hdist
  have hre := Complex.re_le_norm
    (xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample
      hA hc L (Real.log n / 2) m - W)
  change (xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample
      hA hc L (Real.log n / 2) m).re - W.re ≤
    ‖xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample
      hA hc L (Real.log n / 2) m - W‖ at hre
  dsimp only [W] at hdist hre hweil
  linarith

/-- Eventual lower boundedness of the single fixed canonical selected corrected-prime array. -/
def XiPhysicalThetaAbelEnergyCanonicalSelectedEventuallyBoundedBelow
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L : ℝ) : Prop :=
  ∃ B : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    L < Real.log n / 2 → ∀ m : ℕ,
      B ≤ (xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample
        hA hc L (Real.log n / 2) m).re

/-- Exact no-choice RH criterion: the fixed canonical selected prime-contour array is eventually
bounded below exactly when RH holds. -/
theorem canonicalSelectedEventuallyBoundedBelow_iff_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiPhysicalThetaAbelEnergyCanonicalSelectedEventuallyBoundedBelow hA hc L ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨B, N₀, hB⟩
    by_contra hRH
    obtain ⟨n, hn, hLn, hall⟩ :=
      not_riemannHypothesis_implies_canonicalCorrectedPrimeSamples_allRadii_cofinally_unbounded_below
        hL hA hc hRH B N₀
    exact (not_lt_of_ge (hB n hn hLn 0)) (hall 0)
  · intro hRH
    exact ⟨-1, 0, fun n _hn _hLn m =>
      (canonicalCorrectedPrimeSample_re_gt_neg_one_of_riemannHypothesis
        hA hc hRH m).le⟩

/-- Exact dual no-choice criterion: simultaneous all-radius cofinal collapse of the fixed selected
prime-contour array occurs exactly when RH is false. -/
theorem canonicalCorrectedPrimeSamplesAllRadiiCofinallyUnboundedBelow_iff_not_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    (∀ B : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ,
      N₀ ≤ n ∧ L < Real.log n / 2 ∧
      ∀ m : ℕ,
        (xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample
          hA hc L (Real.log n / 2) m).re < B) ↔
      ¬RiemannHypothesis := by
  constructor
  · intro hbad hRH
    obtain ⟨n, _hn, _hLn, hall⟩ := hbad (-1) 0
    exact (not_lt_of_ge
      (canonicalCorrectedPrimeSample_re_gt_neg_one_of_riemannHypothesis
        hA hc hRH 0).le) (hall 0)
  · exact
      not_riemannHypothesis_implies_canonicalCorrectedPrimeSamples_allRadii_cofinally_unbounded_below
        hL hA hc

/-- Premise-free unit-parameter selected-contour RH criterion. -/
theorem unitCanonicalSelectedEventuallyBoundedBelow_iff_riemannHypothesis :
    XiPhysicalThetaAbelEnergyCanonicalSelectedEventuallyBoundedBelow
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) 1 ↔
      RiemannHypothesis := by
  exact canonicalSelectedEventuallyBoundedBelow_iff_riemannHypothesis
    (by norm_num) (by norm_num) (by norm_num)

/-- Premise-free unit-parameter selected-contour false-RH criterion. -/
theorem unitCanonicalCorrectedPrimeSamplesAllRadiiCofinallyUnboundedBelow_iff_not_riemannHypothesis :
    (∀ B : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ,
      N₀ ≤ n ∧ 1 < Real.log n / 2 ∧
      ∀ m : ℕ,
        (xiPhysicalThetaAbelEnergyCanonicalCorrectedPrimeSample
          (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
          1 (Real.log n / 2) m).re < B) ↔
      ¬RiemannHypothesis := by
  exact canonicalCorrectedPrimeSamplesAllRadiiCofinallyUnboundedBelow_iff_not_riemannHypothesis
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower
