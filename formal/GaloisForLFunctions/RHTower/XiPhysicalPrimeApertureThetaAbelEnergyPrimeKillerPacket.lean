import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeSourceCriterion

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- If an absolutely summable complex family has real total below `B`, a finite core forces
every larger finite partial sum below `B`.  This is the finite-packet form of convergence of the
unordered sum. -/
theorem exists_finset_re_sum_lt_of_tsum_re_lt
    {α : Type*} [DecidableEq α] {f : α → ℂ} (hf : Summable f) {B : ℝ}
    (hB : (∑' x, f x).re < B) :
    ∃ t : Finset α, ∀ u : Finset α, t ≤ u → (∑ x ∈ u, f x).re < B := by
  let ε : ℝ := (B - (∑' x, f x).re) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hball : Metric.ball (∑' x, f x) ε ∈ nhds (∑' x, f x) :=
    Metric.ball_mem_nhds _ hε
  have hevent : ∀ᶠ u : Finset α in atTop,
      ∑ x ∈ u, f x ∈ Metric.ball (∑' x, f x) ε :=
    hf.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨t, ht⟩ := hevent
  refine ⟨t, ?_⟩
  intro u htu
  have hnear := ht u htu
  rw [Metric.mem_ball, dist_eq] at hnear
  have hre := Complex.re_le_norm ((∑ x ∈ u, f x) - ∑' x, f x)
  change (∑ x ∈ u, f x).re - (∑' x, f x).re ≤
    ‖(∑ x ∈ u, f x) - ∑' x, f x‖ at hre
  dsimp [ε] at hnear
  linarith

/-- A finite divisor packet whose inclusion forces every admissible pole-crossing corrected-prime
rectangle below the prescribed floor.  Unlike an adaptive exhaustion witness, this certificate is
stable under every further admissible enlargement. -/
def XiPhysicalThetaAbelEnergyCorrectedPrimeKillerPacket
    (L A c a B : ℝ) (t : Finset XiZeroCopy) : Prop :=
  ∀ z₁ z₂ : ℂ,
    z₁.re < z₂.re → z₁.im < z₂.im →
    z₁.re < 0 → 0 < z₂.re →
    z₁.im < -(1 / 2) → -(1 / 2) < z₂.im → z₂.im < 1 / 2 →
    (∀ q ∈ t, q ∈ xiZeroCopyClosedRectangle z₁ z₂) →
    (∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I)) →
    (∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I)) →
    (∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I)) →
    (∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) →
    (xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour
      L A c a z₁ z₂).re < B

/-- A strict upper bound for complete physical theta--Abel Weil energy exposes a finite killer
packet for corrected-prime contours.  Absolute summability makes the certificate persistent under
arbitrary finite enlargement; the residue theorem transfers it to every admissible rectangle. -/
theorem exists_correctedPrimeKillerPacket_of_weil_re_lt
    {L A c a B : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hweil : (xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)).re < B) :
    ∃ t : Finset XiZeroCopy,
      XiPhysicalThetaAbelEnergyCorrectedPrimeKillerPacket L A c a B t := by
  let f : XiZeroCopy → ℂ := fun q =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
      (xiSpectralPoint q) ^ 2
  have hsum : Summable f :=
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_summable hA hc L a
  have htsum : (∑' q, f q).re < B := by
    rw [← xiWeilPolarization_physicalThetaAbelEnergy_eq_tsum_sq]
    exact hweil
  obtain ⟨t, ht⟩ := exists_finset_re_sum_lt_of_tsum_re_lt hsum htsum
  refine ⟨t, ?_⟩
  intro z₁ z₂ hre him hleftGeom hrightGeom hbelow habove htopGeom
    hpacket hbot htop hright hleft
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd L A c a)
      hre him hbot htop hright hleft
  have hsubset : t ≤ xiZeroCopyClosedRectangle z₁ z₂ := by
    intro q hq
    exact hpacket q hq
  have hfinite := ht (xiZeroCopyClosedRectangle z₁ z₂) hsubset
  have hfactor : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  have hsource :
      xiPhysicalThetaAbelEnergyNormalizedSourceContour L A c a z₁ z₂ =
        ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂, f q := by
    rw [xiPhysicalThetaAbelEnergyNormalizedSourceContour, hcontour,
      ← mul_assoc, inv_mul_cancel₀ hfactor, one_mul]
  rw [← xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_correctedPrime
    hbot htop hright hleft him hleftGeom hrightGeom hbelow habove htopGeom]
  rw [hsource]
  exact hfinite

/-- If RH is false, arbitrarily late physical theta--Abel scales and arbitrarily low floors admit
finite killer packets for every enclosing corrected-prime contour. -/
theorem not_riemannHypothesis_implies_correctedPrimeKillerPackets_cofinally
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hRH : ¬RiemannHypothesis) :
    ∀ B : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ,
      N₀ ≤ n ∧ L < Real.log n / 2 ∧
      ∃ t : Finset XiZeroCopy,
        XiPhysicalThetaAbelEnergyCorrectedPrimeKillerPacket
          L A c (Real.log n / 2) B t := by
  intro B N₀
  obtain ⟨n, hn, hLn, hweil⟩ :=
    not_riemannHypothesis_implies_physicalThetaAbelEnergy_weil_cofinally_unbounded_below
      hL hA hc hRH B N₀
  refine ⟨n, hn, hLn, ?_⟩
  exact exists_correctedPrimeKillerPacket_of_weil_re_lt hA hc hweil

/-- Exact dual corrected-prime criterion: cofinally persistent finite killer packets exist exactly
when RH is false.  Under RH, eventual lower bounds provide, for each proposed packet, an enclosing
admissible rectangle contradicting its killer property. -/
theorem correctedPrimeKillerPacketsCofinal_iff_not_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    (∀ B : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ,
      N₀ ≤ n ∧ L < Real.log n / 2 ∧
      ∃ t : Finset XiZeroCopy,
        XiPhysicalThetaAbelEnergyCorrectedPrimeKillerPacket
          L A c (Real.log n / 2) B t) ↔
      ¬RiemannHypothesis := by
  constructor
  · intro hkill hRH
    obtain ⟨B, N₀, habove⟩ :=
      xiPhysicalThetaAbelEnergyCofinalCorrectedPrimeEventuallyBoundedBelow_of_riemannHypothesis
        (L := L) hA hc hRH
    obtain ⟨n, hn, hLn, t, hbelowAll⟩ := hkill B N₀
    obtain ⟨z₁, z₂, hre, him, hleftGeom, hrightGeom, hbelow, haboveGeom,
        htopGeom, ht, hbot, htop, hright, hleft, hfloor⟩ :=
      habove n hn hLn t
    exact (not_lt_of_ge hfloor)
      (hbelowAll z₁ z₂ hre him hleftGeom hrightGeom hbelow haboveGeom htopGeom
        ht hbot htop hright hleft)
  · exact not_riemannHypothesis_implies_correctedPrimeKillerPackets_cofinally
      hL hA hc

/-- Premise-free unit-parameter form of the dual corrected-prime killer-packet criterion. -/
theorem unitCorrectedPrimeKillerPacketsCofinal_iff_not_riemannHypothesis :
    (∀ B : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ,
      N₀ ≤ n ∧ 1 < Real.log n / 2 ∧
      ∃ t : Finset XiZeroCopy,
        XiPhysicalThetaAbelEnergyCorrectedPrimeKillerPacket
          1 1 1 (Real.log n / 2) B t) ↔
      ¬RiemannHypothesis := by
  exact correctedPrimeKillerPacketsCofinal_iff_not_riemannHypothesis
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower
