import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyCofinalSourceCriterion

/-!
# Canonical symmetric-radius physical theta--Abel source criterion

The packet-stable source criterion quantifies over arbitrary finite subsets of
the multiplicity-exact Xi divisor.  This module eliminates that non-geometric
quantifier.  Since every centered Xi point lies in the horizontal strip
`|Im z| < 1/2`, the integral-radius boxes `[-m,m] × [-1,1]` exhaust every
finite divisor packet.

Consequently, eventual lower boundedness only along this single canonical
geometric exhaustion is equivalent to arbitrary-packet cofinality and hence
to RH.  The equivalence is unconditional; the final unit specialization is
closed and premise-free.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Multiplicity-exact Xi copies in the canonical centered box of horizontal
radius `m` and vertical radius one. -/
def xiPhysicalThetaAbelEnergyCanonicalPacket (m : ℕ) : Finset XiZeroCopy :=
  xiZeroCopyClosedRectangle
    (((-(m : ℝ) : ℝ) : ℂ) - I)
    ((((m : ℕ) : ℝ) : ℂ) + I)

/-- Eventual source-contour lower boundedness along the canonical
integral-radius exhaustion. -/
def XiPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow
    (L A c : ℝ) : Prop :=
  ∃ B : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    L < Real.log n / 2 → ∀ m : ℕ,
      XiPhysicalThetaAbelEnergySourceRectangleAbove
        L A c (Real.log n / 2) B
          (xiPhysicalThetaAbelEnergyCanonicalPacket m)

/-- The canonical integral-radius boxes are cofinal among finite
multiplicity-exact Xi packets. -/
theorem xiZeroCopy_finset_subset_physicalThetaAbelEnergyCanonicalPacket
    (t : Finset XiZeroCopy) :
    ∃ m : ℕ, t ⊆ xiPhysicalThetaAbelEnergyCanonicalPacket m := by
  classical
  let R : ℝ := 1 + ∑ q ∈ t, ‖xiSpectralPoint q‖
  obtain ⟨m, hm⟩ := exists_nat_gt R
  refine ⟨m, ?_⟩
  intro q hq
  rw [xiPhysicalThetaAbelEnergyCanonicalPacket,
    mem_xiZeroCopyClosedRectangle]
  apply Complex.mem_reProdIm.mpr
  have hsum : ‖xiSpectralPoint q‖ ≤ ∑ r ∈ t, ‖xiSpectralPoint r‖ :=
    Finset.single_le_sum (fun r _ => norm_nonneg (xiSpectralPoint r)) hq
  have hre := Complex.abs_re_le_norm (xiSpectralPoint q)
  have him := xiSpectralPoint_im_mem_openHalf q
  have hqreL : -(m : ℝ) ≤ (xiSpectralPoint q).re := by
    have hneg := neg_le_neg (le_trans (neg_le_abs _) (le_trans hre hsum))
    dsimp only [R] at hm
    exact le_of_lt (by linarith)
  have hqreR : (xiSpectralPoint q).re ≤ (m : ℝ) := by
    have hpos := le_trans (le_abs_self _) (le_trans hre hsum)
    dsimp only [R] at hm
    exact le_of_lt (by linarith)
  constructor
  · rw [uIcc_of_le]
    · simpa using ⟨hqreL, hqreR⟩
    · simp
  · rw [uIcc_of_le]
    · constructor <;> norm_num <;> linarith [him.1, him.2]
    · norm_num

/-- Canonical symmetric-radius exhaustion is exactly as strong as arbitrary
finite-packet cofinality. -/
theorem xiPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow_iff_cofinal :
    XiPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow L A c ↔
      XiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow L A c := by
  constructor
  · rintro ⟨B, N₀, hB⟩
    refine ⟨B, N₀, ?_⟩
    intro n hn hLn t
    obtain ⟨m, htm⟩ :=
      xiZeroCopy_finset_subset_physicalThetaAbelEnergyCanonicalPacket t
    obtain ⟨z₁, z₂, hre, him, hcontains, hbot, htop, hright, hleft,
        hfloor⟩ := hB n hn hLn m
    exact ⟨z₁, z₂, hre, him, fun q hq => hcontains q (htm hq),
      hbot, htop, hright, hleft, hfloor⟩
  · rintro ⟨B, N₀, hB⟩
    exact ⟨B, N₀, fun n hn hLn m =>
      hB n hn hLn (xiPhysicalThetaAbelEnergyCanonicalPacket m)⟩

/-- Exact canonical symmetric-radius source-contour lower-bound criterion for
RH. -/
theorem xiPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow_iff_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow L A c ↔
      RiemannHypothesis := by
  rw [xiPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow_iff_cofinal]
  exact xiPhysicalThetaAbelEnergyCofinalSourceEventuallyBoundedBelow_iff_riemannHypothesis
    hL hA hc

/-- Closed, premise-free canonical geometric continued-source RH criterion. -/
theorem unitPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow_iff_riemannHypothesis :
    XiPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow 1 1 1 ↔
      RiemannHypothesis := by
  exact
    xiPhysicalThetaAbelEnergySymmetricRadiusSourceEventuallyBoundedBelow_iff_riemannHypothesis
      (by norm_num) (by norm_num) (by norm_num)

end

end RHTower
