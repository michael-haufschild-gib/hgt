import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeKillerPacket
import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergySymmetricRadiusSourceCriterion

/-!
# Canonical-radius tails of corrected-prime killer packets

Loop 84 produces an arbitrary finite copied-zero packet which forces every admissible enclosing
corrected-prime contour below a chosen floor.  This module removes the arbitrary packet choice.
Killer behavior is upward-closed, while the canonical centered integral-radius Xi packets are
monotone and cofinal.  Thus every killer packet generates a whole tail of canonical killer packets.

Consequently, failure of RH is equivalent to cofinal hostile behavior along one deterministic
geometric exhaustion: below every floor and at arbitrarily late physical scales, every sufficiently
large canonical radius forces every admissible enclosing corrected-prime contour below that floor.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Corrected-prime killer behavior is upward-closed in the copied-zero packet. -/
theorem correctedPrimeKillerPacket_mono
    {L A c a B : ℝ} {t u : Finset XiZeroCopy}
    (ht : XiPhysicalThetaAbelEnergyCorrectedPrimeKillerPacket L A c a B t)
    (htu : t ≤ u) :
    XiPhysicalThetaAbelEnergyCorrectedPrimeKillerPacket L A c a B u := by
  intro z₁ z₂ hre him hleftGeom hrightGeom hbelow habove htopGeom
    hu hbot htop hright hleft
  exact ht z₁ z₂ hre him hleftGeom hrightGeom hbelow habove htopGeom
    (fun q hq => hu q (htu hq)) hbot htop hright hleft

/-- Canonical centered integral-radius copied-zero packets increase with radius. -/
theorem xiPhysicalThetaAbelEnergyCanonicalPacket_mono {m k : ℕ} (hmk : m ≤ k) :
    xiPhysicalThetaAbelEnergyCanonicalPacket m ≤
      xiPhysicalThetaAbelEnergyCanonicalPacket k := by
  intro q hq
  rw [xiPhysicalThetaAbelEnergyCanonicalPacket,
    mem_xiZeroCopyClosedRectangle] at hq ⊢
  have hq' : xiSpectralPoint q ∈
      uIcc (-(m : ℝ)) (m : ℝ) ×ℂ uIcc (-1) 1 := by
    simpa using hq
  obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hq'
  have hmkR : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hmorder : -(m : ℝ) ≤ m := neg_le_self (by positivity)
  have hkorder : -(k : ℝ) ≤ k := neg_le_self (by positivity)
  rw [uIcc_of_le hmorder] at hre
  have hout : xiSpectralPoint q ∈
      uIcc (-(k : ℝ)) (k : ℝ) ×ℂ uIcc (-1) 1 := by
    apply Complex.mem_reProdIm.mpr
    rw [uIcc_of_le hkorder]
    exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, him⟩
  simpa using hout

/-- Every sufficiently large canonical centered-radius packet is a corrected-prime killer packet
at the fixed physical scale and floor. -/
def XiPhysicalThetaAbelEnergyCanonicalRadiusKillerTail
    (L A c a B : ℝ) : Prop :=
  ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    XiPhysicalThetaAbelEnergyCorrectedPrimeKillerPacket
      L A c a B (xiPhysicalThetaAbelEnergyCanonicalPacket m)

/-- Any finite corrected-prime killer packet generates a whole tail of canonical-radius killer
packets. -/
theorem correctedPrimeKillerPacket_implies_canonicalRadiusKillerTail
    {L A c a B : ℝ} {t : Finset XiZeroCopy}
    (ht : XiPhysicalThetaAbelEnergyCorrectedPrimeKillerPacket L A c a B t) :
    XiPhysicalThetaAbelEnergyCanonicalRadiusKillerTail L A c a B := by
  obtain ⟨m₀, htm⟩ :=
    xiZeroCopy_finset_subset_physicalThetaAbelEnergyCanonicalPacket t
  refine ⟨m₀, ?_⟩
  intro m hmm
  exact correctedPrimeKillerPacket_mono ht
    (htm.trans (xiPhysicalThetaAbelEnergyCanonicalPacket_mono hmm))

/-- Canonical-radius killer tails exactly classify existence of arbitrary finite killer packets at
one physical scale and floor. -/
theorem exists_correctedPrimeKillerPacket_iff_canonicalRadiusKillerTail
    {L A c a B : ℝ} :
    (∃ t : Finset XiZeroCopy,
      XiPhysicalThetaAbelEnergyCorrectedPrimeKillerPacket L A c a B t) ↔
      XiPhysicalThetaAbelEnergyCanonicalRadiusKillerTail L A c a B := by
  constructor
  · rintro ⟨t, ht⟩
    exact correctedPrimeKillerPacket_implies_canonicalRadiusKillerTail ht
  · rintro ⟨m₀, hm₀⟩
    exact ⟨xiPhysicalThetaAbelEnergyCanonicalPacket m₀, hm₀ m₀ le_rfl⟩

/-- A strict upper bound for complete physical theta--Abel Weil energy forces every sufficiently
large canonical radius to be a corrected-prime killer packet. -/
theorem canonicalRadiusKillerTail_of_weil_re_lt
    {L A c a B : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hweil : (xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)).re < B) :
    XiPhysicalThetaAbelEnergyCanonicalRadiusKillerTail L A c a B := by
  obtain ⟨t, ht⟩ := exists_correctedPrimeKillerPacket_of_weil_re_lt hA hc hweil
  exact correctedPrimeKillerPacket_implies_canonicalRadiusKillerTail ht

/-- If RH is false, below every floor and at arbitrarily late physical scales, all sufficiently
large canonical radii are corrected-prime killer packets. -/
theorem not_riemannHypothesis_implies_canonicalRadiusKillerTails_cofinally
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hRH : ¬RiemannHypothesis) :
    ∀ B : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ,
      N₀ ≤ n ∧ L < Real.log n / 2 ∧
      XiPhysicalThetaAbelEnergyCanonicalRadiusKillerTail
        L A c (Real.log n / 2) B := by
  intro B N₀
  obtain ⟨n, hn, hLn, t, ht⟩ :=
    not_riemannHypothesis_implies_correctedPrimeKillerPackets_cofinally
      hL hA hc hRH B N₀
  exact ⟨n, hn, hLn,
    correctedPrimeKillerPacket_implies_canonicalRadiusKillerTail ht⟩

/-- Exact deterministic-exhaustion dual criterion: cofinal canonical-radius killer tails exist
exactly when RH is false. -/
theorem canonicalRadiusKillerTailsCofinal_iff_not_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    (∀ B : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ,
      N₀ ≤ n ∧ L < Real.log n / 2 ∧
      XiPhysicalThetaAbelEnergyCanonicalRadiusKillerTail
        L A c (Real.log n / 2) B) ↔
      ¬RiemannHypothesis := by
  constructor
  · intro htail
    rw [← correctedPrimeKillerPacketsCofinal_iff_not_riemannHypothesis
      hL hA hc]
    intro B N₀
    obtain ⟨n, hn, hLn, m₀, hm₀⟩ := htail B N₀
    exact ⟨n, hn, hLn, xiPhysicalThetaAbelEnergyCanonicalPacket m₀,
      hm₀ m₀ le_rfl⟩
  · exact not_riemannHypothesis_implies_canonicalRadiusKillerTails_cofinally
      hL hA hc

/-- Premise-free unit-parameter canonical-radius killer-tail criterion. -/
theorem unitCanonicalRadiusKillerTailsCofinal_iff_not_riemannHypothesis :
    (∀ B : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ,
      N₀ ≤ n ∧ 1 < Real.log n / 2 ∧
      XiPhysicalThetaAbelEnergyCanonicalRadiusKillerTail
        1 1 1 (Real.log n / 2) B) ↔
      ¬RiemannHypothesis := by
  exact canonicalRadiusKillerTailsCofinal_iff_not_riemannHypothesis
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower
