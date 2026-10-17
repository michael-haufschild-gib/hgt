import GaloisForLFunctions.RHTower.BernsteinOccupationRigidity
import GaloisForLFunctions.RHTower.XiBernsteinMaximalPacketAsymptotic
import GaloisForLFunctions.RHTower.ReciprocalAtomTestSpaceClosure

/-!
# Multiplicity-exact conjugation of the maximal Xi packet

The Deninger divisor conjugation preserves complete amplitude packets and pairs reciprocal-square
fibres bijectively. Aggregated coefficients retain the full fibre cardinality.
-/

open Complex
open scoped BigOperators Real unitInterval ComplexConjugate

namespace RHTower

noncomputable section

theorem xiEndpointNormalizedReciprocalSquare_conjEquiv (q : XiZeroCopy) :
    xiEndpointNormalizedReciprocalSquare (xiZeroCopyConjEquiv q) =
      conj (xiEndpointNormalizedReciprocalSquare q) := by
  simp only [xiEndpointNormalizedReciprocalSquare, xiZeroCopyReciprocalSquare_conjEquiv,
    map_div₀, Complex.conj_ofReal]

theorem xiEndpointBernsteinAtomAmplitudeBase_conjEquiv (q : XiZeroCopy) :
    xiEndpointBernsteinAtomAmplitudeBase (xiZeroCopyConjEquiv q) =
      xiEndpointBernsteinAtomAmplitudeBase q := by
  rw [xiEndpointBernsteinAtomAmplitudeBase, xiEndpointNormalizedReciprocalSquare_conjEquiv]
  rw [show 1 - conj (xiEndpointNormalizedReciprocalSquare q) =
      conj (1 - xiEndpointNormalizedReciprocalSquare q) by simp, norm_conj, norm_conj]
  rfl

theorem mem_xiEndpointMaximalPacket_iff_amplitude_eq
    {D : Finset XiZeroCopy} {B beta : ℝ} (hgap : beta < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (htail : ∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) (q : XiZeroCopy) :
    q ∈ D ↔ xiEndpointBernsteinAtomAmplitudeBase q = B := by
  constructor
  · exact hD q
  · intro hq
    by_contra hnot
    have h := htail q hnot
    rw [hq] at h
    exact (not_le_of_gt hgap) h

theorem xiEndpointMaximalPacket_conj_closed
    {D : Finset XiZeroCopy} {B beta : ℝ} (hgap : beta < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (htail : ∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) :
    ∀ q ∈ D, xiZeroCopyConjEquiv q ∈ D := by
  intro q hq
  rw [mem_xiEndpointMaximalPacket_iff_amplitude_eq hgap hD htail,
    xiEndpointBernsteinAtomAmplitudeBase_conjEquiv]
  exact hD q hq

/-- Multiplicity of a normalized reciprocal-square coordinate, with all Xi copies retained. -/
def xiEndpointCoordinateMultiplicity (D : Finset XiZeroCopy) (u : ℂ) : ℕ :=
  (D.filter fun q => xiEndpointNormalizedReciprocalSquare q = u).card

theorem xiEndpointCoordinateMultiplicity_pos {D : Finset XiZeroCopy} {u : ℂ}
    (hu : u ∈ xiEndpointCoordinateSet D) : 0 < xiEndpointCoordinateMultiplicity D u := by
  classical
  obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu
  exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hqu⟩⟩

theorem xiEndpointCoordinateWeight_eq_multiplicity (D : Finset XiZeroCopy) (u : ℂ) :
    xiEndpointCoordinateWeight D u =
      (xiEndpointCoordinateMultiplicity D u : ℂ) *
        (primeArchEndpointHausdorffRadius : ℂ) * u := by
  classical
  have hconst : ∀ q ∈ D.filter (fun q => xiEndpointNormalizedReciprocalSquare q = u),
      xiZeroCopyReciprocalSquare q = (primeArchEndpointHausdorffRadius : ℂ) * u := by
    intro q hq
    have heq := (Finset.mem_filter.mp hq).2
    dsimp only [xiEndpointNormalizedReciprocalSquare] at heq
    have hR : (primeArchEndpointHausdorffRadius : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr primeArchEndpointHausdorffRadius_pos.ne'
    have h := (div_eq_iff hR).mp heq
    simpa only [mul_comm] using h
  rw [xiEndpointCoordinateWeight, finiteExponentialFiberCoefficient,
    Finset.sum_eq_card_nsmul hconst, nsmul_eq_mul]
  simp only [xiEndpointCoordinateMultiplicity]
  ring

theorem xiEndpointCoordinateMultiplicity_conj
    (D : Finset XiZeroCopy) (hD : ∀ q ∈ D, xiZeroCopyConjEquiv q ∈ D) (u : ℂ) :
    xiEndpointCoordinateMultiplicity D (conj u) = xiEndpointCoordinateMultiplicity D u := by
  classical
  have heq : (D.filter fun q => xiEndpointNormalizedReciprocalSquare q = conj u) =
      (D.filter fun q => xiEndpointNormalizedReciprocalSquare q = u).image xiZeroCopyConjEquiv := by
    ext q
    constructor
    · intro hq
      obtain ⟨hqD, hqu⟩ := Finset.mem_filter.mp hq
      apply Finset.mem_image.mpr
      refine ⟨xiZeroCopyConjEquiv q, Finset.mem_filter.mpr ⟨hD q hqD, ?_⟩,
        xiZeroCopyConjEquiv_apply_apply q⟩
      rw [xiEndpointNormalizedReciprocalSquare_conjEquiv, hqu]
      simp
    · intro hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hrD, hru⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hD r hrD, by
        rw [xiEndpointNormalizedReciprocalSquare_conjEquiv, hru]⟩
  rw [xiEndpointCoordinateMultiplicity, heq,
    Finset.card_image_of_injective _ xiZeroCopyConjEquiv.injective]
  rfl

theorem xiEndpointCoordinateSet_conj_mem
    (D : Finset XiZeroCopy) (hD : ∀ q ∈ D, xiZeroCopyConjEquiv q ∈ D)
    {u : ℂ} (hu : u ∈ xiEndpointCoordinateSet D) : conj u ∈ xiEndpointCoordinateSet D := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
  exact Finset.mem_image.mpr ⟨xiZeroCopyConjEquiv q, hD q hq,
    xiEndpointNormalizedReciprocalSquare_conjEquiv q⟩

end
end RHTower
