import GaloisForLFunctions.RHTower.AtomicBernsteinPacketIndexAsymptotic
import GaloisForLFunctions.RHTower.XiBernsteinPurityHalfOrderAsymptotic

/-!
# Index asymptotics of the actual prime--archimedean source

The complete maximal Xi packet, when superunit, supplies every separation and summability
condition needed for the source-defined bounded-test law at the fixed endpoint radius.
-/

open Filter Topology
open scoped BigOperators Real unitInterval

namespace RHTower

noncomputable section

/-- Source-defined coefficient-index energy at the one fixed PA endpoint radius. -/
def primeArchEndpointBernsteinIndexEnergy (g : I → ℝ) (n : ℕ) : ℝ :=
  ∑ k : Fin (n + 1), g (bernstein.z k) * ‖primeArchEndpointBernsteinPacket n k‖ ^ 2

theorem primeArchEndpointBernsteinIndexEnergy_eq_atomic (g : I → ℝ) (n : ℕ) :
    primeArchEndpointBernsteinIndexEnergy g n =
      atomicBernsteinPacketIndexEnergy xiZeroCopyReciprocalSquare
        xiEndpointNormalizedReciprocalSquare g n := by
  rw [primeArchEndpointBernsteinIndexEnergy, atomicBernsteinPacketIndexEnergy,
    primeArchEndpointBernsteinPacket_eq_atomic]

theorem tendsto_primeArchEndpointBernsteinIndexEnergy_of_maximalPacket
    (D : Finset XiZeroCopy) {B beta : ℝ} (hB : 1 < B)
    (hbeta0 : 0 ≤ beta) (hbeta : beta < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (htail : ∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta)
    {g : I → ℝ} {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |g x| ≤ M)
    (hg : ∀ u ∈ xiEndpointCoordinateSet D, ContinuousAt g (bernsteinAffineOccupation u)) :
    Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      primeArchEndpointBernsteinIndexEnergy g n) atTop
      (nhds (∑ u ∈ xiEndpointCoordinateSet D, ‖xiEndpointCoordinateWeight D u‖ ^ 2 *
        bernsteinAffineRowHalfOrderConstant u * g (bernsteinAffineOccupation u))) := by
  classical
  have hamp : ∀ u ∈ xiEndpointCoordinateSet D, ‖u‖ + ‖1 - u‖ = B := by
    intro u hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    exact hD q hq
  have him : ∀ u ∈ xiEndpointCoordinateSet D, u.im ≠ 0 := by
    intro u hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    exact (xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude q
      (by rw [hD q hq]; exact hB)).2
  have hzero : ∀ u ∈ xiEndpointCoordinateSet D, u ≠ 0 := by
    intro u hu heq
    exact him u hu (by rw [heq]; rfl)
  have hone : ∀ u ∈ xiEndpointCoordinateSet D, u ≠ 1 := by
    intro u hu heq
    exact him u hu (by rw [heq]; rfl)
  have hcross : ∀ u ∈ xiEndpointCoordinateSet D, ∀ v ∈ xiEndpointCoordinateSet D, u ≠ v →
      ∃ gamma : ℝ, 0 ≤ gamma ∧ gamma < B ^ 2 ∧
        ∀ n : ℕ, ‖reflectedBernsteinCrossMoment u v n‖ ≤ gamma ^ n := by
    intro u hu v hv huv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    exact exists_uniform_mixedXiBernsteinCrossMoment_gap_of_distinct_maximal_coordinates
      hB (hD q hq) (hD r hr) huv
  have hlead := tendsto_finiteBernsteinCoordinatePacketIndexEnergy
    (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) (by linarith : 0 < B)
    hamp hzero hone hcross hM hbound hg
  have h := tendsto_atomicBernsteinPacketIndexEnergy_of_finiteCoordinatePacket
    D xiZeroCopyReciprocalSquare xiEndpointNormalizedReciprocalSquare
    summable_xiZeroCopyReciprocalSquare (by linarith : 0 < B) hbeta0 hbeta
    (fun q hq => (hD q hq).le) htail hM hbound hlead
  simpa only [← primeArchEndpointBernsteinIndexEnergy_eq_atomic] using h

/-- The alternative with an off-line divisor has one complete finite packet governing every
bounded test continuous at its occupation points. No off-line divisor is asserted to exist. -/
theorem exists_primeArchEndpointBernstein_index_law_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ D : Finset XiZeroCopy, ∃ B beta : ℝ,
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
      (∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
      (∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) ∧
      (∀ (g : I → ℝ) (M : ℝ), 0 ≤ M → (∀ x, |g x| ≤ M) →
        (∀ u ∈ xiEndpointCoordinateSet D, ContinuousAt g (bernsteinAffineOccupation u)) →
        Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
          primeArchEndpointBernsteinIndexEnergy g n) atTop
          (nhds (∑ u ∈ xiEndpointCoordinateSet D, ‖xiEndpointCoordinateWeight D u‖ ^ 2 *
            bernsteinAffineRowHalfOrderConstant u * g (bernsteinAffineOccupation u)))) := by
  obtain ⟨D, B, beta, hB, hbeta1, hbeta, hDne, hD, htail⟩ :=
    exists_uniformlySeparated_maximal_xiEndpointAmplitudePacket_of_not_rh hRH
  refine ⟨D, B, beta, hB, hbeta1, hbeta, hDne, hD, htail, ?_⟩
  intro g M hM hbound hg
  exact tendsto_primeArchEndpointBernsteinIndexEnergy_of_maximalPacket D hB
    (by linarith) hbeta hD htail hM hbound hg

end
end RHTower
