import GaloisForLFunctions.HTGeometry.FiniteRealAtomicMeasure
import GaloisForLFunctions.RHTower.XiBernsteinIndexNormalization

/-!
# Probability limits of the actual Bernstein index profile

Every actual source packet has positive energy and defines a probability measure.
The normalized maximal-divisor weights give its weak limit.
-/

open Filter Topology MeasureTheory
open scoped BigOperators Real unitInterval
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

def primeArchEndpointBernsteinIndexProbability (n : ℕ) : FiniteMeasure I :=
  normalizedFiniteRealAtomicMeasure Finset.univ (fun k : Fin (n + 1) => bernstein.z k)
    (fun k => ‖primeArchEndpointBernsteinPacket n k‖ ^ 2)

def xiEndpointBernsteinOccupationProbability (D : Finset XiZeroCopy) : FiniteMeasure I :=
  normalizedFiniteRealAtomicMeasure (xiEndpointCoordinateSet D) bernsteinAffineOccupation
    (fun u => ‖xiEndpointCoordinateWeight D u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u)

theorem isProbabilityMeasure_primeArchEndpointBernsteinIndexProbability (n : ℕ) :
    IsProbabilityMeasure (primeArchEndpointBernsteinIndexProbability n : Measure I) := by
  apply isProbabilityMeasure_normalizedFiniteRealAtomicMeasure _ _ _ (fun _ _ => sq_nonneg _)
  simpa only [primeArchEndpointBernsteinIndexEnergy, one_mul]
    using primeArchEndpointBernsteinIndexEnergy_one_pos n

theorem integral_primeArchEndpointBernsteinIndexProbability (n : ℕ) (g : I → ℝ) :
    (∫ p, g p ∂(primeArchEndpointBernsteinIndexProbability n : Measure I)) =
      primeArchEndpointBernsteinIndexEnergy g n /
        primeArchEndpointBernsteinIndexEnergy (fun _ => 1) n := by
  have hpos : 0 < ∑ k : Fin (n + 1), ‖primeArchEndpointBernsteinPacket n k‖ ^ 2 := by
    simpa only [primeArchEndpointBernsteinIndexEnergy, one_mul]
      using primeArchEndpointBernsteinIndexEnergy_one_pos n
  rw [primeArchEndpointBernsteinIndexProbability, integral_normalizedFiniteRealAtomicMeasure
    _ _ _ (fun _ _ => sq_nonneg _) hpos]
  simp only [primeArchEndpointBernsteinIndexEnergy, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem isProbabilityMeasure_xiEndpointBernsteinOccupationProbability
    (D : Finset XiZeroCopy)
    (hw : ∀ u ∈ xiEndpointCoordinateSet D,
      0 ≤ ‖xiEndpointCoordinateWeight D u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u)
    (hpos : 0 < xiEndpointBernsteinOccupationMass D) :
    IsProbabilityMeasure (xiEndpointBernsteinOccupationProbability D : Measure I) :=
  isProbabilityMeasure_normalizedFiniteRealAtomicMeasure _ _ _ hw hpos

theorem integral_xiEndpointBernsteinOccupationProbability
    (D : Finset XiZeroCopy)
    (hw : ∀ u ∈ xiEndpointCoordinateSet D,
      0 ≤ ‖xiEndpointCoordinateWeight D u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u)
    (hpos : 0 < xiEndpointBernsteinOccupationMass D) (g : I → ℝ) :
    (∫ p, g p ∂(xiEndpointBernsteinOccupationProbability D : Measure I)) =
      (∑ u ∈ xiEndpointCoordinateSet D, ‖xiEndpointCoordinateWeight D u‖ ^ 2 *
        bernsteinAffineRowHalfOrderConstant u * g (bernsteinAffineOccupation u)) /
          xiEndpointBernsteinOccupationMass D :=
  integral_normalizedFiniteRealAtomicMeasure _ _ _ hw hpos g

theorem tendsto_primeArchEndpointBernsteinIndexProbability_of_maximalPacket
    (D : Finset XiZeroCopy) {B beta : ℝ} (hDne : D.Nonempty) (hB : 1 < B)
    (hbeta0 : 0 ≤ beta) (hbeta : beta < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (htail : ∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) :
    IsProbabilityMeasure (xiEndpointBernsteinOccupationProbability D : Measure I) ∧
      Tendsto primeArchEndpointBernsteinIndexProbability atTop
        (nhds (xiEndpointBernsteinOccupationProbability D)) := by
  have hpos := xiEndpointBernsteinOccupationMass_pos D hDne hB hD
  have hw : ∀ u ∈ xiEndpointCoordinateSet D,
      0 ≤ ‖xiEndpointCoordinateWeight D u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u := by
    intro u hu
    obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu
    have him : u.im ≠ 0 := by
      rw [← hqu]
      exact (xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude q
        (by rw [hD q hq]; exact hB)).2
    exact mul_nonneg (sq_nonneg _) (bernsteinAffineRowHalfOrderConstant_pos
      (fun heq => him (by rw [heq]; rfl)) (fun heq => him (by rw [heq]; rfl))).le
  refine ⟨isProbabilityMeasure_xiEndpointBernsteinOccupationProbability D hw hpos, ?_⟩
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro g
  simp only [integral_primeArchEndpointBernsteinIndexProbability,
    integral_xiEndpointBernsteinOccupationProbability D hw hpos]
  exact tendsto_primeArchEndpointBernstein_normalized_index_test D hDne hB hbeta0 hbeta hD htail
    (norm_nonneg g) (fun p => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm p)
    (fun u hu => g.continuous.continuousAt)

end
end RHTower
