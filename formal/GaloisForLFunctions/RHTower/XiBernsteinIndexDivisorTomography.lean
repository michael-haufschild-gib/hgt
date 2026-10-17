import GaloisForLFunctions.RHTower.XiBernsteinIndexMeasures
import GaloisForLFunctions.RHTower.XiBernsteinIndexProbability

/-!
# Fixed-scale Bernstein index tomography of the dominant Xi divisor

The actual source index law determines dominant reciprocal-square coordinates up to conjugation
and recovers their complete fibre multiplicities. All source conditions are discharged.
-/

open Complex Filter Topology MeasureTheory
open scoped BigOperators Real unitInterval ComplexConjugate

namespace RHTower

noncomputable section

/-- An unconditional source-divisor alternative. If the divisor has an off-line part, one fixed
PA scale detects its complete dominant reciprocal-square packet through coefficient-index
measures, with exact coordinates modulo conjugation and exact fibre multiplicities. -/
theorem primeArchEndpointBernstein_index_divisor_tomography :
    RiemannHypothesis ∨ ∃ D : Finset XiZeroCopy, ∃ B beta : ℝ,
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
      (∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
      (∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) ∧
      (∀ q, q ∈ D ↔ xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
      Tendsto (fun n : ℕ =>
        primeArchEndpointBernsteinIndexEnergy (fun _ => 1) n ^ ((n : ℝ)⁻¹))
        atTop (nhds (B ^ 2)) ∧
      Tendsto (primeArchEndpointBernsteinIndexMeasure B) atTop
        (nhds (xiEndpointBernsteinOccupationMeasure D)) ∧
      0 < xiEndpointBernsteinOccupationMass D ∧
      IsProbabilityMeasure (xiEndpointBernsteinOccupationProbability D : Measure I) ∧
      Tendsto primeArchEndpointBernsteinIndexProbability atTop
        (nhds (xiEndpointBernsteinOccupationProbability D)) ∧
      (∀ p : I, 0 < (xiEndpointBernsteinOccupationMeasure D : Measure I).real {p} ↔
        ∃ u ∈ xiEndpointCoordinateSet D, bernsteinAffineOccupation u = p) ∧
      (∀ u ∈ xiEndpointCoordinateSet D,
        u.im ≠ 0 ∧
        u.re = (1 + B ^ 2 * (2 * (bernsteinAffineOccupation u : ℝ) - 1)) / 2 ∧
        u.im ^ 2 = B ^ 2 * (bernsteinAffineOccupation u : ℝ) ^ 2 - u.re ^ 2 ∧
        (xiEndpointCoordinateSet D).filter (fun v => bernsteinAffineOccupation v =
          bernsteinAffineOccupation u) = {u, conj u} ∧
        ∀ N : ℕ, xiEndpointCoordinateMultiplicity D u = N ↔
          (xiEndpointBernsteinOccupationMeasure D : Measure I).real {bernsteinAffineOccupation u} =
            2 * primeArchEndpointHausdorffRadius ^ 2 * B ^ 2 *
              (bernsteinAffineOccupation u : ℝ) ^ 2 * (N : ℝ) ^ 2 *
              bernsteinAffineRowHalfOrderConstant u) := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  obtain ⟨D, B, beta, hB, hbeta1, hbeta, hDne, hD, htail⟩ :=
    exists_uniformlySeparated_maximal_xiEndpointAmplitudePacket_of_not_rh hRH
  have hbeta0 : 0 ≤ beta := le_trans zero_le_one hbeta1.le
  have hconj := xiEndpointMaximalPacket_conj_closed hbeta hD htail
  have him : ∀ u ∈ xiEndpointCoordinateSet D, u.im ≠ 0 := by
    intro u hu
    obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu
    rw [← hqu]
    exact (xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude q
      (by rw [hD q hq]; exact hB)).2
  have hkap : ∀ u ∈ xiEndpointCoordinateSet D, 0 ≤ bernsteinAffineRowHalfOrderConstant u := by
    intro u hu
    exact (bernsteinAffineRowHalfOrderConstant_pos
      (fun heq => him u hu (by rw [heq]; rfl))
      (fun heq => him u hu (by rw [heq]; rfl))).le
  have hprob := tendsto_primeArchEndpointBernsteinIndexProbability_of_maximalPacket
    D hDne hB hbeta0 hbeta hD htail
  refine Or.inr ⟨D, B, beta, hB, hbeta1, hbeta, hDne, hD, htail,
    mem_xiEndpointMaximalPacket_iff_amplitude_eq hbeta hD htail,
    tendsto_primeArchEndpointBernstein_index_mass_root_of_maximalPacket hRH D hDne hbeta hD htail,
    tendsto_primeArchEndpointBernsteinIndexMeasure_of_maximalPacket D hB hbeta0 hbeta hD htail,
    xiEndpointBernsteinOccupationMass_pos D hDne hB hD, hprob.1, hprob.2, ?_, ?_⟩
  · intro p
    rw [xiEndpointBernsteinOccupationMeasure_singleton D hkap]
    exact xiEndpointOccupationAtomWeight_pos_iff D hB hD p
  · intro u hu
    have hamp : ‖u‖ + ‖1 - u‖ = B := by
      obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu
      rw [← hqu]
      exact hD q hq
    refine ⟨him u hu, ?_, ?_, xiEndpointOccupation_coordinate_fibre D hD hconj hu, ?_⟩
    · simpa only [hamp] using re_eq_bernsteinAffineOccupation u
    · simpa only [hamp] using im_sq_eq_bernsteinAffineOccupation u
    · intro N
      rw [xiEndpointBernsteinOccupationMeasure_singleton D hkap]
      exact xiEndpointCoordinateMultiplicity_eq_iff_atomWeight D hB hD hconj hu N

end
end RHTower
