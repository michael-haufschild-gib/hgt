import GaloisForLFunctions.HTGeometry.CompactConnectedAbelianGenerators
import GaloisForLFunctions.HTGeometry.CompactGroupCoveringVolume

/-!
# The compact-group minimax return volume law

For a compact connected second-countable abelian group with a bi-invariant extended metric and
Haar probability measure, worst dense-orbit recurrence at resolution `eps` is trapped between the
reciprocal target volume and the reciprocal covering volume:

* every rotation returns inside `eps` by the covering number at radius `eps/2`;
* some topological generator avoids the `eps`-ball through its first `L` powers whenever
  `L * mu(ball 1 eps) < 1`;
* the covering number at radius `eps/2` is at most the reciprocal volume of the ball of radius
  `eps/4`.
-/

open Metric MeasureTheory Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

variable {G : Type*} [PseudoEMetricSpace G] [CommGroup G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G] [ConnectedSpace G]

/-- **Compact-group minimax return volume law.**  The universal covering deadline, the
generator-based lower mechanism, and the covering–volume sandwich, for a compact connected
second-countable abelian group with a bi-invariant metric. -/
theorem compactGroup_minimax_return_volume_law
    (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] {ε : ℝ≥0} (hε : ε ≠ 0) :
    (∀ α : G, ∃ n : ℕ, 0 < n ∧ (n : ℕ∞) ≤ Metric.coveringNumber (ε / 2) (Set.univ : Set G) ∧
        edist (α ^ n) 1 ≤ (ε : ℝ≥0∞)) ∧
      (∀ L : ℕ, (L : ℝ≥0∞) * μ (eball (1 : G) (ε : ℝ≥0∞)) < 1 →
        ∃ α ∈ denseGenerators G, ∀ n : ℕ, 0 < n → n ≤ L → α ^ n ∉ eball (1 : G) (ε : ℝ≥0∞)) ∧
      (Metric.coveringNumber (ε / 2) (Set.univ : Set G) : ℝ≥0∞) *
          μ (eball (1 : G) ((ε : ℝ≥0∞) / 4)) ≤ 1 ∧
      1 ≤ (Metric.coveringNumber ε (Set.univ : Set G) : ℝ≥0∞) *
          μ (closedEBall (1 : G) (ε : ℝ≥0∞)) := by
  have hε2 : ε / 2 ≠ 0 := by
    simpa using hε
  refine ⟨fun α => ?_, fun L hL => ?_, ?_, one_le_coveringNumber_mul_measure_closedEBall μ hε⟩
  · obtain ⟨n, hn, hcard, hdist⟩ :=
      exists_pow_return_le_two_mul_coveringNumber (G := G) α (ε / 2) hε2
    refine ⟨n, hn, hcard, ?_⟩
    calc edist (α ^ n) 1 ≤ 2 * ((ε / 2 : ℝ≥0) : ℝ≥0∞) := hdist
      _ = (ε : ℝ≥0∞) := by
        rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul]
        congr 1
        field_simp
  · exact exists_denseGenerator_avoiding_of_measure_budget μ _
      Metric.isOpen_eball.measurableSet L hL
  · have h := coveringNumber_mul_measure_eball_le_one μ hε2
    have hcast : (((ε / 2 : ℝ≥0) : ℝ≥0∞) / 2) = (ε : ℝ≥0∞) / 4 := by
      rw [ENNReal.coe_div (by norm_num)]
      rw [ENNReal.coe_ofNat]
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
        ← ENNReal.mul_inv (by norm_num) (by norm_num)]
      norm_num
    rwa [hcast] at h

end GaloisForLFunctions.HTGeometry
