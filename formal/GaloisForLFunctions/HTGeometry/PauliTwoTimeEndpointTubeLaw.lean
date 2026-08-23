import GaloisForLFunctions.HTGeometry.PauliTwoTimeEndpointJacobianCoercivityLaw
import GaloisForLFunctions.HTGeometry.GaussianDiameterTubeUpperBound

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Same-draw coefficient set whose paired endpoints lie in one target tube. -/
def realTwoLocalPauliTwoTimeEndpointTube
    (n : ℕ) (target : QubitCStarMatrix n × QubitCStarMatrix n)
    (t ε : ℝ) : Set (TwoLocalPauliCoefficientSpace n) :=
  {z | z ∈ twoLocalPauliCoefficientBox n ∧
    dist (realTwoLocalPauliTwoTimeEndpoint z t
      (1 / (144 * (n : ℝ) ^ 3))) target ≤ ε}

/-- One paired target tube has system-size-controlled coefficient diameter.
This is the global one-sheet replacement for a fibre-multiplicity estimate. -/
theorem realTwoLocalPauliTwoTimeEndpointTube_pairwise_dist_le
    {n : ℕ} (hn : 1 ≤ n)
    (target : QubitCStarMatrix n × QubitCStarMatrix n)
    (t : ℝ) {ε : ℝ} (_hε : 0 ≤ ε) :
    ∀ x ∈ realTwoLocalPauliTwoTimeEndpointTube n target t ε,
      ∀ y ∈ realTwoLocalPauliTwoTimeEndpointTube n target t ε,
        dist x y ≤ 2304 * (n : ℝ) ^ 3 * ε := by
  intro x hx y hy
  have hglobal := realTwoLocalPauliTwoTimeEndpoint_lower_of_mem_box
    hn hx.1 hy.1 t
  have hpair :
      ‖realTwoLocalPauliTwoTimeEndpoint y t
          (1 / (144 * (n : ℝ) ^ 3)) -
        realTwoLocalPauliTwoTimeEndpoint x t
          (1 / (144 * (n : ℝ) ^ 3))‖ ≤ 2 * ε := by
    rw [← dist_eq_norm]
    calc
      dist (realTwoLocalPauliTwoTimeEndpoint y t
          (1 / (144 * (n : ℝ) ^ 3)))
          (realTwoLocalPauliTwoTimeEndpoint x t
            (1 / (144 * (n : ℝ) ^ 3))) ≤
        dist (realTwoLocalPauliTwoTimeEndpoint y t
            (1 / (144 * (n : ℝ) ^ 3))) target +
          dist target (realTwoLocalPauliTwoTimeEndpoint x t
            (1 / (144 * (n : ℝ) ^ 3))) := dist_triangle _ _ _
      _ ≤ ε + ε := by
        gcongr
        · exact hy.2
        · simpa [dist_comm] using hx.2
      _ = 2 * ε := by ring
  have hbase :
      (1 / (144 * (n : ℝ) ^ 3)) / 8 * dist x y ≤ 2 * ε := by
    rw [dist_eq_norm, norm_sub_rev]
    exact hglobal.trans hpair
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ 1152 * (n : ℝ) ^ 3 by positivity)
  have hcancel :
      (1152 * (n : ℝ) ^ 3) *
          ((1 / (144 * (n : ℝ) ^ 3)) / 8) = 1 := by
    field_simp
    norm_num
  rw [← mul_assoc, hcancel, one_mul] at hmul
  nlinarith

/-- Growing-dimensional Gaussian tube bound for every fixed occupied endpoint
pair.  Exponent is full active Pauli parameter count. -/
theorem stdGaussian_realTwoLocalPauliTwoTimeEndpointTube_le
    {n : ℕ} (hn : 1 ≤ n)
    (target : QubitCStarMatrix n × QubitCStarMatrix n)
    (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    stdGaussian (TwoLocalPauliCoefficientSpace n)
        (realTwoLocalPauliTwoTimeEndpointTube n target t ε) ≤
      gaussianDensityPeakENN ^ Fintype.card (PauliTracelessLabel n 2) *
        ((ENNReal.ofReal (2304 * (n : ℝ) ^ 3 * ε)) ^
            Fintype.card (PauliTracelessLabel n 2) *
          ENNReal.ofReal
            (Real.sqrt Real.pi ^ Fintype.card (PauliTracelessLabel n 2) /
              Real.Gamma
                (Fintype.card (PauliTracelessLabel n 2) / 2 + 1))) := by
  let i : Fin n := ⟨0, by omega⟩
  letI : Nonempty (PauliTracelessLabel n 2) :=
    ⟨⟨pauliZLabel i, by
      constructor
      · rw [pauliWeight_pauliZLabel]
        omega
      · exact pauliZLabel_ne_identity i⟩⟩
  apply stdGaussian_apply_le_of_pairwise_dist_le
  · positivity
  · exact realTwoLocalPauliTwoTimeEndpointTube_pairwise_dist_le
      hn target t hε

/-- Complete finite occupied-image pair-tube event. -/
def realTwoLocalPauliTwoTimeEndpointTargetUnionTube
    (n : ℕ) {C : Type*} [Fintype C]
    (target : C → QubitCStarMatrix n × QubitCStarMatrix n)
    (t ε : ℝ) : Set (TwoLocalPauliCoefficientSpace n) :=
  ⋃ c, realTwoLocalPauliTwoTimeEndpointTube n (target c) t ε

/-- Complete circuit union pays occupied endpoint-pair count exactly once;
every target retains full active-parameter exponent. -/
theorem stdGaussian_realTwoLocalPauliTwoTimeEndpointTargetUnionTube_le
    {n : ℕ} (hn : 1 ≤ n) {C : Type*} [Fintype C]
    (target : C → QubitCStarMatrix n × QubitCStarMatrix n)
    (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    stdGaussian (TwoLocalPauliCoefficientSpace n)
        (realTwoLocalPauliTwoTimeEndpointTargetUnionTube n target t ε) ≤
      (Fintype.card C : ℝ≥0∞) *
        (gaussianDensityPeakENN ^ Fintype.card (PauliTracelessLabel n 2) *
          ((ENNReal.ofReal (2304 * (n : ℝ) ^ 3 * ε)) ^
              Fintype.card (PauliTracelessLabel n 2) *
            ENNReal.ofReal
              (Real.sqrt Real.pi ^ Fintype.card (PauliTracelessLabel n 2) /
                Real.Gamma
                  (Fintype.card (PauliTracelessLabel n 2) / 2 + 1)))) := by
  unfold realTwoLocalPauliTwoTimeEndpointTargetUnionTube
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc
    ∑ c : C, stdGaussian (TwoLocalPauliCoefficientSpace n)
        (realTwoLocalPauliTwoTimeEndpointTube n (target c) t ε) ≤
      ∑ _c : C,
        gaussianDensityPeakENN ^ Fintype.card (PauliTracelessLabel n 2) *
          ((ENNReal.ofReal (2304 * (n : ℝ) ^ 3 * ε)) ^
              Fintype.card (PauliTracelessLabel n 2) *
            ENNReal.ofReal
              (Real.sqrt Real.pi ^ Fintype.card (PauliTracelessLabel n 2) /
                Real.Gamma
                  (Fintype.card (PauliTracelessLabel n 2) / 2 + 1))) := by
      apply Finset.sum_le_sum
      intro c _
      exact stdGaussian_realTwoLocalPauliTwoTimeEndpointTube_le
        hn (target c) t hε
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end

end GaloisForLFunctions.HTGeometry
