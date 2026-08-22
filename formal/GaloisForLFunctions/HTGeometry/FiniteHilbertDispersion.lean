import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Exact finite Hilbert dispersion

The ordered pairwise squared-distance energy of a finite real Hilbert packet is exactly its
weighted second moment minus the squared norm of its weighted resultant.  No sign or normalization
condition on weights is required.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Ordered pairwise squared-distance energy is twice the weighted moment defect. -/
theorem finite_pairwise_hilbert_dispersion
    (s : Finset ι) (w : ι → ℝ) (v : ι → E) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * ‖v i‖ ^ 2) -
        ‖∑ i ∈ s, w i • v i‖ ^ 2) := by
  have hleft :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i‖ ^ 2) =
        (∑ i ∈ s, w i * ‖v i‖ ^ 2) * (∑ j ∈ s, w j) := by
    calc
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i‖ ^ 2 =
          ∑ i ∈ s, (w i * ‖v i‖ ^ 2) * (∑ j ∈ s, w j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ i ∈ s, w i * ‖v i‖ ^ 2) * (∑ j ∈ s, w j) := by
            rw [Finset.sum_mul]
  have hright :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v j‖ ^ 2) =
        (∑ i ∈ s, w i) * (∑ j ∈ s, w j * ‖v j‖ ^ 2) := by
    calc
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v j‖ ^ 2 =
          ∑ i ∈ s, w i * (∑ j ∈ s, w j * ‖v j‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ i ∈ s, w i) * (∑ j ∈ s, w j * ‖v j‖ ^ 2) := by
            calc
              ∑ i ∈ s, w i * (∑ j ∈ s, w j * ‖v j‖ ^ 2) =
                  ∑ i ∈ s, (∑ j ∈ s, w j * ‖v j‖ ^ 2) * w i := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
              _ = (∑ j ∈ s, w j * ‖v j‖ ^ 2) * (∑ i ∈ s, w i) := by
                    exact (Finset.mul_sum s w (∑ j ∈ s, w j * ‖v j‖ ^ 2)).symm
              _ = (∑ i ∈ s, w i) * (∑ j ∈ s, w j * ‖v j‖ ^ 2) := by ring
  have hinner :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * inner ℝ (v i) (v j)) =
        inner ℝ (∑ i ∈ s, w i • v i) (∑ j ∈ s, w j • v j) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    simp_rw [real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hmiddle :
      (∑ i ∈ s, ∑ j ∈ s, 2 * (w i * w j * inner ℝ (v i) (v j))) =
        2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * inner ℝ (v i) (v j)) := by
    calc
      ∑ i ∈ s, ∑ j ∈ s, 2 * (w i * w j * inner ℝ (v i) (v j)) =
          ∑ i ∈ s, 2 * (∑ j ∈ s, w i * w j * inner ℝ (v i) (v j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = 2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * inner ℝ (v i) (v j)) := by
            rw [Finset.mul_sum]
  calc
    ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s,
          (w i * w j * ‖v i‖ ^ 2 -
            2 * (w i * w j * inner ℝ (v i) (v j)) + w i * w j * ‖v j‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [norm_sub_sq_real]
          ring
    _ = (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i‖ ^ 2) -
          2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * inner ℝ (v i) (v j)) +
            (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v j‖ ^ 2) := by
          simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [hmiddle]
    _ = 2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * ‖v i‖ ^ 2) -
        ‖∑ i ∈ s, w i • v i‖ ^ 2) := by
          rw [hleft, hright, hinner, real_inner_self_eq_norm_sq]
          ring

/-- Exact finite weighted Hilbert variance.  This is the unconditional form of `(AH7)`. -/
theorem finite_weighted_hilbert_dispersion
    (s : Finset ι) (w : ι → ℝ) (v : ι → E) :
    ‖∑ i ∈ s, w i • v i‖ ^ 2 =
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * ‖v i‖ ^ 2) -
        (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2 := by
  rw [finite_pairwise_hilbert_dispersion]
  ring

/-- On a zero-total-weight packet, squared Hilbert distance is conditionally negative. -/
theorem finite_pairwise_hilbert_dispersion_of_sum_eq_zero
    (s : Finset ι) (w : ι → ℝ) (v : ι → E) (hw : ∑ i ∈ s, w i = 0) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2) =
      -2 * ‖∑ i ∈ s, w i • v i‖ ^ 2 := by
  rw [finite_pairwise_hilbert_dispersion, hw]
  ring

/-- Conditional negative type of squared Hilbert distance for every zero-total-weight packet. -/
theorem finite_pairwise_hilbert_dispersion_nonpos_of_sum_eq_zero
    (s : Finset ι) (w : ι → ℝ) (v : ι → E) (hw : ∑ i ∈ s, w i = 0) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2) ≤ 0 := by
  rw [finite_pairwise_hilbert_dispersion_of_sum_eq_zero s w v hw]
  positivity

/-- Equality in conditional negative type is exactly vanishing of the weighted resultant. -/
theorem finite_pairwise_hilbert_dispersion_eq_zero_iff_of_sum_eq_zero
    (s : Finset ι) (w : ι → ℝ) (v : ι → E) (hw : ∑ i ∈ s, w i = 0) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2) = 0 ↔
      ∑ i ∈ s, w i • v i = 0 := by
  rw [finite_pairwise_hilbert_dispersion_of_sum_eq_zero s w v hw]
  constructor
  · intro h
    have hnorm : ‖∑ i ∈ s, w i • v i‖ = 0 := by
      nlinarith [norm_nonneg (∑ i ∈ s, w i • v i)]
    exact norm_eq_zero.mp hnorm
  · intro h
    rw [h]
    norm_num

end GaloisForLFunctions.HTGeometry
