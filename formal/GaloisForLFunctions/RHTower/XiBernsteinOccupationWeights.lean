import GaloisForLFunctions.RHTower.XiBernsteinOccupationFibres

/-!
# Exact multiplicity recovery from Bernstein occupation weights

Every occupied index corresponds to exactly one conjugate pair of maximal reciprocal-square
coordinates. Its positive atom weight determines their common fibre multiplicity uniquely.
-/

open Complex
open scoped BigOperators Real unitInterval ComplexConjugate

namespace RHTower

noncomputable section

/-- The limiting mass at an occupation point, after equal-coordinate fibres were aggregated. -/
def xiEndpointOccupationAtomWeight (D : Finset XiZeroCopy) (p : I) : ℝ :=
  ∑ u ∈ (xiEndpointCoordinateSet D).filter (fun u => bernsteinAffineOccupation u = p),
    ‖xiEndpointCoordinateWeight D u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u

theorem xiEndpointOccupationAtomWeight_pos_iff
    (D : Finset XiZeroCopy) {B : ℝ} (hB : 1 < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) (p : I) :
    0 < xiEndpointOccupationAtomWeight D p ↔
      ∃ u ∈ xiEndpointCoordinateSet D, bernsteinAffineOccupation u = p := by
  classical
  have hterm : ∀ u ∈ xiEndpointCoordinateSet D,
      0 < ‖xiEndpointCoordinateWeight D u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u := by
    intro u hu
    have hc := norm_pos_iff.mpr (xiEndpointCoordinateWeight_ne_zero hu)
    obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu
    have him : u.im ≠ 0 := by
      rw [← hqu]
      exact (xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude q
        (by rw [hD q hq]; exact hB)).2
    exact mul_pos (sq_pos_of_pos hc) (bernsteinAffineRowHalfOrderConstant_pos
      (fun heq => him (by rw [heq]; rfl)) (fun heq => him (by rw [heq]; rfl)))
  constructor
  · intro hpos
    by_contra hnot
    have he : (xiEndpointCoordinateSet D).filter (fun u => bernsteinAffineOccupation u = p) = ∅ := by
      ext u
      constructor
      · intro hu
        exact False.elim (hnot ⟨u, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩)
      · simp
    simp only [xiEndpointOccupationAtomWeight, he, Finset.sum_empty, lt_self_iff_false] at hpos
  · rintro ⟨u, hu, hp⟩
    apply Finset.sum_pos'
      (fun v hv => (hterm v (Finset.mem_filter.mp hv).1).le)
    exact ⟨u, Finset.mem_filter.mpr ⟨hu, hp⟩, hterm u hu⟩

theorem xiEndpointOccupation_coordinate_fibre
    (D : Finset XiZeroCopy) {B : ℝ}
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (hconj : ∀ q ∈ D, xiZeroCopyConjEquiv q ∈ D)
    {u : ℂ} (hu : u ∈ xiEndpointCoordinateSet D) :
    (xiEndpointCoordinateSet D).filter (fun v => bernsteinAffineOccupation v =
      bernsteinAffineOccupation u) = {u, conj u} := by
  classical
  have hamp : ∀ v ∈ xiEndpointCoordinateSet D, ‖v‖ + ‖1 - v‖ = B := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    exact hD q hq
  ext v
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, hp⟩
    exact (bernsteinAffineOccupation_eq_iff_of_amplitude_eq
      ((hamp v hv).trans (hamp u hu).symm)).mp hp
  · rintro (rfl | rfl)
    · exact ⟨hu, rfl⟩
    · exact ⟨xiEndpointCoordinateSet_conj_mem D hconj hu, bernsteinAffineOccupation_conj u⟩

theorem xiEndpointOccupationAtomWeight_eq_multiplicity
    (D : Finset XiZeroCopy) {B : ℝ} (hB : 1 < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (hconj : ∀ q ∈ D, xiZeroCopyConjEquiv q ∈ D)
    {u : ℂ} (hu : u ∈ xiEndpointCoordinateSet D) :
    xiEndpointOccupationAtomWeight D (bernsteinAffineOccupation u) =
      2 * primeArchEndpointHausdorffRadius ^ 2 * B ^ 2 *
        (bernsteinAffineOccupation u : ℝ) ^ 2 *
        (xiEndpointCoordinateMultiplicity D u : ℝ) ^ 2 *
        bernsteinAffineRowHalfOrderConstant u := by
  classical
  obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu
  have hamp : ‖u‖ + ‖1 - u‖ = B := by rw [← hqu]; exact hD q hq
  have him : u.im ≠ 0 := by
    rw [← hqu]
    exact (xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude q
      (by rw [hD q hq]; exact hB)).2
  have hne : u ≠ conj u := by
    intro heq
    have h := congrArg Complex.im heq
    simp only [Complex.conj_im] at h
    exact him (by linarith)
  have hnorm : ‖u‖ = B * (bernsteinAffineOccupation u : ℝ) := by
    change ‖u‖ = B * (‖u‖ / (‖u‖ + ‖1 - u‖))
    rw [hamp]
    field_simp [ne_of_gt (lt_trans zero_lt_one hB)]
  rw [xiEndpointOccupationAtomWeight, xiEndpointOccupation_coordinate_fibre D hD hconj hu,
    Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    xiEndpointCoordinateWeight_eq_multiplicity, xiEndpointCoordinateWeight_eq_multiplicity,
    xiEndpointCoordinateMultiplicity_conj D hconj,
    bernsteinAffineRowHalfOrderConstant_conj]
  simp only [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos primeArchEndpointHausdorffRadius_pos, norm_conj, hnorm]
  ring

/-- The observed atom weight determines the positive integer fibre multiplicity uniquely. -/
theorem xiEndpointCoordinateMultiplicity_eq_iff_atomWeight
    (D : Finset XiZeroCopy) {B : ℝ} (hB : 1 < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (hconj : ∀ q ∈ D, xiZeroCopyConjEquiv q ∈ D)
    {u : ℂ} (hu : u ∈ xiEndpointCoordinateSet D) (N : ℕ) :
    xiEndpointCoordinateMultiplicity D u = N ↔
      xiEndpointOccupationAtomWeight D (bernsteinAffineOccupation u) =
        2 * primeArchEndpointHausdorffRadius ^ 2 * B ^ 2 *
          (bernsteinAffineOccupation u : ℝ) ^ 2 * (N : ℝ) ^ 2 *
          bernsteinAffineRowHalfOrderConstant u := by
  have hweight := xiEndpointOccupationAtomWeight_eq_multiplicity D hB hD hconj hu
  obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu
  have him : u.im ≠ 0 := by
    rw [← hqu]
    exact (xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude q
      (by rw [hD q hq]; exact hB)).2
  have hu0 : u ≠ 0 := fun heq => him (by rw [heq]; rfl)
  have hu1 : u ≠ 1 := fun heq => him (by rw [heq]; rfl)
  have hp : 0 < (bernsteinAffineOccupation u : ℝ) :=
    div_pos (norm_pos_iff.mpr hu0) (bernsteinAffineAmplitude_pos u)
  have hkap := bernsteinAffineRowHalfOrderConstant_pos hu0 hu1
  have hB0 : 0 < B := lt_trans zero_lt_one hB
  have hR0 := primeArchEndpointHausdorffRadius_pos
  let K := 2 * primeArchEndpointHausdorffRadius ^ 2 * B ^ 2 *
    (bernsteinAffineOccupation u : ℝ) ^ 2 * bernsteinAffineRowHalfOrderConstant u
  have hK : 0 < K := by dsimp [K]; positivity
  constructor
  · intro hN
    simpa only [hN] using hweight
  · intro hN
    have heq : K * (xiEndpointCoordinateMultiplicity D u : ℝ) ^ 2 = K * (N : ℝ) ^ 2 := by
      dsimp only [K]
      nlinarith [hweight.symm.trans hN]
    have hsq := mul_left_cancel₀ hK.ne' heq
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hD0 : 0 ≤ (xiEndpointCoordinateMultiplicity D u : ℝ) := Nat.cast_nonneg _
    have hsame : (xiEndpointCoordinateMultiplicity D u : ℝ) = (N : ℝ) :=
      le_antisymm ((sq_le_sq₀ hD0 hN0).mp hsq.le) ((sq_le_sq₀ hN0 hD0).mp hsq.ge)
    exact_mod_cast hsame

end
end RHTower
