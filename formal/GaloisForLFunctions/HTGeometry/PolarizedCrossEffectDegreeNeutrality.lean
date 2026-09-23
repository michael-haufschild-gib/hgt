import GaloisForLFunctions.HTGeometry.ConstitutivePolarizedCrossEffect

/-!
# Degreewise information neutrality of the polarized cross-effect transform

Complete functional-equation transport changes each polarized coordinate only by the sign
`(−1)^{|S|}`, so it preserves the energy of every interaction-degree band.  This is exactly
`(PC.11)`: information neutrality, and therefore no selection.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- **(PC.11)  Degreewise information neutrality.**  The complement action preserves the polarized
energy carried by every set of interaction degrees. -/
theorem polarizedPacketTransform_degree_energy_neutral
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (c : Finset I → ℝ) (E : Finset ℕ) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset I => S.card ∈ E),
        (polarizedPacketTransform (fun i => 1 - q i) (rawComplementPacket c) S) ^ (2 : ℕ)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset I => S.card ∈ E),
        (polarizedPacketTransform q c S) ^ (2 : ℕ) := by
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [polarizedPacketTransform_complement_intertwining hq0 hq1]
  have hsq : ((-1 : ℝ) ^ S.card) ^ (2 : ℕ) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [mul_pow, hsq, one_mul]

/-- The total polarized energy is preserved: the degree band may be everything. -/
theorem polarizedPacketTransform_total_energy_neutral
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (c : Finset I → ℝ) :
    ∑ S : Finset I, (polarizedPacketTransform (fun i => 1 - q i) (rawComplementPacket c) S) ^ (2 : ℕ)
      = ∑ S : Finset I, (polarizedPacketTransform q c S) ^ (2 : ℕ) := by
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [polarizedPacketTransform_complement_intertwining hq0 hq1]
  have hsq : ((-1 : ℝ) ^ S.card) ^ (2 : ℕ) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [mul_pow, hsq, one_mul]

end

end GaloisForLFunctions.HTGeometry
