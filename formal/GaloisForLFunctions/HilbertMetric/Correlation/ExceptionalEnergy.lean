import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Removing sources from a Gram energy

A finite packet is split into retained and exceptional sources. Polarization
controls the change in its full Gram energy, including signed cross terms.
The square-root energy changes by at most the norm of the exceptional packet.
-/

open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.HilbertMetric
noncomputable section
variable {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Squared norm of the coherent sum, with every cross term retained. -/
def packetEnergy (s : Finset ι) (v : ι → E) : ℝ := ‖∑ i ∈ s, v i‖ ^ 2

omit [InnerProductSpace ℝ E] in
theorem packetEnergy_nonneg (s : Finset ι) (v : ι → E) : 0 ≤ packetEnergy s v :=
  sq_nonneg _

/-- The energy is the complete real Gram sum. -/
theorem packetEnergy_eq_gram (s : Finset ι) (v : ι → E) :
    packetEnergy s v = ∑ i ∈ s, ∑ j ∈ s, ⟪v i, v j⟫_ℝ := by
  simp only [packetEnergy, ← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
  exact Finset.sum_comm

/-- Polarization gives the exact centered error when subtracting one vector. -/
theorem energy_sub_centered (x y : E) :
    (‖x - y‖ ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) ^ 2 ≤
      4 * ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h := sq_le_sq₀ (abs_nonneg ⟪x, y⟫_ℝ)
    (mul_nonneg (norm_nonneg x) (norm_nonneg y)) |>.mpr (abs_real_inner_le_norm x y)
  rw [sq_abs, mul_pow] at h
  rw [norm_sub_sq_real]
  nlinarith only [h]

/-- Explicit two-sided deletion error, including its quadratic term. -/
theorem energy_sub_error (x y : E) :
    |‖x - y‖ ^ 2 - ‖x‖ ^ 2| ≤ ‖y‖ ^ 2 + 2 * ‖x‖ * ‖y‖ := by
  rw [norm_sub_sq_real]
  have h := abs_real_inner_le_norm x y
  rw [abs_le] at h ⊢
  constructor <;> nlinarith only [h.1, h.2, sq_nonneg ‖y‖]

omit [InnerProductSpace ℝ E] in
private theorem packet_sdiff [DecidableEq ι] (s e : Finset ι) (v : ι → E) :
    (∑ i ∈ s \ e, v i) = (∑ i ∈ s, v i) - ∑ i ∈ s ∩ e, v i := by
  have h := Finset.sum_inter_add_sum_sdiff s e v
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

/-- Centered deletion error is at most twice the geometric mean of the two energies. -/
theorem packetEnergy_deletion_centered [DecidableEq ι] (s e : Finset ι) (v : ι → E) :
    (packetEnergy (s \ e) v - packetEnergy s v - packetEnergy (s ∩ e) v) ^ 2 ≤
      4 * packetEnergy s v * packetEnergy (s ∩ e) v := by
  simpa only [packetEnergy, packet_sdiff] using
    energy_sub_centered (∑ i ∈ s, v i) (∑ i ∈ s ∩ e, v i)

/-- Absolute energy loss under arbitrary finite deletion. -/
theorem packetEnergy_deletion_error [DecidableEq ι] (s e : Finset ι) (v : ι → E) :
    |packetEnergy (s \ e) v - packetEnergy s v| ≤
      packetEnergy (s ∩ e) v +
        2 * Real.sqrt (packetEnergy s v) * Real.sqrt (packetEnergy (s ∩ e) v) := by
  simpa only [packetEnergy, packet_sdiff, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    using energy_sub_error (∑ i ∈ s, v i) (∑ i ∈ s ∩ e, v i)

omit [InnerProductSpace ℝ E] in
/-- A drop in square-root energy forces exceptional energy of at least its square. -/
theorem packetEnergy_deletion_reverse [DecidableEq ι] (s e : Finset ι) (v : ι → E) :
    (Real.sqrt (packetEnergy s v) - Real.sqrt (packetEnergy (s \ e) v)) ^ 2 ≤
      packetEnergy (s ∩ e) v := by
  simp only [packetEnergy, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have h := abs_norm_sub_norm_le (∑ i ∈ s, v i) (∑ i ∈ s \ e, v i)
  rw [packet_sdiff, sub_sub_cancel] at h
  have hh := sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.mpr h
  simpa only [sq_abs, packet_sdiff] using hh

omit [InnerProductSpace ℝ E] in
/-- Coherent energy is bounded by cardinality times the individual energy mass. -/
theorem packetEnergy_le_card_mul (s : Finset ι) (v : ι → E) :
    packetEnergy s v ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖v i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s v) 2).trans h

omit [InnerProductSpace ℝ E] in
/-- Cardinality cost of an observed correlation loss, with no lower-bound premise. -/
theorem packetEnergy_deletion_cardinality [DecidableEq ι] (s e : Finset ι) (v : ι → E) :
    (Real.sqrt (packetEnergy s v) - Real.sqrt (packetEnergy (s \ e) v)) ^ 2 ≤
      ((s ∩ e).card : ℝ) * ∑ i ∈ s ∩ e, ‖v i‖ ^ 2 :=
  (packetEnergy_deletion_reverse s e v).trans (packetEnergy_le_card_mul _ v)

end
end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.packetEnergy_deletion_centered
#print axioms GaloisForLFunctions.HilbertMetric.packetEnergy_deletion_error
#print axioms GaloisForLFunctions.HilbertMetric.packetEnergy_deletion_cardinality
