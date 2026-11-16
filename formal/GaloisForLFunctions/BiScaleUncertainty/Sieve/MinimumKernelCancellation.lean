import GaloisForLFunctions.BiScaleUncertainty.KerPCenteredSieveAndFirstSecondMomentReciprocity

/-!
# Minimum-kernel cancellation for centered sieve weights

The minimum-kernel cancellation in the proof of Proposition 7 of
Gonçalves–Kerr–Klurman–Vedana removes a common logarithmic scale.
For the corpus's endpoint-centered sieve weights, centering is automatic:
the pairing equals a negative maximum-kernel pairing at every real scale.
-/

namespace GaloisForLFunctions.BiScaleUncertainty

open Finset

/-- Harmonic coordinates of the endpoint-centered sieve weight at a positive cutoff. -/
noncomputable def centeredHarmonicWeight (N : ℕ) (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  kerPEndpointWeight (N + 1) c i / (i : ℝ)

theorem sum_centeredHarmonicWeight (N : ℕ) (c : ℕ → ℝ) :
    ∑ i ∈ Icc 1 (N + 1), centeredHarmonicWeight N c i = 0 :=
  finiteHarmonicSum_kerPEndpointWeight_eq_zero (by omega) c

/-- The logarithmic minimum kernel paired against two centered sieve rows. -/
noncomputable def centeredMinimumPairing (N : ℕ) (c d : ℕ → ℝ) (L : ℝ) : ℝ :=
  ∑ i ∈ Icc 1 (N + 1), ∑ j ∈ Icc 1 (N + 1),
    centeredHarmonicWeight N c i * centeredHarmonicWeight N d j *
      min (L - Real.log i) (L - Real.log j)

/-- The common logarithmic scale cancels exactly, leaving a maximum kernel. -/
theorem centeredMinimumPairing_eq_neg_max (N : ℕ) (c d : ℕ → ℝ) (L : ℝ) :
    centeredMinimumPairing N c d L =
      -(∑ i ∈ Icc 1 (N + 1), ∑ j ∈ Icc 1 (N + 1),
        centeredHarmonicWeight N c i * centeredHarmonicWeight N d j *
          max (Real.log i) (Real.log j)) := by
  have hmin (x y : ℝ) : min (L - x) (L - y) = L - max x y := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, min_eq_right (by linarith)]
    · rw [max_eq_left h, min_eq_left (by linarith)]
  have hconstant : (∑ i ∈ Icc 1 (N + 1), ∑ j ∈ Icc 1 (N + 1),
      centeredHarmonicWeight N c i * centeredHarmonicWeight N d j * L) = 0 := by
    simp_rw [mul_assoc, ← mul_sum, ← sum_mul, sum_centeredHarmonicWeight,
      zero_mul]
  unfold centeredMinimumPairing
  simp_rw [hmin, mul_sub, sum_sub_distrib]
  rw [hconstant, zero_sub]

/-- Centered sieve pairing is invariant under every common translation of the log scale. -/
theorem centeredMinimumPairing_scale_invariant (N : ℕ) (c d : ℕ → ℝ) (L M : ℝ) :
    centeredMinimumPairing N c d L = centeredMinimumPairing N c d M := by
  rw [centeredMinimumPairing_eq_neg_max, centeredMinimumPairing_eq_neg_max]

/-- The cancellation bounds the pairing by the log width, independently of its base scale. -/
theorem abs_centeredMinimumPairing_le (N : ℕ) (c d : ℕ → ℝ) (L : ℝ) :
    |centeredMinimumPairing N c d L| ≤
      (∑ i ∈ Icc 1 (N + 1), |centeredHarmonicWeight N c i|) *
      (∑ j ∈ Icc 1 (N + 1), |centeredHarmonicWeight N d j|) * Real.log (N + 1) := by
  have hlog (i : ℕ) (hi : i ∈ Icc 1 (N + 1)) :
      0 ≤ Real.log i ∧ Real.log i ≤ Real.log (N + 1) := by
    obtain ⟨hi1, hiN⟩ := mem_Icc.mp hi
    constructor
    · exact Real.log_nonneg (by exact_mod_cast hi1)
    · apply Real.log_le_log (by exact_mod_cast (show 0 < i by omega))
      exact_mod_cast hiN
  rw [centeredMinimumPairing_eq_neg_max, abs_neg]
  calc
    _ ≤ ∑ i ∈ Icc 1 (N + 1), ∑ j ∈ Icc 1 (N + 1),
        |centeredHarmonicWeight N c i| * |centeredHarmonicWeight N d j| *
          Real.log (N + 1) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
      rw [abs_mul, abs_mul,
        abs_of_nonneg ((hlog i hi).1.trans (le_max_left _ _))]
      exact mul_le_mul_of_nonneg_left (max_le (hlog i hi).2 (hlog j hj).2)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp_rw [mul_assoc, ← mul_sum, ← sum_mul]

#print axioms centeredMinimumPairing_eq_neg_max
#print axioms centeredMinimumPairing_scale_invariant
#print axioms abs_centeredMinimumPairing_le

end GaloisForLFunctions.BiScaleUncertainty
