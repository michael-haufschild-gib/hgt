import Mathlib

/-!
# Coherent history mechanics

This module certifies the finite algebraic core of coherent-history mechanics:

* total phase extraction and anchored phase-Gram reconstruction;
* the exact two-history phase-dispersion budget;
* the entrywise modulus as the least positive matrix majorant;
* positivity and the associativity/Bianchi identity of the interference defect;
* a closed rational period-two coherent process with an exponentially expanding
  positive history envelope.

The results are route-independent and contain no RH premise.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

section PolarReconstruction

/-- Total phase convention: zero receives the neutral phase. -/
noncomputable def coherentUnitPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else (‖z‖ : ℂ)⁻¹ * z

/-- Modulus and the total phase reconstruct every complex history weight. -/
theorem norm_mul_coherentUnitPhase (z : ℂ) :
    (‖z‖ : ℂ) * coherentUnitPhase z = z := by
  by_cases hz : z = 0
  · simp [coherentUnitPhase, hz]
  · rw [coherentUnitPhase, if_neg hz]
    have hn : (‖z‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hz)
    field_simp

/-- Rank-one phase-Gram coordinate of two marked histories. -/
noncomputable def coherentPhaseGram (z w : ℂ) : ℂ :=
  coherentUnitPhase z * star (coherentUnitPhase w)

/-- Positive weight and the anchored phase Gram reconstruct the original history packet up to the
single common phase of the anchor. -/
theorem coherentPhaseGram_anchor_reconstruct (z w : ℂ) :
    (‖z‖ : ℂ) * coherentPhaseGram z w =
      z * star (coherentUnitPhase w) := by
  rw [coherentPhaseGram, ← mul_assoc, norm_mul_coherentUnitPhase]

/-- Exact two-history conservation: variation mass squared is coherent mass squared plus the
phase-dispersion defect. -/
theorem twoHistory_phaseDispersion_identity (z w : ℂ) :
    (‖z‖ + ‖w‖) ^ 2 = ‖z + w‖ ^ 2 +
      2 * (‖z‖ * ‖w‖ - (z * (starRingEnd ℂ) w).re) := by
  rw [Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm z, ← Complex.sq_norm w]
  ring

/-- The two-history phase-dispersion defect is nonnegative. -/
theorem twoHistory_phaseDispersion_nonneg (z w : ℂ) :
    0 ≤ ‖z‖ * ‖w‖ - (z * (starRingEnd ℂ) w).re := by
  have h := Complex.re_le_norm (z * (starRingEnd ℂ) w)
  rw [norm_mul, Complex.norm_conj] at h
  linarith

end PolarReconstruction

section PositiveMajorant

/-- Entrywise positive envelope of a complex matrix. -/
noncomputable def coherentEntrywiseNorm {m n : Type*} (A : Matrix m n ℂ) :
    Matrix m n ℝ :=
  fun i j => ‖A i j‖

/-- A positive matrix majorizes the absolute output of a coherent matrix on every input. -/
def IsCoherentPositiveMajorant {x y : Type*} [Fintype x]
    (A : Matrix y x ℂ) (P : Matrix y x ℝ) : Prop :=
  ∀ (u : x → ℂ) (i : y), ‖A.mulVec u i‖ ≤ ∑ j, P i j * ‖u j‖

/-- The entrywise norm always supplies a positive majorant. -/
theorem coherentEntrywiseNorm_isPositiveMajorant {x y : Type*} [Fintype x]
    (A : Matrix y x ℂ) : IsCoherentPositiveMajorant A (coherentEntrywiseNorm A) := by
  intro u i
  calc
    ‖A.mulVec u i‖ = ‖∑ j, A i j * u j‖ := rfl
    _ ≤ ∑ j, ‖A i j * u j‖ := norm_sum_le _ _
    _ = ∑ j, coherentEntrywiseNorm A i j * ‖u j‖ := by
      simp only [coherentEntrywiseNorm, norm_mul]

/-- Every positive majorant dominates the entrywise norm, so the latter is the unique least one. -/
theorem coherentEntrywiseNorm_le_of_positiveMajorant {x y : Type*} [Fintype x]
    [DecidableEq x] (A : Matrix y x ℂ) (P : Matrix y x ℝ)
    (hP : IsCoherentPositiveMajorant A P) (i : y) (j : x) :
    coherentEntrywiseNorm A i j ≤ P i j := by
  classical
  have h := hP (fun k => if k = j then 1 else 0) i
  have hsum :
      (∑ k : x, P i k * ‖(if k = j then (1 : ℂ) else 0)‖) = P i j := by
    rw [Fintype.sum_eq_single j]
    · simp
    · intro k hk
      rw [if_neg hk]
      simp
  rw [hsum] at h
  simpa [Matrix.mulVec, dotProduct, coherentEntrywiseNorm] using h

end PositiveMajorant

section CompositionDefect

/-- Positive history mass lost when a two-stage coherent process is collapsed before taking its
entrywise modulus. -/
noncomputable def coherentInterferenceDefect {x y z : Type*} [Fintype y]
    (B : Matrix z y ℂ) (A : Matrix y x ℂ) : Matrix z x ℝ :=
  coherentEntrywiseNorm B * coherentEntrywiseNorm A - coherentEntrywiseNorm (B * A)

/-- The interference defect is entrywise nonnegative. -/
theorem coherentInterferenceDefect_nonneg {x y z : Type*} [Fintype y]
    (B : Matrix z y ℂ) (A : Matrix y x ℂ) (i : z) (j : x) :
    0 ≤ coherentInterferenceDefect B A i j := by
  rw [show coherentInterferenceDefect B A i j =
      (∑ k, ‖B i k‖ * ‖A k j‖) - ‖∑ k, B i k * A k j‖ by
    simp [coherentInterferenceDefect, coherentEntrywiseNorm, Matrix.mul_apply]]
  rw [sub_nonneg]
  calc
    ‖∑ k, B i k * A k j‖ ≤ ∑ k, ‖B i k * A k j‖ := norm_sum_le _ _
    _ = ∑ k, ‖B i k‖ * ‖A k j‖ := by simp only [norm_mul]

/-- Exact associativity conservation. Parenthesization changes where interference memory is
registered, but not its total transported positive budget. -/
theorem coherentInterferenceDefect_associativity {x y z w : Type*}
    [Fintype y] [Fintype z]
    (A : Matrix y x ℂ) (B : Matrix z y ℂ) (C : Matrix w z ℂ) :
    coherentEntrywiseNorm C * coherentInterferenceDefect B A +
        coherentInterferenceDefect C (B * A) =
      coherentInterferenceDefect C B * coherentEntrywiseNorm A +
        coherentInterferenceDefect (C * B) A := by
  unfold coherentInterferenceDefect
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  abel

end CompositionDefect

section RecurrentOpenEnvelope

abbrev CoherentTwoMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- Closed rational coherent witness. -/
noncomputable def coherentRecurrenceWitness : CoherentTwoMatrix :=
  !![(3 : ℝ) / 5, 2 / 5; 8 / 5, -3 / 5]

/-- Its source-marked positive one-step history envelope. -/
noncomputable def coherentEnvelopeWitness : CoherentTwoMatrix :=
  !![(3 : ℝ) / 5, 2 / 5; 8 / 5, 3 / 5]

/-- Exact expanding positive-history ray. -/
noncomputable def coherentExpandingRay : Fin 2 → ℝ := ![1, 2]

/-- The coherent process has exact period two. -/
theorem coherentRecurrenceWitness_sq :
    coherentRecurrenceWitness * coherentRecurrenceWitness = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coherentRecurrenceWitness, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The positive envelope expands one marked ray by the exact factor `7/5`. -/
theorem coherentEnvelopeWitness_mulVec :
    coherentEnvelopeWitness.mulVec coherentExpandingRay =
      (7 / 5 : ℝ) • coherentExpandingRay := by
  funext i
  fin_cases i <;>
    norm_num [coherentEnvelopeWitness, coherentExpandingRay, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- Exact envelope growth at every history depth. -/
theorem coherentEnvelopeWitness_pow_mulVec (n : ℕ) :
    (coherentEnvelopeWitness ^ n).mulVec coherentExpandingRay =
      ((7 / 5 : ℝ) ^ n) • coherentExpandingRay := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, coherentEnvelopeWitness_mulVec,
        Matrix.mulVec_smul, ih]
      simp only [pow_succ, smul_smul]
      congr 1
      ring

/-- The first coordinate records the exact exponential history growth. -/
theorem coherentExpandingRay_coordinate (n : ℕ) :
    ((coherentEnvelopeWitness ^ n).mulVec coherentExpandingRay) 0 =
      (7 / 5 : ℝ) ^ n := by
  rw [coherentEnvelopeWitness_pow_mulVec]
  simp [coherentExpandingRay]

/-- The marked positive history is open although the coherent response is period two. -/
theorem coherentExpandingRay_tendsto :
    Filter.Tendsto
      (fun n => ((coherentEnvelopeWitness ^ n).mulVec coherentExpandingRay) 0)
      Filter.atTop Filter.atTop := by
  simpa [coherentExpandingRay_coordinate] using
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 7 / 5 by norm_num))

/-- Unconditional fusion capstone: exact coherent recurrence and exact open positive history occur
in one closed finite process. -/
theorem coherentHistoryMechanics_closed_capstone :
    coherentRecurrenceWitness * coherentRecurrenceWitness = 1 ∧
      coherentEnvelopeWitness.mulVec coherentExpandingRay =
        (7 / 5 : ℝ) • coherentExpandingRay ∧
      Filter.Tendsto
        (fun n => ((coherentEnvelopeWitness ^ n).mulVec coherentExpandingRay) 0)
        Filter.atTop Filter.atTop := by
  exact ⟨coherentRecurrenceWitness_sq, coherentEnvelopeWitness_mulVec,
    coherentExpandingRay_tendsto⟩

end RecurrentOpenEnvelope

end GaloisForLFunctions.HTGeometry
