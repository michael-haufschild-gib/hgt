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

/-! ## Interventional energy conservation -/

/-- **Exact interventional energy conservation.**  Positive intervention energy splits exactly into
the coherent phase-weighted response energy and the unresolved within-fibre history variance. -/
theorem coherentHistory_energy_decomposition {H Y : Type*} [Fintype H] [Fintype Y]
    [DecidableEq Y] (π : H → Y) (m : H → ℝ) (z : H → ℂ) (s : Y → ℂ)
    (hs : ∀ y : Y, (∑ h ∈ Finset.univ with π h = y, (m h : ℂ) * z h)
        = ((∑ h ∈ Finset.univ with π h = y, m h : ℝ) : ℂ) * s y) :
    ∑ h, m h * Complex.normSq (z h)
      = (∑ y, (∑ h ∈ Finset.univ with π h = y, m h) * Complex.normSq (s y))
        + ∑ h, m h * Complex.normSq (z h - s (π h)) := by
  classical
  have hfib : ∀ f : H → ℝ, ∑ h, f h = ∑ y, ∑ h ∈ Finset.univ with π h = y, f h :=
    fun f => (Finset.sum_fiberwise Finset.univ π f).symm
  rw [hfib (fun h => m h * Complex.normSq (z h)),
    hfib (fun h => m h * Complex.normSq (z h - s (π h))), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  set F : Finset H := Finset.univ.filter fun h => π h = y with hF
  have hmem : ∀ h ∈ F, π h = y := by
    intro h hh
    exact (Finset.mem_filter.mp hh).2
  set v : ℝ := ∑ h ∈ F, m h with hv
  have hexpand : ∑ h ∈ F, m h * Complex.normSq (z h - s (π h))
      = (∑ h ∈ F, m h * Complex.normSq (z h))
        + v * Complex.normSq (s y)
        - 2 * ((∑ h ∈ F, (m h : ℂ) * z h) * (starRingEnd ℂ) (s y)).re := by
    have hpt : ∀ h ∈ F, m h * Complex.normSq (z h - s (π h))
        = m h * Complex.normSq (z h) + m h * Complex.normSq (s y)
          - 2 * (((m h : ℂ) * z h) * (starRingEnd ℂ) (s y)).re := by
      intro h hh
      rw [hmem h hh]
      simp [Complex.normSq_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
        Complex.mul_im]
      ring
    rw [Finset.sum_congr rfl hpt]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 1
    · congr 1
      rw [← Finset.sum_mul, ← hv]
    · rw [← Finset.mul_sum]
      congr 1
      rw [show ((∑ h ∈ F, (m h : ℂ) * z h) * (starRingEnd ℂ) (s y))
          = ∑ h ∈ F, ((m h : ℂ) * z h * (starRingEnd ℂ) (s y)) from Finset.sum_mul _ _ _]
      exact (map_sum Complex.reAddGroupHom
        (fun h => (m h : ℂ) * z h * (starRingEnd ℂ) (s y)) F).symm
  have hmean : ((∑ h ∈ F, (m h : ℂ) * z h) * (starRingEnd ℂ) (s y)).re
      = v * Complex.normSq (s y) := by
    rw [hs y]
    simp [hv, hF, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [hexpand, hmean]
  ring

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

/-- The positive envelope has nonnegative entries, so it is monotone on vectors. -/
theorem coherentEnvelopeWitness_mulVec_mono {u v : Fin 2 → ℝ} (huv : ∀ i, u i ≤ v i) (i : Fin 2) :
    coherentEnvelopeWitness.mulVec u i ≤ coherentEnvelopeWitness.mulVec v i := by
  fin_cases i <;>
    · simp only [Matrix.mulVec, dotProduct, coherentEnvelopeWitness, Fin.sum_univ_succ]
      norm_num
      nlinarith [huv 0, huv 1]

/-- Iterating a subinvariant vector keeps it subinvariant. -/
theorem coherentEnvelopeWitness_pow_mulVec_le {u : Fin 2 → ℝ}
    (hMu : ∀ i, coherentEnvelopeWitness.mulVec u i ≤ u i) (n : ℕ) :
    ∀ i, (coherentEnvelopeWitness ^ n).mulVec u i ≤ u i := by
  induction n with
  | zero => intro i; simp
  | succ n ih =>
      intro i
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      calc coherentEnvelopeWitness.mulVec ((coherentEnvelopeWitness ^ n).mulVec u) i
          ≤ coherentEnvelopeWitness.mulVec u i :=
            coherentEnvelopeWitness_mulVec_mono ih i
        _ ≤ u i := hMu i

/-- **Positive-carrier obstruction.**  No positive vector comparable with the expanding ray is
subinvariant for the coherent history envelope. -/
theorem coherentEnvelope_no_invariant_positive_carrier
    (u : Fin 2 → ℝ) (c C : ℝ) (hc : 0 < c)
    (hcq : ∀ i, c * coherentExpandingRay i ≤ u i)
    (huC : ∀ i, u i ≤ C * coherentExpandingRay i)
    (hMu : ∀ i, coherentEnvelopeWitness.mulVec u i ≤ u i) : False := by
  have hstep : ∀ (m : ℕ) (i : Fin 2),
      (coherentEnvelopeWitness ^ m).mulVec (fun j => c * coherentExpandingRay j) i
        ≤ (coherentEnvelopeWitness ^ m).mulVec u i := by
    intro m
    induction m with
    | zero => intro i; simpa using hcq i
    | succ m ih =>
        intro i
        rw [pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        exact coherentEnvelopeWitness_mulVec_mono ih i
  have hlin : ∀ n : ℕ,
      (coherentEnvelopeWitness ^ n).mulVec (fun j => c * coherentExpandingRay j) 0
        = c * (7 / 5 : ℝ) ^ n := by
    intro n
    have hc' : (fun j => c * coherentExpandingRay j) = c • coherentExpandingRay := by
      funext j
      simp [Pi.smul_apply, smul_eq_mul]
    rw [hc', Matrix.mulVec_smul, coherentEnvelopeWitness_pow_mulVec]
    simp [coherentExpandingRay, Pi.smul_apply, smul_eq_mul]
  have hgrow : ∀ n : ℕ, c * (7 / 5 : ℝ) ^ n ≤ C := by
    intro n
    have hlow := hstep n 0
    rw [hlin n] at hlow
    have hup : (coherentEnvelopeWitness ^ n).mulVec u 0 ≤ C * coherentExpandingRay 0 :=
      le_trans (coherentEnvelopeWitness_pow_mulVec_le hMu n 0) (huC 0)
    have h2 : coherentExpandingRay 0 = 1 := by simp [coherentExpandingRay]
    rw [h2, mul_one] at hup
    linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / c) (show (1 : ℝ) < 7 / 5 by norm_num)
  have hgn := hgrow n
  rw [div_lt_iff₀ hc] at hn
  linarith

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
