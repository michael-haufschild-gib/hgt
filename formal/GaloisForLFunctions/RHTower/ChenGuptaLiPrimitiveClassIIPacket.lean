/-
# Chen--Gupta--Li primitive Class-II finite packet

This module canonically enumerates certified Class-II rows, transfers their
individual L-value thresholds to one finite common threshold, and provides the
count-to-fourth-moment inequality without caller-supplied premises.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIILValueThreshold

open Complex

noncomputable section

namespace RHTower

noncomputable def cglPrimitiveClassIWellSpacedClassIIPacketIndex
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card) :
    CGLPrimitiveClassIWellSpacedClassIIRow X Y n χ τ H :=
  (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).equivFin.symm i

noncomputable def cglPrimitiveClassIWellSpacedClassIIPacketRows
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :
    Fin (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card →
      CGLCharacterDyadicRowData (n + 1) :=
  fun i => cglPrimitiveClassIWellSpacedClassIIMaximizerRow X Y n χ τ H
    (cglPrimitiveClassIWellSpacedClassIIPacketIndex X Y n χ τ H i)

noncomputable def cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card) : NNReal :=
  (cglPrimitiveClassIWellSpacedClassIILValueThreshold X Y n χ τ H
    (cglPrimitiveClassIWellSpacedClassIIPacketIndex X Y n χ τ H i)).toNNReal

theorem cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold_positive
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card) :
    0 < cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold X Y n χ τ H i := by
  rw [cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold, Real.toNNReal_pos]
  exact cglPrimitiveClassIWellSpacedClassIILValueThreshold_positive X Y n χ τ H
    (cglPrimitiveClassIWellSpacedClassIIPacketIndex X Y n χ τ H i)

theorem cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold_le_LValue
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card) :
    (cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold X Y n χ τ H i : ℝ) ≤
      ‖cglClassIICriticalLineLValue
        (cglPrimitiveClassIWellSpacedClassIIPacketRows X Y n χ τ H i)‖ := by
  have hnonneg : 0 ≤ cglPrimitiveClassIWellSpacedClassIILValueThreshold X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIIPacketIndex X Y n χ τ H i) := by
    unfold cglPrimitiveClassIWellSpacedClassIILValueThreshold
    apply div_nonneg
    · exact le_of_lt (div_pos (Real.exp_pos _) (by norm_num))
    · apply mul_nonneg
      · apply mul_nonneg
        · exact norm_nonneg _
        · exact norm_nonneg _
      · exact abs_nonneg _
  rw [show (cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold X Y n χ τ H i : ℝ) =
      cglPrimitiveClassIWellSpacedClassIILValueThreshold X Y n χ τ H
        (cglPrimitiveClassIWellSpacedClassIIPacketIndex X Y n χ τ H i) by
      exact Real.coe_toNNReal _ hnonneg]
  have hchar := cglPrimitiveClassIWellSpacedClassIIMaximizerRow_character X Y n χ τ H
    (cglPrimitiveClassIWellSpacedClassIIPacketIndex X Y n χ τ H i)
  simpa [cglPrimitiveClassIWellSpacedClassIIPacketRows, cglClassIICriticalLineLValue, hchar] using
    cglPrimitiveClassIWellSpacedClassII_LValueThreshold_le X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIIPacketIndex X Y n χ τ H i)

noncomputable def cglPrimitiveClassIWellSpacedClassIIPacketThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) : NNReal := by
  classical
  let R := (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card
  exact if hR : R = 0 then 0 else
    Finset.inf' (Finset.univ : Finset (Fin R))
      (by
        apply Finset.nonempty_iff_ne_empty.mpr
        intro hempty
        apply hR
        have hcard : (Finset.univ : Finset (Fin R)).card = 0 := by
          rw [hempty]
          simp
        simpa using hcard)
      (cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold X Y n χ τ H)

/-- Either the finite Class-II packet is empty or its common threshold is
strictly positive. -/
theorem cglPrimitiveClassIWellSpacedClassIIPacketThreshold_positive_or_empty
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :
    0 < (cglPrimitiveClassIWellSpacedClassIIPacketThreshold X Y n χ τ H : ℝ) ∨
      (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card = 0 := by
  classical
  unfold cglPrimitiveClassIWellSpacedClassIIPacketThreshold
  dsimp only
  split_ifs with hR
  · right
    simp [hR]
  · left
    let R := (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card
    have hnonempty : (Finset.univ : Finset (Fin R)).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      apply hR
      have hcard : (Finset.univ : Finset (Fin R)).card = 0 := by
        rw [hempty]
        simp
      simpa [R] using hcard
    have hinf : 0 < Finset.inf' (Finset.univ : Finset (Fin R)) hnonempty
        (cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold X Y n χ τ H) := by
      apply (Finset.lt_inf'_iff hnonempty).mpr
      intro i hi
      exact cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold_positive X Y n χ τ H i
    exact_mod_cast hinf

theorem cglPrimitiveClassIWellSpacedClassIIPacketThreshold_le_rowThreshold
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card) :
    cglPrimitiveClassIWellSpacedClassIIPacketThreshold X Y n χ τ H ≤
      cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold X Y n χ τ H i := by
  classical
  unfold cglPrimitiveClassIWellSpacedClassIIPacketThreshold
  dsimp only
  split_ifs with hR
  · have hcard : (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card = 0 := by
      simp [hR]
    exact Fin.elim0 (by simpa [hcard] using i)
  · exact Finset.inf'_le _ (Finset.mem_univ i)

theorem cglPrimitiveClassIWellSpacedClassIIPacketThreshold_le_LValue
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card) :
    (cglPrimitiveClassIWellSpacedClassIIPacketThreshold X Y n χ τ H : ℝ) ≤
      ‖cglClassIICriticalLineLValue
        (cglPrimitiveClassIWellSpacedClassIIPacketRows X Y n χ τ H i)‖ := by
  calc
    (cglPrimitiveClassIWellSpacedClassIIPacketThreshold X Y n χ τ H : ℝ) ≤
        (cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold X Y n χ τ H i : ℝ) := by
      exact_mod_cast cglPrimitiveClassIWellSpacedClassIIPacketThreshold_le_rowThreshold X Y n χ τ H i
    _ ≤ ‖cglClassIICriticalLineLValue
        (cglPrimitiveClassIWellSpacedClassIIPacketRows X Y n χ τ H i)‖ :=
      cglPrimitiveClassIWellSpacedClassIIPacketRowThreshold_le_LValue X Y n χ τ H i

theorem cglPrimitiveClassIWellSpacedClassIIPacket_card_mul_threshold_fourth_le
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :
    ((cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card : ℝ) *
      (cglPrimitiveClassIWellSpacedClassIIPacketThreshold X Y n χ τ H : ℝ) ^ 4 ≤
      ∑ i : Fin (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card,
        ‖cglClassIICriticalLineLValue
          (cglPrimitiveClassIWellSpacedClassIIPacketRows X Y n χ τ H i)‖ ^ 4 := by
  calc
    ((cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card : ℝ) *
        (cglPrimitiveClassIWellSpacedClassIIPacketThreshold X Y n χ τ H : ℝ) ^ 4 =
        ∑ _i : Fin (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card,
          (cglPrimitiveClassIWellSpacedClassIIPacketThreshold X Y n χ τ H : ℝ) ^ 4 := by
      simp
    _ ≤ ∑ i : Fin (cglPrimitiveClassIWellSpacedClassIIRows X Y n χ τ H).card,
        ‖cglClassIICriticalLineLValue
          (cglPrimitiveClassIWellSpacedClassIIPacketRows X Y n χ τ H i)‖ ^ 4 := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ NNReal.zero_le_coe
        (cglPrimitiveClassIWellSpacedClassIIPacketThreshold_le_LValue X Y n χ τ H i) 4

end RHTower
