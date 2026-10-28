import Zeta23.ZeroSide

/-!
# Coalescence on arbitrary real evaluation families

A fixed reflection label with multiplicity two and two swapped labels carrying the same real
vector contribute the same matrix `2 v vᵀ`. This identity preserves the full block matrix and
total multiplicity for arbitrary real families, while changing the fixed-label multiplicity.
Neither orthogonality nor unit normalization is required.

An explicit normalized example has distinct fixed-label vectors with inner product `3/5`.
Its trace and Frobenius moment retain their correlations. The constructions concern abstract
`ZeroBlockData`; no realization by a prescribed arithmetic evaluation family is asserted.
-/

open Complex Finset Matrix
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

variable {α β d : Type*}

/-- Fixed reflection labels with multiplicities one and two on arbitrary real vectors. -/
def doubleZeroFrameData (u : α → d → ℝ) (w : β → d → ℝ) :
    Zeta23.ZeroSide.ZeroBlockData (α ⊕ β) d where
  m := Sum.elim (fun _ => 1) (fun _ => 2)
  one_le_m z := by rcases z with _ | _ <;> simp
  v := Sum.elim (fun a k => (u a k : ℂ)) (fun b k => (w b k : ℂ))
  σ := id
  σ_invol _ := rfl
  m_σ _ := rfl
  v_σ z := by rcases z with a | b <;> ext k <;> simp

/-- Simple fixed labels and swapped pairs sharing arbitrary real vectors.
The labels encode an abstract involution, without an arithmetic realization condition. -/
def coalescedPairFrameData (u : α → d → ℝ) (w : β → d → ℝ) :
    Zeta23.ZeroSide.ZeroBlockData (α ⊕ (β ⊕ β)) d where
  m _ := 1
  one_le_m _ := le_rfl
  v := Sum.elim (fun a k => (u a k : ℂ))
    (Sum.elim (fun b k => (w b k : ℂ)) (fun b k => (w b k : ℂ)))
  σ := Sum.map id (Equiv.sumComm β β)
  σ_invol z := by rcases z with a | (b | b) <;> rfl
  m_σ _ := rfl
  v_σ z := by rcases z with a | (b | b) <;> ext k <;> simp

open Zeta23.ZeroSide

/-- Splitting a double fixed label into two reflected labels with the same real vector
preserves the full block matrix, including every cross-correlation between vectors. -/
theorem blockA_coalescedPairFrame_eq_doubleZeroFrame
    [Fintype α] [Fintype β]
    (u : α → d → ℝ) (w : β → d → ℝ) :
    (coalescedPairFrameData u w).blockA = (doubleZeroFrameData u w).blockA := by
  simp only [ZeroBlockData.blockA, coalescedPairFrameData, doubleZeroFrameData,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Nat.cast_one, Nat.cast_ofNat, one_smul]
  rw [← Finset.smul_sum, two_smul ℂ]

/-- Total and fixed-label multiplicity counts for arbitrary real double-zero frames. -/
theorem counts_doubleZeroFrameData
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (u : α → d → ℝ) (w : β → d → ℝ) :
    (doubleZeroFrameData u w).Ncount = Fintype.card α + 2 * Fintype.card β ∧
      (doubleZeroFrameData u w).Non = Fintype.card α + 2 * Fintype.card β := by
  have hon : (doubleZeroFrameData u w).onLine = Finset.univ := by
    ext z
    simp [ZeroBlockData.onLine, doubleZeroFrameData]
  constructor
  · simp [ZeroBlockData.Ncount, doubleZeroFrameData, Fintype.sum_sum_type, Nat.mul_comm]
  · unfold ZeroBlockData.Non
    rw [hon]
    simp [doubleZeroFrameData, Fintype.sum_sum_type, Nat.mul_comm]

/-- Splitting double fixed labels preserves total multiplicity but removes their fixed-label mass. -/
theorem counts_coalescedPairFrameData
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (u : α → d → ℝ) (w : β → d → ℝ) :
    (coalescedPairFrameData u w).Ncount = Fintype.card α + 2 * Fintype.card β ∧
      (coalescedPairFrameData u w).Non = Fintype.card α := by
  have hon : (coalescedPairFrameData u w).onLine =
      Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext z
    simp only [ZeroBlockData.onLine, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map, Function.Embedding.coeFn_mk, coalescedPairFrameData]
    rcases z with a | (b | b) <;> simp
  constructor
  · simp [ZeroBlockData.Ncount, coalescedPairFrameData, two_mul]
  · unfold ZeroBlockData.Non
    rw [hon, Finset.sum_map]
    simp [coalescedPairFrameData]

/-- Two distinct unit vectors with inner product `3/5`. -/
def correlatedSimpleFrame : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![3 / 5, 4 / 5]]

/-- The unit vector assigned to both members of a reflected pair. -/
def correlatedPairFrame (_ : Unit) : Fin 2 → ℝ := ![0, 1]

/-- The common Gram matrix of a nonorthogonal pair of real frames. -/
theorem blockA_correlatedPairFrame :
    (coalescedPairFrameData correlatedSimpleFrame correlatedPairFrame).blockA =
      !![(34 / 25 : ℂ), 12 / 25; 12 / 25, 66 / 25] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ZeroBlockData.blockA_apply, coalescedPairFrameData,
      correlatedSimpleFrame, correlatedPairFrame, Fintype.sum_sum_type, Fin.sum_univ_two]

/-- Normalized, nonorthogonal vectors preserve coalescence indistinguishability.
Their cross-correlations remain in the Frobenius moment `232/25`. -/
theorem nonorthogonal_coalescence_example :
    let D := coalescedPairFrameData correlatedSimpleFrame correlatedPairFrame
    let E := doubleZeroFrameData correlatedSimpleFrame correlatedPairFrame
    (∀ z, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) = 1) ∧
      (∑ k, star (D.v (Sum.inl 0) k) * D.v (Sum.inl 1) k) = (3 / 5 : ℂ) ∧
      D.blockA = E.blockA ∧ D.Ncount = 4 ∧ E.Non = 4 ∧ D.Non = 2 ∧
      RHLinalg.rtrace D.blockA = 4 ∧ RHLinalg.frobSq D.blockA = 232 / 25 := by
  dsimp only
  refine ⟨?_, ?_, blockA_coalescedPairFrame_eq_doubleZeroFrame _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rcases z with a | (b | b)
    · fin_cases a <;> norm_num [coalescedPairFrameData, correlatedSimpleFrame,
        Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs]
    · norm_num [coalescedPairFrameData, correlatedPairFrame, Fin.sum_univ_two]
    · norm_num [coalescedPairFrameData, correlatedPairFrame, Fin.sum_univ_two]
  · norm_num [coalescedPairFrameData, correlatedSimpleFrame, Fin.sum_univ_two]
  · simpa using (counts_coalescedPairFrameData correlatedSimpleFrame correlatedPairFrame).1
  · simpa using (counts_doubleZeroFrameData correlatedSimpleFrame correlatedPairFrame).2
  · simpa using (counts_coalescedPairFrameData correlatedSimpleFrame correlatedPairFrame).2
  · rw [blockA_correlatedPairFrame]
    norm_num [RHLinalg.rtrace, Matrix.trace, Fin.sum_univ_two]
  · rw [blockA_correlatedPairFrame]
    norm_num [RHLinalg.frobSq, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, map_ofNat]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
