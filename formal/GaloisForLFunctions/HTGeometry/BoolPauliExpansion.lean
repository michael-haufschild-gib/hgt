/-
# Single-qubit Hermitian expansion and the bilinear leaf coupling

Every Hermitian `2 × 2` matrix is a real combination of the identity and the three Paulis, and the
leaf coupling is bilinear.  So coupling a weight-`≤1` operator to an arbitrary Hermitian single-qubit
factor stays inside the weight-`≤2` Pauli span: the identity part of the factor keeps the weight, and
each Pauli part raises it by one.  A traceless real field on the new qubit is exactly a multiple of
`Z`.

Main results:
* `exists_real_boolPauli_expansion` — **the single-qubit Hermitian expansion**.
* `coupleSnoc_add_right`, `coupleSnoc_smul_right` — bilinearity of the leaf coupling.
* `couple_hermitian_mem_pauliSpan` — **the leaf coupling stays in the weight-two span**.
* `diagonal_boolShift_eq` — the traceless field is a multiple of `Z`.
-/
import GaloisForLFunctions.HTGeometry.PauliBoundedWeightSpan
import GaloisForLFunctions.HTGeometry.ChartQuadraticRateEscape
import GaloisForLFunctions.HTGeometry.TwoQubitSeedPauliTransport

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem finitePauliMatrix_fin_one (P : Fin 1 → Option (Fin 3)) :
    finitePauliMatrix P
      = Matrix.reindex oneQubitConfigEquiv oneQubitConfigEquiv (boolPauliOption (P 0)) := by
  ext x y
  simp only [finitePauliMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    boolPauliOptionEntry]
  rw [Fin.prod_univ_one]
  rfl

theorem reindex_symm_reindex_bool (X : Matrix Bool Bool ℂ) :
    Matrix.reindex oneQubitConfigEquiv.symm oneQubitConfigEquiv.symm
        (Matrix.reindex oneQubitConfigEquiv oneQubitConfigEquiv X) = X := by
  ext x y
  rfl

/-- **Every Hermitian single-qubit matrix is a real combination of the identity and the three
Paulis.** -/
theorem exists_real_boolPauli_expansion {B : Matrix Bool Bool ℂ} (hB : B.IsHermitian) :
    ∃ c : Option (Fin 3) → ℝ, B = ∑ p : Option (Fin 3), (c p : ℂ) • boolPauliOption p := by
  classical
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (FiniteQubitConfiguration (Fin 1))
      (FiniteQubitConfiguration (Fin 1)) ℂ,
      B' = Matrix.reindex oneQubitConfigEquiv oneQubitConfigEquiv B := ⟨_, rfl⟩
  have hB'herm : B'.IsHermitian := by
    rw [hB']
    exact hB.submatrix _
  obtain ⟨Bsa, hBsa⟩ : ∃ Bsa : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin 1))
      (FiniteQubitConfiguration (Fin 1)) ℂ), (Bsa : Matrix _ _ ℂ) = B' := ⟨⟨B', hB'herm⟩, rfl⟩
  have hexp := (finitePauliSelfAdjointBasis (Fin 1)).sum_repr Bsa
  have hcoe : B' = ∑ P : Fin 1 → Option (Fin 3),
      (((finitePauliSelfAdjointBasis (Fin 1)).repr Bsa P : ℝ) : ℂ) • finitePauliMatrix P := by
    rw [← hBsa]
    conv_lhs => rw [← hexp]
    push_cast
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [finitePauliSelfAdjointBasis_apply]
    rfl
  refine ⟨fun p => (finitePauliSelfAdjointBasis (Fin 1)).repr Bsa (fun _ => p), ?_⟩
  have hback : B = Matrix.reindex oneQubitConfigEquiv.symm oneQubitConfigEquiv.symm B' := by
    rw [hB', reindex_symm_reindex_bool]
  rw [hback, hcoe]
  have hpush : Matrix.reindex oneQubitConfigEquiv.symm oneQubitConfigEquiv.symm
      (∑ P : Fin 1 → Option (Fin 3),
        (((finitePauliSelfAdjointBasis (Fin 1)).repr Bsa P : ℝ) : ℂ) • finitePauliMatrix P)
      = ∑ P : Fin 1 → Option (Fin 3),
        (((finitePauliSelfAdjointBasis (Fin 1)).repr Bsa P : ℝ) : ℂ) •
          boolPauliOption (P 0) := by
    ext x y
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [finitePauliMatrix_fin_one P]
    rfl
  rw [hpush]
  exact (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Option (Fin 3))).symm
    (fun P : Fin 1 → Option (Fin 3) =>
      (((finitePauliSelfAdjointBasis (Fin 1)).repr Bsa P : ℝ) : ℂ) •
        boolPauliOption (P 0))).symm

theorem coupleSnoc_add_right (n : ℕ) (B B' : Matrix Bool Bool ℂ)
    (A : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ) :
    coupleSnoc n (B + B') A = coupleSnoc n B A + coupleSnoc n B' A := by
  ext x y
  simp [mul_add]

theorem coupleSnoc_smul_right (n : ℕ) (c : ℂ) (B : Matrix Bool Bool ℂ)
    (A : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ) :
    coupleSnoc n (c • B) A = c • coupleSnoc n B A := by
  ext x y
  simp [mul_comm, mul_assoc]

/-- **The leaf coupling of a weight-`≤1` operator with a Hermitian single-qubit factor stays in the
weight-`≤2` Pauli span.** -/
theorem couple_hermitian_mem_pauliSpan {n : ℕ}
    {A : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hA : A ∈ pauliSpan n 1) {B : Matrix Bool Bool ℂ} (hB : B.IsHermitian) :
    coupleSnoc n B A ∈ pauliSpan (n + 1) 2 := by
  classical
  obtain ⟨c, hBexp⟩ := exists_real_boolPauli_expansion hB
  have hsum : coupleSnoc n B A
      = ∑ p : Option (Fin 3), (c p : ℂ) • coupleSnoc n (boolPauliOption p) A := by
    rw [hBexp]
    ext x y
    simp only [coupleSnoc_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      layerMatrixCoupling, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  refine Submodule.sum_mem _ fun p _ => ?_
  refine Submodule.smul_mem _ _ ?_
  cases p with
  | none => exact pauliSpan_mono (by norm_num) (couple_one_mem_pauliSpan hA)
  | some j => exact couple_mem_pauliSpan_succ hA j

/-- The traceless field on the new qubit is a multiple of `Z`. -/
theorem diagonal_boolShift_eq (z : ℂ) :
    Matrix.diagonal (boolShift z) = (z / 2) • boolPauliOption (some 2) := by
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.diagonal, boolShift, boolPauliOption, finiteQubitPauli]

end GaloisForLFunctions.HTGeometry

end
