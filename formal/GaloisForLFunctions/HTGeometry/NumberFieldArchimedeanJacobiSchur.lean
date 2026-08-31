import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanGreedyFlag
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanSiegelData

/-!
# Jacobi coordinates under first Schur descent

First Schur descent removes exactly the first upper-unipotent row and first positive diagonal
weight.  The construction is simultaneous at real and complex infinite places.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder Matrix NumberField

noncomputable section

variable {n : ℕ}

/-- Tail Jacobi data obtained by deleting the first coordinate. -/
def JacobiData.firstTail (J : JacobiData (n + 1)) : JacobiData n where
  U := matrixFirstTail J.U
  d := fun i => J.d i.succ
  pos := fun i => J.pos i.succ
  upper := fun i j hij => J.upper i.succ j.succ (by simpa using hij)
  unit := fun i => J.unit i.succ

/-- Real Jacobi form commutes exactly with first Schur descent. -/
theorem JacobiData.firstTail_form (J : JacobiData (n + 1)) :
    J.firstTail.form = matrixFirstSchur J.form := by
  ext i j
  simp [JacobiData.firstTail, JacobiData.form, matrixFirstSchur,
    matrixFirstHead, matrixFirstCross, matrixFirstTail, Matrix.mul_apply,
    Matrix.diagonal_apply, Fin.sum_univ_succ, J.unit, J.upper,
    ne_of_gt (J.pos (0 : Fin (n + 1)))]
  ring

/-- Tail Hermitian Jacobi data obtained by deleting the first coordinate. -/
def ComplexJacobiData.firstTail (J : ComplexJacobiData (n + 1)) :
    ComplexJacobiData n where
  U := matrixFirstTail J.U
  d := fun i => J.d i.succ
  pos := fun i => J.pos i.succ
  upper := fun i j hij => J.upper i.succ j.succ (by simpa using hij)
  unit := fun i => J.unit i.succ

/-- Hermitian Jacobi form commutes exactly with first Schur descent. -/
theorem ComplexJacobiData.firstTail_form (J : ComplexJacobiData (n + 1)) :
    J.firstTail.form = matrixFirstSchur J.form := by
  ext i j
  simp [ComplexJacobiData.firstTail, ComplexJacobiData.form, matrixFirstSchur,
    matrixFirstHead, matrixFirstCross, matrixFirstTail, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, Fin.sum_univ_succ, J.unit, J.upper,
    ne_of_gt (J.pos (0 : Fin (n + 1)))]
  ring

variable {K : Type*} [Field K] [NumberField K]

/-- Simultaneous Jacobi data descend through the first real/Hermitian Schur complement. -/
def NumberFieldArchimedeanJacobiData.firstTail
    {A : numberFieldArchimedeanPositiveForms K (n + 1)}
    (J : NumberFieldArchimedeanJacobiData A) :
    NumberFieldArchimedeanJacobiData (numberFieldArchimedeanSchur A) where
  realU := fun w => matrixFirstTail (J.realU w)
  realD := fun w i => J.realD w i.succ
  realPos := fun w i => J.realPos w i.succ
  realUpper := fun w i j hij => J.realUpper w i.succ j.succ (by simpa using hij)
  realUnit := fun w i => J.realUnit w i.succ
  realForm := fun w => by
    change matrixFirstSchur
        (A.1.1 w : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = _
    rw [← J.realJacobiData_form w]
    exact (J.realJacobiData w).firstTail_form.symm
  complexU := fun w => matrixFirstTail (J.complexU w)
  complexD := fun w i => J.complexD w i.succ
  complexPos := fun w i => J.complexPos w i.succ
  complexUpper := fun w i j hij => J.complexUpper w i.succ j.succ (by simpa using hij)
  complexUnit := fun w i => J.complexUnit w i.succ
  complexForm := fun w => by
    change matrixFirstSchur
        (A.1.2 w : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = _
    rw [← J.complexJacobiData_form w]
    rw [← (J.complexJacobiData w).firstTail_form]
    change Matrix.conjTranspose (matrixFirstTail (J.complexU w)) *
        Matrix.diagonal (fun i : Fin n => ((J.complexD w i.succ).re : ℂ)) *
          matrixFirstTail (J.complexU w) = _
    have hd : (fun i : Fin n => ((J.complexD w i.succ).re : ℂ)) =
        fun i => J.complexD w i.succ := by
      funext i
      exact (J.complexD_eq_ofReal_re w i.succ).symm
    rw [hd]

omit [NumberField K] in
@[simp]
theorem NumberFieldArchimedeanJacobiData.firstTail_realD
    {A : numberFieldArchimedeanPositiveForms K (n + 1)}
    (J : NumberFieldArchimedeanJacobiData A) (w) (i : Fin n) :
    J.firstTail.realD w i = J.realD w i.succ := rfl

omit [NumberField K] in
@[simp]
theorem NumberFieldArchimedeanJacobiData.firstTail_complexD
    {A : numberFieldArchimedeanPositiveForms K (n + 1)}
    (J : NumberFieldArchimedeanJacobiData A) (w) (i : Fin n) :
    J.firstTail.complexD w i = J.complexD w i.succ := rfl

@[simp]
theorem NumberFieldArchimedeanJacobiData.firstTail_mass
    {A : numberFieldArchimedeanPositiveForms K (n + 1)}
    (J : NumberFieldArchimedeanJacobiData A) (i : Fin n) :
    numberFieldArchimedeanJacobiMass J.firstTail i =
      numberFieldArchimedeanJacobiMass J i.succ := by
  rfl

/-- Jacobi-coordinate form of recursive primitive minimality. -/
def NumberFieldArchimedeanJacobiData.IsMassGreedy :
    (m : ℕ) → (A : numberFieldArchimedeanPositiveForms K m) →
      NumberFieldArchimedeanJacobiData A → Prop
  | 0, _, _ => True
  | 1, _, _ => True
  | m + 2, _, J =>
      numberFieldArchimedeanJacobiMass J (0 : Fin (m + 2)) ≤
          numberFieldArchimedeanJacobiFormDiagonalMass J (1 : Fin (m + 2)) ∧
        NumberFieldArchimedeanJacobiData.IsMassGreedy (m + 1) _ J.firstTail

/-- A recursively primitive-minimal cone point makes every simultaneous Jacobi decomposition
mass-greedy.  The coordinate-basis competitor is constructed and proved primitive internally. -/
theorem NumberFieldArchimedeanJacobiData.isMassGreedy_of_greedyFlag :
    ∀ (m : ℕ) (A : numberFieldArchimedeanPositiveForms K m)
      (J : NumberFieldArchimedeanJacobiData A),
      NumberFieldArchimedeanGreedyFlag m A → J.IsMassGreedy m A := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero =>
      intro A J h
      trivial
  | one =>
      intro A J h
      trivial
  | more m ih0 ih1 =>
      intro A J h
      change (_ ∧ _) at h
      change (_ ∧ _)
      constructor
      · rw [← J.formDiagonalMass_zero (i := (0 : Fin (m + 2))) rfl,
          J.formDiagonalMass_eq_energy, J.formDiagonalMass_eq_energy]
        exact h.1 (numberFieldCoordinateBasis (K := K) (1 : Fin (m + 2)))
          (numberFieldCoordinateBasis_primitive (K := K) (1 : Fin (m + 2)))
      · exact ih1 (numberFieldArchimedeanSchur A) J.firstTail h.2

/-- One determinant-one integral action and one simultaneous Jacobi decomposition realize the
complete recursive mass-greedy flag; all witnesses are selected inside the theorem. -/
theorem exists_numberFieldArchimedean_massGreedyJacobi
    (K : Type*) [Field K] [NumberField K]
    (m : ℕ) (A : numberFieldArchimedeanPositiveForms K m) :
    ∃ (B : Matrix (Fin m) (Fin m) (𝓞 K)) (hB : B.det = 1)
      (J : NumberFieldArchimedeanJacobiData
        (numberFieldArchimedeanPositiveConj
          (transposeSpecialLinearOfDetOne B hB) A)),
      NumberFieldArchimedeanJacobiData.IsMassGreedy m
        (numberFieldArchimedeanPositiveConj
          (transposeSpecialLinearOfDetOne B hB) A) J := by
  obtain ⟨B, hB, hflag⟩ := exists_numberFieldArchimedean_greedyFlag K m A
  let A' : numberFieldArchimedeanPositiveForms K m :=
    numberFieldArchimedeanPositiveConj (transposeSpecialLinearOfDetOne B hB) A
  have hflag' : NumberFieldArchimedeanGreedyFlag m A' := hflag
  let J : NumberFieldArchimedeanJacobiData A' :=
    Classical.choice (exists_numberFieldArchimedeanJacobiData A')
  refine ⟨B, hB, J, ?_⟩
  exact NumberFieldArchimedeanJacobiData.isMassGreedy_of_greedyFlag m A' J hflag'

end

end GaloisForLFunctions.HTGeometry
