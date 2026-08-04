import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectSelector

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Entrywise tensor product of arbitrary one-qubit matrices over a finite
register. -/
def finiteLocalMatrix
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (M : σ → Matrix Bool Bool ℂ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  fun x y => ∏ s, M s (x s) (y s)

theorem finiteLocalMatrix_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (M N : σ → Matrix Bool Bool ℂ) :
    finiteLocalMatrix M * finiteLocalMatrix N =
      finiteLocalMatrix fun s => M s * N s := by
  ext x z
  rw [Matrix.mul_apply]
  change (∑ y : σ → Bool,
      (∏ s, M s (x s) (y s)) * (∏ s, N s (y s) (z s))) =
    ∏ s, ∑ y : Bool, M s (x s) y * N s y (z s)
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun s (y : Bool) =>
    M s (x s) y * N s y (z s)).symm

theorem finitePauliMatrix_eq_finiteLocalMatrix
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    finitePauliMatrix P = finiteLocalMatrix fun s => boolPauliOption (P s) := by
  rfl

theorem finiteLocalMatrix_pointwise_smul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (c : σ → ℂ) (M : σ → Matrix Bool Bool ℂ) :
    finiteLocalMatrix (fun s => c s • M s) =
      (∏ s, c s) • finiteLocalMatrix M := by
  ext x y
  change (∏ s, c s * M s (x s) (y s)) =
    (∏ s, c s) * ∏ s, M s (x s) (y s)
  exact Finset.prod_mul_distrib

/-- Local conjugation sign for phase-free Pauli labels. -/
def boolPauliConjugationSign
    (q p : Option (Fin 3)) : ℂ :=
  if q = none ∨ p = none ∨ q = p then 1 else -1

theorem boolPauliOption_conj
    (q p : Option (Fin 3)) :
    boolPauliOption q * boolPauliOption p * boolPauliOption q =
      boolPauliConjugationSign q p • boolPauliOption p := by
  cases q with
  | none => simp [boolPauliOption, boolPauliConjugationSign]
  | some a =>
      cases p with
      | none =>
          simpa [boolPauliOption, boolPauliConjugationSign] using
            boolPauliOption_mul_self (some a)
      | some b =>
          simp only [boolPauliOption]
          rw [finiteQubitPauli_conj]
          by_cases hab : a = b
          · subst b
            simp [boolPauliConjugationSign]
          · simp [hab, boolPauliConjugationSign]

/-- Product conjugation sign of two finite Pauli strings. -/
def finitePauliConjugationSign
    {σ : Type*} [Fintype σ]
    (Q P : σ → Option (Fin 3)) : ℂ :=
  ∏ s, boolPauliConjugationSign (Q s) (P s)

/-- Conjugating any finite Pauli string by another changes only its sign. -/
theorem finitePauliMatrix_conj
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q P : σ → Option (Fin 3)) :
    finitePauliMatrix Q * finitePauliMatrix P * finitePauliMatrix Q =
      finitePauliConjugationSign Q P • finitePauliMatrix P := by
  simp only [finitePauliMatrix_eq_finiteLocalMatrix]
  rw [finiteLocalMatrix_mul, finiteLocalMatrix_mul]
  rw [show (fun s =>
      (boolPauliOption (Q s) * boolPauliOption (P s)) *
        boolPauliOption (Q s)) =
      (fun s => boolPauliConjugationSign (Q s) (P s) •
        boolPauliOption (P s)) by
    funext s
    rw [boolPauliOption_conj]]
  exact finiteLocalMatrix_pointwise_smul _ _

theorem boolPauliConjugationSign_sq
    (q p : Option (Fin 3)) :
    boolPauliConjugationSign q p * boolPauliConjugationSign q p = 1 := by
  simp only [boolPauliConjugationSign]
  split <;> norm_num

theorem finitePauliConjugationSign_sq
    {σ : Type*} [Fintype σ]
    (Q P : σ → Option (Fin 3)) :
    finitePauliConjugationSign Q P * finitePauliConjugationSign Q P = 1 := by
  rw [finitePauliConjugationSign, ← Finset.prod_mul_distrib]
  simp [boolPauliConjugationSign_sq]

end

end GaloisForLFunctions.HTGeometry
