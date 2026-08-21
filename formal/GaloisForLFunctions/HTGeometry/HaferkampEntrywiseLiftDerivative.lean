import GaloisForLFunctions.HTGeometry.HaferkampTerminalPauliPhase

open scoped BigOperators ComplexConjugate Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Entrywise real derivatives commute with multiplication by a fixed matrix
on the right. -/
theorem EntrywiseMatrixHasDerivAt.mul_right_const
    {ι κ μ : Type*} [Fintype κ] [DecidableEq κ]
    {F : ℝ → Matrix ι κ ℂ} {F' : Matrix ι κ ℂ} {t : ℝ}
    (hF : EntrywiseMatrixHasDerivAt F F' t) (C : Matrix κ μ ℂ) :
    EntrywiseMatrixHasDerivAt (fun s => F s * C) (F' * C) t := by
  intro i k
  change HasDerivAt (fun s : ℝ => ∑ j, F s i j * C j k) ((F' * C) i k) t
  simpa only [Matrix.mul_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (hF i j).mul_const (C j k)))

/-- A reverse-chronological finite word with one varying gate and an identity
suffix has its derivative at that gate followed by the fixed earlier word. -/
theorem entrywiseHasDerivAt_reverseProd_replace_of_suffix_one
    {N : Type*} [Fintype N] [DecidableEq N]
    (before after : List (Matrix N N ℂ))
    {F : ℝ → Matrix N N ℂ} {F' : Matrix N N ℂ} {t : ℝ}
    (hF : EntrywiseMatrixHasDerivAt F F' t)
    (hafter : ∀ M ∈ after, M = 1) :
    EntrywiseMatrixHasDerivAt
      (fun s => (before ++ F s :: after).reverse.prod)
      (F' * before.reverse.prod) t := by
  have hafterReverse : ∀ M ∈ after.reverse, M = 1 := by
    intro M hM
    exact hafter M (by simpa using hM)
  have hproduct : ∀ s,
      (before ++ F s :: after).reverse.prod = F s * before.reverse.prod := by
    intro s
    rw [List.reverse_append, List.prod_append, List.reverse_cons, List.prod_append,
      List.prod_eq_one hafterReverse]
    simp
  rw [show (fun s => (before ++ F s :: after).reverse.prod) =
    (fun s => F s * before.reverse.prod) by funext s; exact hproduct s]
  exact hF.mul_right_const before.reverse.prod

/-- The arbitrary two-qubit matrix lift is complex-linear. -/
theorem twoQubitLiftMatrix_smul
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b) (c : ℂ)
    (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    twoQubitLiftMatrix a b hab (c • M) = c • twoQubitLiftMatrix a b hab M := by
  ext x y
  simp [twoQubitLiftMatrix, Matrix.reindex_apply, Matrix.smul_apply]
  ring

/-- Entrywise real differentiability is preserved by the arbitrary finite
two-qubit matrix lift. -/
theorem EntrywiseMatrixHasDerivAt.twoQubitLiftMatrix
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {F : ℝ → Matrix (Bool × Bool) (Bool × Bool) ℂ}
    {F' : Matrix (Bool × Bool) (Bool × Bool) ℂ} {t : ℝ}
    (hF : EntrywiseMatrixHasDerivAt F F' t)
    (a b : Q) (hab : a ≠ b) :
    EntrywiseMatrixHasDerivAt (fun s => twoQubitLiftMatrix a b hab (F s))
      (twoQubitLiftMatrix a b hab F') t := by
  intro x y
  change HasDerivAt (fun s : ℝ =>
      F s ((splitTwoQubitConfig a b hab x).1) ((splitTwoQubitConfig a b hab y).1) *
        (1 : Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
          ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ)
          ((splitTwoQubitConfig a b hab x).2) ((splitTwoQubitConfig a b hab y).2))
      (F' ((splitTwoQubitConfig a b hab x).1) ((splitTwoQubitConfig a b hab y).1) *
        (1 : Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
          ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ)
          ((splitTwoQubitConfig a b hab x).2) ((splitTwoQubitConfig a b hab y).2)) t
  exact (hF _ _).mul_const _

/-- The terminal `SU(4)` phase path, lifted to any two register coordinates,
has tangent `i` times the lifted `I ⊗ Z` terminal direction. -/
theorem entrywiseHasDerivAt_twoQubitLift_terminalPauliGatePath
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    EntrywiseMatrixHasDerivAt (fun t : ℝ =>
      (twoQubitLift a b hab (terminalPauliGatePath U t) :
        Matrix (Q → Bool) (Q → Bool) ℂ))
      (Complex.I • twoQubitLiftMatrix a b hab
        (boolTwoQubitPauli none (some 2) *
          (U : Matrix (Bool × Bool) (Bool × Bool) ℂ))) 0 := by
  have hlocal := entrywiseHasDerivAt_terminalPauliGatePath U
  have hlift := hlocal.twoQubitLiftMatrix a b hab
  rw [twoQubitLiftMatrix_smul] at hlift
  exact hlift

end

end GaloisForLFunctions.HTGeometry
