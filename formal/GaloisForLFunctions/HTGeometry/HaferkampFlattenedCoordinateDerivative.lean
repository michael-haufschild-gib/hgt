import GaloisForLFunctions.HTGeometry.HaferkampFlattenedTerminalGates
import GaloisForLFunctions.HTGeometry.HaferkampEntrywiseLiftDerivative

/-!
# Derivatives of selected coordinates in flattened gate words

Unlike an isolated BLC block, a selected terminal gate in a flattened assembly
has a nontrivial later-word suffix.  These elementary entrywise product rules
give its exact derivative without treating that suffix as identity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Entrywise real derivatives commute with multiplication by a fixed matrix
on the left. -/
theorem EntrywiseMatrixHasDerivAt.mul_left_const
    {ι κ μ : Type*} [Fintype κ] [DecidableEq κ]
    {F : ℝ → Matrix κ μ ℂ} {F' : Matrix κ μ ℂ} {t : ℝ}
    (C : Matrix ι κ ℂ) (hF : EntrywiseMatrixHasDerivAt F F' t) :
    EntrywiseMatrixHasDerivAt (fun s => C * F s) (C * F') t := by
  intro i k
  change HasDerivAt (fun s : ℝ => ∑ j, C i j * F s j k) ((C * F') i k) t
  simpa [Matrix.mul_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (hasDerivAt_const (x := t) (c := C i j)).mul (hF j k)))

/-- Replacing one gate in a reverse-chronological finite word differentiates
to the later suffix, the gate derivative, and the earlier prefix, in that
order. -/
theorem entrywiseHasDerivAt_reverseProd_replace
    {N : Type*} [Fintype N] [DecidableEq N]
    (before after : List (Matrix N N ℂ))
    {F : ℝ → Matrix N N ℂ} {F' : Matrix N N ℂ} {t : ℝ}
    (hF : EntrywiseMatrixHasDerivAt F F' t) :
    EntrywiseMatrixHasDerivAt
      (fun s => (before ++ F s :: after).reverse.prod)
      (after.reverse.prod * F' * before.reverse.prod) t := by
  have hproduct : ∀ s : ℝ,
      (before ++ F s :: after).reverse.prod =
        after.reverse.prod * F s * before.reverse.prod := by
    intro s
    rw [List.reverse_append, List.prod_append, List.reverse_cons, List.prod_append]
    simp only [List.prod_cons, List.prod_nil, one_mul, Matrix.mul_assoc]
  rw [show (fun s => (before ++ F s :: after).reverse.prod) =
      (fun s => after.reverse.prod * F s * before.reverse.prod) by
        funext s; exact hproduct s]
  exact (hF.mul_left_const after.reverse.prod).mul_right_const before.reverse.prod

/-- Lifting the exact terminal `SU(4)` phase at the root-targeting edge has
the root-Pauli tangent used by every flattened terminal coordinate. -/
theorem entrywiseHasDerivAt_totalTwoQubitLift_terminalPauliGatePath
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    EntrywiseMatrixHasDerivAt (fun t : ℝ =>
      (totalTwoQubitLift (cone.mergePlan.terminal, root) (terminalPauliGatePath U t) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (Complex.I • (finitePauliMatrix
        (Function.update (fun _ => none) root (some 2)) *
        (totalTwoQubitLift (cone.mergePlan.terminal, root) U :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ))) 0 := by
  have hlift := entrywiseHasDerivAt_twoQubitLift_terminalPauliGatePath
    cone.mergePlan.terminal root cone.mergePlan.terminal_ne_root U
  have htotal (V : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
      (totalTwoQubitLift (cone.mergePlan.terminal, root) V :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      (twoQubitLift cone.mergePlan.terminal root cone.mergePlan.terminal_ne_root V :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    exact congrArg (fun W : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (totalTwoQubitLift_eq_twoQubitLift
        (cone.mergePlan.terminal, root) cone.mergePlan.terminal_ne_root V)
  have hroot : twoQubitLiftMatrix cone.mergePlan.terminal root
      cone.mergePlan.terminal_ne_root
      (boolTwoQubitPauli none (some 2) *
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) =
      finitePauliMatrix (Function.update (fun _ => none) root (some 2)) *
        (totalTwoQubitLift (cone.mergePlan.terminal, root) U :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    rw [twoQubitLiftMatrix_terminal_coordinate]
    rw [← totalTwoQubitLift_eq_twoQubitLift
      (cone.mergePlan.terminal, root) cone.mergePlan.terminal_ne_root U]
    congr 2
    funext q
    by_cases hq : q = root
    · subst q
      simp [updateTwoQubitPauliLabel]
    · simp [updateTwoQubitPauliLabel, hq]
  rw [show (fun t : ℝ =>
      (totalTwoQubitLift (cone.mergePlan.terminal, root) (terminalPauliGatePath U t) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) =
      (fun t : ℝ =>
        (twoQubitLift cone.mergePlan.terminal root cone.mergePlan.terminal_ne_root
          (terminalPauliGatePath U t) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) by
        funext t; exact htotal (terminalPauliGatePath U t)]
  rw [show Complex.I • twoQubitLiftMatrix cone.mergePlan.terminal root
      cone.mergePlan.terminal_ne_root
      (boolTwoQubitPauli none (some 2) *
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) =
      Complex.I • (finitePauliMatrix
        (Function.update (fun _ => none) root (some 2)) *
        (totalTwoQubitLift (cone.mergePlan.terminal, root) U :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) by rw [hroot]]
  exact hlift

end

end GaloisForLFunctions.HTGeometry
