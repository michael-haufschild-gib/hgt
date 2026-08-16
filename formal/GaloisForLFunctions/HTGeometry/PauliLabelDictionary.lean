import GaloisForLFunctions.HTGeometry.PauliProductLaw
import GaloisForLFunctions.HTGeometry.PauliSymplecticTransitivity

/-!
# The dictionary between binary symplectic labels and Pauli strings

A binary symplectic label at one site names one of the four single-qubit Pauli matrices, with label
addition the Klein four-group law and the commutation form the sign produced by conjugation.  Over
all sites, the symplectic sum of labels names the Pauli-string product and the commutation form
records whether the two strings commute.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- The single-qubit Pauli label named by a binary symplectic pair. -/
def sitePauli (p : ZMod 2 × ZMod 2) : Option (Fin 3) :=
  if p.1 = 0 then (if p.2 = 0 then none else some 2)
  else (if p.2 = 0 then some 0 else some 1)

/-- The Pauli string named by a binary symplectic label. -/
def pauliOf (u : PauliSymp n) : Fin n → Option (Fin 3) := fun i => sitePauli (u i)

theorem sitePauli_zero : sitePauli (0 : ZMod 2 × ZMod 2) = none := by decide

theorem sitePauli_injective : Function.Injective sitePauli := by decide

theorem optMul_sitePauli (a b : ZMod 2 × ZMod 2) :
    optMul (sitePauli a) (sitePauli b) = sitePauli (a + b) := by
  revert a b
  decide

/-- The sign attached to a residue. -/
def signOf (z : ZMod 2) : ℂ := if z = 0 then 1 else -1

theorem zmodTwo_cases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

theorem signOf_add (a b : ZMod 2) : signOf (a + b) = signOf a * signOf b := by
  rcases zmodTwo_cases a with rfl | rfl <;> rcases zmodTwo_cases b with rfl | rfl <;>
    simp +decide [signOf]

theorem signOf_sq (z : ZMod 2) : signOf z * signOf z = 1 := by
  rcases zmodTwo_cases z with rfl | rfl <;> simp +decide [signOf]

theorem signOf_ne_zero (z : ZMod 2) : signOf z ≠ 0 := by
  rcases zmodTwo_cases z with rfl | rfl <;> simp +decide [signOf]

/-- The single-site commutation sign is the sign of the single-site symplectic form. -/
theorem boolPauliConjugationSign_sitePauli (a b : ZMod 2 × ZMod 2) :
    boolPauliConjugationSign (sitePauli a) (sitePauli b) = signOf (a.1 * b.2 + a.2 * b.1) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  rcases zmodTwo_cases a1 with rfl | rfl <;> rcases zmodTwo_cases a2 with rfl | rfl <;>
    rcases zmodTwo_cases b1 with rfl | rfl <;> rcases zmodTwo_cases b2 with rfl | rfl <;>
    simp +decide [boolPauliConjugationSign, signOf]

theorem pauliOf_zero : pauliOf (0 : PauliSymp n) = fun _ => none := by
  funext i
  rw [pauliOf]
  exact sitePauli_zero

theorem pauliOf_injective : Function.Injective (pauliOf (n := n)) := by
  intro u v h
  funext i
  exact sitePauli_injective (congrFun h i)

theorem optMul_pauliOf (u v : PauliSymp n) :
    (fun i => optMul (pauliOf u i) (pauliOf v i)) = pauliOf (u + v) := by
  funext i
  exact optMul_sitePauli (u i) (v i)

/-- **The commutation sign of two Pauli strings is the sign of their symplectic form.** -/
theorem finitePauliConjugationSign_pauliOf (u v : PauliSymp n) :
    finitePauliConjugationSign (pauliOf u) (pauliOf v) = signOf (symForm u v) := by
  rw [finitePauliConjugationSign, symForm]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => simp [signOf]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, signOf_add]
      congr 1
      exact boolPauliConjugationSign_sitePauli (u a) (v a)

end GaloisForLFunctions.HTGeometry
