import GaloisForLFunctions.HTGeometry.FinitePauliConjugationLaw

/-!
# The signed product law of Pauli strings

Two single-qubit Pauli labels multiply to a fourth root of unity times a third label, with the
label product the Klein four-group law and the phase `±i` on distinct nonidentity labels.  Taking
products over sites, the product of two Pauli strings is the product of the sitewise phases times
the Pauli string of the sitewise label product.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The Klein four-group law on single-qubit Pauli labels. -/
def optMul : Option (Fin 3) → Option (Fin 3) → Option (Fin 3)
  | none, q => q
  | some a, none => some a
  | some a, some b => if a = b then none else some ((a + b) + (a + b))

/-- The phase produced by multiplying two single-qubit Pauli labels. -/
def optPhase : Option (Fin 3) → Option (Fin 3) → ℂ
  | none, _ => 1
  | some _, none => 1
  | some a, some b => if a = b then 1 else if b = a + 1 then Complex.I else -Complex.I

/-- **The single-qubit Pauli product law.** -/
theorem boolPauliOption_mul (p q : Option (Fin 3)) :
    boolPauliOption p * boolPauliOption q = optPhase p q • boolPauliOption (optMul p q) := by
  ext x y
  fin_cases p <;> fin_cases q <;> fin_cases x <;> fin_cases y <;>
    norm_num +decide [boolPauliOption, finiteQubitPauli, optMul, optPhase, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.one_apply, Complex.ext_iff]

/-- **The Pauli string product law.** -/
theorem finitePauliMatrix_mul {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P Q : σ → Option (Fin 3)) :
    finitePauliMatrix P * finitePauliMatrix Q =
      (∏ s, optPhase (P s) (Q s)) • finitePauliMatrix fun s => optMul (P s) (Q s) := by
  simp only [finitePauliMatrix_eq_finiteLocalMatrix]
  rw [finiteLocalMatrix_mul]
  have hstep : (fun s => boolPauliOption (P s) * boolPauliOption (Q s)) =
      fun s => optPhase (P s) (Q s) • boolPauliOption (optMul (P s) (Q s)) := by
    funext s
    exact boolPauliOption_mul (P s) (Q s)
  rw [hstep, finiteLocalMatrix_pointwise_smul]

theorem optMul_self (p : Option (Fin 3)) : optMul p p = none := by
  cases p with
  | none => rfl
  | some a => simp [optMul]

theorem optPhase_self (p : Option (Fin 3)) : optPhase p p = 1 := by
  cases p with
  | none => rfl
  | some a => simp [optPhase]

theorem optMul_none_right (p : Option (Fin 3)) : optMul p none = p := by
  cases p <;> rfl

theorem optPhase_none_right (p : Option (Fin 3)) : optPhase p none = 1 := by
  cases p <;> rfl

theorem optMul_comm (p q : Option (Fin 3)) : optMul p q = optMul q p := by
  cases p with
  | none => rw [optMul, optMul_none_right]
  | some a =>
      cases q with
      | none => rw [optMul_none_right, optMul]
      | some b =>
          by_cases h : a = b
          · subst h
            rfl
          · rw [optMul, optMul, if_neg h, if_neg (fun hc => h hc.symm), add_comm a b]

end GaloisForLFunctions.HTGeometry
