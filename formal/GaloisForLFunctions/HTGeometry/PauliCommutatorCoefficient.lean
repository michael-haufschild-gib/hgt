import GaloisForLFunctions.HTGeometry.PauliCommutator
import GaloisForLFunctions.HTGeometry.PauliParseval

/-!
# Reading a Pauli coefficient off a commutator

Pairing a commutator of two Pauli combinations against a Pauli string with the Hilbert–Schmidt
trace selects exactly the index pairs whose label product is that string, weighted by the
difference of the two product phases.  This turns a vanishing commutator into a family of scalar
equations indexed by Pauli strings.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The total phase produced by multiplying two Pauli strings. -/
def optPhaseProd (S T : σ → Option (Fin 3)) : ℂ := ∏ s, optPhase (S s) (T s)

/-- The label product of two Pauli strings. -/
def optMulLabel (S T : σ → Option (Fin 3)) : σ → Option (Fin 3) := fun s => optMul (S s) (T s)

theorem finitePauliMatrix_mul' (S T : σ → Option (Fin 3)) :
    finitePauliMatrix S * finitePauliMatrix T =
      optPhaseProd S T • finitePauliMatrix (optMulLabel S T) :=
  finitePauliMatrix_mul S T

theorem optMulLabel_comm (S T : σ → Option (Fin 3)) : optMulLabel T S = optMulLabel S T := by
  funext s
  exact optMul_comm (T s) (S s)

/-- The Hilbert–Schmidt pairing of two Pauli strings. -/
theorem trace_pauli_mul (R S : σ → Option (Fin 3)) :
    Matrix.trace (finitePauliMatrix R * finitePauliMatrix S) =
      if R = S then (2 : ℂ) ^ Fintype.card σ else 0 := by
  have hstar : star (finitePauliMatrix R) = finitePauliMatrix R :=
    finitePauliMatrix_isHermitian R
  have h := trace_star_finitePauliMatrix_mul R S
  rw [hstar] at h
  exact h

/-- **The commutator coefficient of a single pair of Pauli strings.** -/
theorem trace_pauli_commutator (R S T : σ → Option (Fin 3)) :
    Matrix.trace (finitePauliMatrix R *
        (finitePauliMatrix S * finitePauliMatrix T -
          finitePauliMatrix T * finitePauliMatrix S)) =
      (optPhaseProd S T - optPhaseProd T S) *
        (if R = optMulLabel S T then (2 : ℂ) ^ Fintype.card σ else 0) := by
  rw [finitePauliMatrix_commutator]
  have hlabel : (fun s => optMul (S s) (T s)) = optMulLabel S T := rfl
  rw [hlabel]
  have hphase : ((∏ s, optPhase (S s) (T s)) - ∏ s, optPhase (T s) (S s)) =
      optPhaseProd S T - optPhaseProd T S := rfl
  rw [hphase, Matrix.mul_smul, Matrix.trace_smul, trace_pauli_mul, smul_eq_mul]

/-- **The commutator coefficient of two Pauli combinations.** -/
theorem trace_pauli_commutator_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : σ → Option (Fin 3)) (S : ι → (σ → Option (Fin 3))) (T : κ → (σ → Option (Fin 3)))
    (h : ι → ℂ) (k : κ → ℂ) :
    Matrix.trace (finitePauliMatrix R *
        ((∑ i, h i • finitePauliMatrix (S i)) * (∑ j, k j • finitePauliMatrix (T j)) -
          (∑ j, k j • finitePauliMatrix (T j)) * (∑ i, h i • finitePauliMatrix (S i)))) =
      ∑ i, ∑ j, h i * k j * ((optPhaseProd (S i) (T j) - optPhaseProd (T j) (S i)) *
        (if R = optMulLabel (S i) (T j) then (2 : ℂ) ^ Fintype.card σ else 0)) := by
  classical
  have hexpand : ((∑ i, h i • finitePauliMatrix (S i)) * (∑ j, k j • finitePauliMatrix (T j)) -
      (∑ j, k j • finitePauliMatrix (T j)) * (∑ i, h i • finitePauliMatrix (S i))) =
      ∑ i, ∑ j, (h i * k j) •
        (finitePauliMatrix (S i) * finitePauliMatrix (T j) -
          finitePauliMatrix (T j) * finitePauliMatrix (S i)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := Finset.univ)
      (t := (Finset.univ : Finset ι))]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, smul_smul, mul_comm (k j) (h i)]
  rw [hexpand, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, trace_pauli_commutator, smul_eq_mul]

end GaloisForLFunctions.HTGeometry
