import GaloisForLFunctions.HTGeometry.FinitePauliDepolarizing

/-! # The trace and skew part of a unitary from Pauli commutators -/

open Matrix Finset Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages
noncomputable section
variable {K : ℕ}
private abbrev Reg (K : ℕ) := Matrix (FiniteQubitConfiguration (Fin K)) (FiniteQubitConfiguration (Fin K)) ℂ

/-- A Pauli word and its conjugate can both be rotated on the same register. -/
def pauliBracket (U : Reg K) (j : Fin K → Option (Fin 3)) : Reg K :=
  let P := finitePauliMatrix j
  let Q := U*P*star U
  Q*P-P*Q

/-- The commutator mean is exactly the skew part of the circuit after
the phase of its normalized trace has been removed. -/
theorem mean_pauli_bracket (U : Reg K) :
    let τ := U.trace/(2:ℂ)^K
    ((4:ℂ)^K)⁻¹ • (∑ j, pauliBracket U j)=conj τ • U-τ • star U := by
  intro τ
  have h (j : Fin K → Option (Fin 3)) :
      pauliBracket U j=U*(finitePauliMatrix j*star U*finitePauliMatrix j)-
        (finitePauliMatrix j*U*finitePauliMatrix j)*star U := by
    simp only [pauliBracket,Matrix.mul_assoc]
  simp_rw [h]
  rw [Finset.sum_sub_distrib,←Matrix.mul_sum,←Matrix.sum_mul,
    sum_finitePauliMatrix_conj,sum_finitePauliMatrix_conj,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,Matrix.one_mul,smul_sub,smul_smul,smul_smul,Fintype.card_fin]
  have hfour : (4:ℂ)^K=(2^K)^2 := by rw [←pow_mul, mul_comm K 2,pow_mul]; norm_num
  have hn : (2:ℂ)^K≠0 := pow_ne_zero _ (by norm_num)
  have he (z : ℂ) : ((4:ℂ)^K)⁻¹*(2^K*z)=z/2^K := by rw [hfour]; field_simp
  rw [he,he,Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose]
  have htwo : conj (2:ℂ)=2 := by exact_mod_cast Complex.conj_ofReal 2
  simp [τ,htwo]

#print axioms mean_pauli_bracket
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages
