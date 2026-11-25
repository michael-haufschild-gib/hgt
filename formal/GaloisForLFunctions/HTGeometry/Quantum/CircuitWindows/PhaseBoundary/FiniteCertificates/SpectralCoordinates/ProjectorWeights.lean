import GaloisForLFunctions.HTGeometry.MatrixEntriesInSubfield
import GaloisForLFunctions.HTGeometry.MaximallyProjectivePhysicalCircuitHardIntervalLaw
import GaloisForLFunctions.QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import Mathlib.LinearAlgebra.Lagrange

/-! # Spectral-projector coefficients over the field of matrix entries and energies -/

open Matrix Polynomial Finset
open scoped ComplexConjugate Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.SpectralCoordinates
noncomputable section
variable {F : Type*} [Field F] [Algebra F ℂ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (K : IntermediateField F ℂ)

private theorem entries_aeval {H : Matrix ι ι ℂ} (hH : EntriesIn K H) (p : K[X]) :
    EntriesIn K (Polynomial.aeval H (p.map K.subtype)) := by
  have hp (n : ℕ) : EntriesIn K (H^n) := by
    induction n with
    | zero => rw [pow_zero]; exact EntriesIn.one
    | succ n ih => rw [pow_succ]; exact ih.mul hH
  induction p using Polynomial.induction_on' with
  | add p q a b => simpa only [Polynomial.map_add,map_add] using a.add b
  | monomial n c =>
    rw [Polynomial.map_monomial,Polynomial.aeval_monomial,←Algebra.smul_def]
    exact EntriesIn.smul c.property (hp n)

/-- Individual eigenvectors may acquire arbitrary phases. Each product
of a column entry and the conjugate of another entry is a projector
entry and lies in the field already containing H and its simple energies. -/
theorem projector_weight_mem {H : Matrix ι ι ℂ} (h : H.IsHermitian) (hH : EntriesIn K H)
    (he : ∀ j, (h.eigenvalues j:ℂ)∈K) (hinj : Function.Injective h.eigenvalues) (i j k : ι) :
    let V := hermitianEigenbasisUnitary h
    V.val i k*(V⁻¹).val k j ∈ K := by
  classical
  let λ' (j : ι) : K := ⟨_,he j⟩
  let p := Lagrange.basis Finset.univ λ' k
  have hλ : Function.Injective λ' := by
    intro j l hj
    apply hinj
    exact Complex.ofReal_injective (congrArg Subtype.val hj)
  have ev (l : ι) : (p.map K.subtype).eval (h.eigenvalues l:ℂ)=if k=l then 1 else 0 := by
    change (p.map K.subtype).eval (K.subtype (λ' l))=_
    rw [Polynomial.eval_map_apply]
    by_cases hh : k=l
    · subst l
      rw [if_pos rfl,Lagrange.eval_basis_self hλ.injOn (Finset.mem_univ _),map_one]
    · rw [if_neg hh,Lagrange.eval_basis_of_ne hh (Finset.mem_univ _),map_zero]
  have hm := entries_aeval K hH p i j
  rw [QuantumAlg.QSP.MultiQubit.QSVT.polynomialOperator_spectral _ _ h,
    Unitary.conjStarAlgAut_apply,Matrix.mul_apply] at hm
  simpa only [Matrix.mul_diagonal,ev,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,if_true] using hm

#print axioms projector_weight_mem
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.SpectralCoordinates

