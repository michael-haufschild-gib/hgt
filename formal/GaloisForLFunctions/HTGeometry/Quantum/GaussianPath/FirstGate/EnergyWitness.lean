import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.PathFactors
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # One onsite or bond observable distinguishes any pair of distinct energies -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
private abbrev Register (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Each energy is the coefficient-weighted sum of the diagonal
expectations of the physical Pauli terms in its own eigenstate. -/
theorem energy_from_local_expectations {n : ℕ} (u : PathShell n) :
    let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
    let V : Register (n+2) := hH.eigenvectorUnitary
    ∀ i, hH.eigenvalues i=∑ l : PathLabel n, u l*((star V*finitePauliMatrix (pathWord l)*V) i i).re := by
  intro hH V i
  let D := Matrix.diagonal (fun j => (hH.eigenvalues j:ℂ))
  have hV : star V*V=1 := (Unitary.mem_iff.mp hH.eigenvectorUnitary.2).1
  have hspec : pathHamiltonian u=V*D*star V := isHermitian_eq_conj_diagonal hH
  have h : D=star V*pathHamiltonian u*V := by
    rw [hspec]
    simp only [mul_assoc,hV,mul_one]
    rw [←mul_assoc,hV,one_mul]
  rw [pathHamiltonian_eq_sum,Finset.mul_sum,Finset.sum_mul] at h
  have he := congrArg (fun B : Register (n+2) => (B i i).re) h
  simpa only [D,Matrix.diagonal_apply_eq,Matrix.mul_smul,Matrix.smul_mul,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,Complex.re_sum,Complex.ofReal_re,Complex.ofReal_mul_re] using he

/-- A difference of energies forces a distinct first-order response to at
least one physical single-gate direction. -/
theorem exists_distinguishing_term {n : ℕ} (u : PathShell n) :
    let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
    let V : Register (n+2) := hH.eigenvectorUnitary
    ∀ a b, hH.eigenvalues a≠hH.eigenvalues b → ∃ l : PathLabel n,
      ((star V*finitePauliMatrix (pathWord l)*V) a a).re ≠
        ((star V*finitePauliMatrix (pathWord l)*V) b b).re := by
  intro hH V a b hab
  by_contra! h
  apply hab
  rw [energy_from_local_expectations u a,energy_from_local_expectations u b]
  exact Finset.sum_congr rfl fun l _ => congrArg (u l*·) (h l)

#print axioms exists_distinguishing_term
end
end GaloisForLFunctions.HTGeometry.FirstGate
