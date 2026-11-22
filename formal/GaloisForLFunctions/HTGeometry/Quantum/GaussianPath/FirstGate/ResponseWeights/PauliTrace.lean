import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.EnergyWitness
import GaloisForLFunctions.HTGeometry.PauliCommutatorCoefficient

/-! # Energy covariance of each physical local Pauli -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.FirstGate.ResponseWeights
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Expectation of the specified onsite or bond Pauli in energy eigenstate j. -/
def localMean {n : ℕ} (p : PathShell n) (l : PathLabel n) (j : Fin (n+2)→Bool) : ℝ :=
  let V : Reg (n+2) := (isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvectorUnitary
  ((star V*finitePauliMatrix (pathWord l)*V) j j).re

private theorem trace_local {n : ℕ} (p : PathShell n) (l : PathLabel n) :
    ((pathHamiltonian p*finitePauliMatrix (pathWord l)).trace).re=2^(n+2)*p l := by
  rw [pathHamiltonian_eq_sum,Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum,Finset.sum_eq_single l]
  · have he : ((2:ℂ)^(n+2)).re=(2:ℝ)^(n+2) := by
      rw [show (2:ℂ)^(n+2)=((2:ℝ)^(n+2):ℝ) by norm_cast,Complex.ofReal_re]
    simp [trace_pauli_mul,mul_comm,he]
  · intro j _ hj
    simp [trace_pauli_mul,pathWord_injective.ne hj]
  · exact fun h => (h (Finset.mem_univ l)).elim

/-- The signed covariance of the energies with one Pauli expectation is
exactly that Pauli's coefficient. This holds for every real shell. -/
theorem localMean_energy_sum {n : ℕ} (p : PathShell n) (l : PathLabel n) :
    ∑ j, (isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvalues j*localMean p l j=2^(n+2)*p l := by
  let hH := (isSelfAdjoint_pathHamiltonian p).isHermitian
  let V : Reg (n+2) := hH.eigenvectorUnitary
  let P := finitePauliMatrix (pathWord l)
  let D := diagonal (fun j => (hH.eigenvalues j:ℂ))
  have hs : pathHamiltonian p=V*D*star V := isHermitian_eq_conj_diagonal hH
  have he : (pathHamiltonian p*P).trace=(D*(star V*P*V)).trace := by
    rw [hs]
    calc
      _ = (V*(D*(star V*P))).trace := by simp only [mul_assoc]
      _ = ((D*(star V*P))*V).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [mul_assoc]
  have h := (congrArg Complex.re he).symm.trans (trace_local p l)
  simpa only [Matrix.trace,Matrix.diag_apply,D,Matrix.diagonal_mul,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,localMean,V,hH,P] using h

theorem localMean_sum {n : ℕ} (p : PathShell n) (l : PathLabel n) : ∑ j, localMean p l j=0 := by
  let V : Reg (n+2) := (isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvectorUnitary
  let P := finitePauliMatrix (pathWord l)
  have hv : V*star V=1 := (Unitary.mem_iff.mp (isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvectorUnitary.2).2
  have he : (star V*P*V).trace=P.trace := by
    rw [Matrix.trace_mul_comm (star V*P) V,←mul_assoc,hv,one_mul]
  have hz : P.trace=0 := finitePauliMatrix_trace_eq_zero_of_ne_identity _ (pathWord_ne_identity l)
  simpa only [Matrix.trace,Matrix.diag_apply,Complex.re_sum,Complex.zero_re,localMean,V,P] using
    congrArg Complex.re (he.trans hz)

#print axioms localMean_energy_sum
end
end GaloisForLFunctions.HTGeometry.FirstGate.ResponseWeights
