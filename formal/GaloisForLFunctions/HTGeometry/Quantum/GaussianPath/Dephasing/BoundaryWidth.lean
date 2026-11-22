import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.Pinching
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.ResponseWeights.PauliTrace
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliContextuality
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # Spectral width of every dephased physical coupling -/
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing
noncomputable section
open FirstGate.ResponseWeights
private abbrev Reg (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

def couplingField {n : ℕ} (l : PathLabel n) : selfAdjoint (Reg (n+2)) :=
  ⟨finitePauliMatrix (pathWord l),(finitePauliMatrix_isHermitian _).isSelfAdjoint⟩

/-- The coupling-energy fraction bounds the squared half-width of its
dephased Pauli. Subtract the optimal scalar from the Pauli expectations
before applying Cauchy–Schwarz to their energy covariance. -/
theorem coupling_width_floor {n : ℕ} (p : PathShell n) (l : PathLabel n) :
    let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian _⟩
    let D := pinchedField H (couplingField l)
    (p l)^2 ≤ (∑ m : PathLabel n, (p m)^2)*(circuitHamiltonianSpectralWidth D/2)^2 := by
  intro H D
  let W := circuitHamiltonianSpectralWidth D/2
  let U : Reg (n+2) := H.2.isHermitian.eigenvectorUnitary
  let b (i : Fin (n+2)→Bool) := (star U*(couplingField l).val*U) i i
  let E := H.2.isHermitian.eigenvalues
  let d := (2:ℝ)^(n+2)
  let S := ∑ m : PathLabel n, (p m)^2
  have hd : 0 < d := pow_pos (by norm_num) _
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU : U∈unitary (Reg (n+2)) := H.2.isHermitian.eigenvectorUnitary.2
  obtain ⟨c,hc,_⟩ := exists_optimal_scalarCenteredHamiltonian D
  have hcI : (c:ℂ) • (1 : Reg (n+2))=U*diagonal (fun _ => (c:ℂ))*star U := by
    rw [←smul_one_eq_diagonal_const,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,(Unitary.mem_iff.mp hU).2]
  have hwidth : ‖fun i => b i-(c:ℂ)‖=W := by
    change ‖U*diagonal b*star U-(c:ℂ) • (1 : Reg (n+2))‖=W at hc
    rwa [hcI,←Matrix.sub_mul,←Matrix.mul_sub,Matrix.diagonal_sub,l2_opNorm_unitary_conj_eq hU,
      Matrix.l2_opNorm_diagonal] at hc
  have hbound (i : Fin (n+2)→Bool) : |localMean p l i-c| ≤ W := by
    calc _ = |(b i-(c:ℂ)).re| := rfl
         _ ≤ _ := (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm (fun j => b j-(c:ℂ)) i).trans_eq hwidth)
  have hsq : (∑ i, (localMean p l i-c)^2) ≤ d*W^2 := by
    calc _ ≤ ∑ _ : Fin (n+2)→Bool, W^2 := Finset.sum_le_sum fun i _ => by
             simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound i) 2
         _ = _ := by simp [d,nsmul_eq_mul]
  have hE := FluxOccupation.path_spectral_moments p
  have he : ∑ i, E i*(localMean p l i-c)=d*p l := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
    change (∑ i, (isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvalues i*localMean p l i)-
      (∑ i, (isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvalues i)*c=_
    rw [localMean_energy_sum,hE.1,zero_mul,sub_zero]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ E (fun i => localMean p l i-c)
  have hesq : ∑ i, E i^2=d*S := by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hE.2
  rw [he,hesq] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left hsq (mul_nonneg hd.le hS))
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hd)).mp
  calc d^2*(p l)^2 = (d*p l)^2 := (mul_pow ..).symm
       _ ≤ _ := h'
       _ = _ := by ring

/-- Each individual onsite or bond field has positive dephased width on
every prefix of a single Gaussian chain. -/
theorem gaussian_coupling_width_pos :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
      let p := pathPauliDisorderShell ω n
      let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian _⟩
      ∀ l : PathLabel n, 0 < circuitHamiltonianSpectralWidth (pinchedField H (couplingField l)) := by
  filter_upwards [gaussian_path_ae_nonzero_coordinates] with ω hω n
  intro p H l
  have hp : p l≠0 := by rcases l with ⟨i,a⟩|⟨e,ab⟩ <;> exact hω _
  apply lt_of_le_of_ne (circuitHamiltonianSpectralWidth_nonneg _) 
  intro he
  have h := coupling_width_floor p l
  change (p l)^2 ≤ _*(circuitHamiltonianSpectralWidth (pinchedField H (couplingField l))/2)^2 at h
  rw [←he,zero_div,zero_pow (by decide : 2≠0),mul_zero] at h
  exact (sq_pos_of_ne_zero hp).not_ge h

#print axioms coupling_width_floor
#print axioms gaussian_coupling_width_pos
end
end GaloisForLFunctions.HTGeometry.Dephasing
