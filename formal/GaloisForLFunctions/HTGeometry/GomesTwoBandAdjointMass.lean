import GaloisForLFunctions.HTGeometry.GomesPauliAdjointMass
import GaloisForLFunctions.HTGeometry.CoppoSSH
import GaloisForLFunctions.HTGeometry.NoncommutativeQubitExponentialFormation

/-!
# Adjoint Gram masses of the existing SSH and qubit Hamiltonians

The mass-kernel/stabilizer construction in Gomes, arXiv:2509.25276, is applied
mechanically to two actual two-band models in the corpus. The SSH gap polynomial
and the qubit spectral radius determine the transverse adjoint Gram eigenvalues.
For SSH, gap closure is exactly full Pauli stabilizer enlargement, and at the
zone boundary this occurs precisely when the hopping coefficients agree. These
are exact statements about the normalized commutator Gram, without adding a
physical gauge-field model or nonzero-parameter hypotheses.
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Real Pauli coordinates of the existing complex SSH hopping symbol. -/
def gomesSSHCarrier (u v theta : ℝ) : Fin 3 → ℝ :=
  ![(coppoSSHOffDiagonal u v theta).re,-(coppoSSHOffDiagonal u v theta).im,0]

/-- The actual SSH Bloch matrix is exactly the Pauli carrier of its hopping coordinates. -/
theorem gomesSSHCarrier_matrix (u v theta : ℝ) :
    gomesPauliCarrier (gomesSSHCarrier u v theta) = coppoSSHBloch u v theta := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [gomesPauliCarrier,gomesSSHCarrier,coppoSSHBloch,
      QuantumAlg.pauliX,QuantumAlg.pauliY,QuantumAlg.pauliZ]

/-- The existing SSH squared band gap is the exact carrier norm entering the adjoint mass matrix. -/
theorem gomesSSHCarrier_norm (u v theta : ℝ) :
    gomesSSHCarrier u v theta ⬝ᵥ gomesSSHCarrier u v theta = coppoSSHGapSq u v theta := by
  rw [← coppoSSHOffDiagonal_normSq]
  simp [gomesSSHCarrier,dotProduct,Fin.sum_univ_three,Complex.normSq_apply]

/-- The SSH massless directions are exactly the generators commuting with the actual Bloch matrix. -/
theorem gomesSSHAdjointMass_kernel (u v theta : ℝ) (x : Fin 3 → ℝ) :
    gomesPauliAdjointMass (gomesSSHCarrier u v theta) *ᵥ x = 0 ↔
      coppoSSHBloch u v theta * gomesPauliCarrier x =
        gomesPauliCarrier x * coppoSSHBloch u v theta := by
  rw [gomesPauliAdjointMass_kernel_iff_commutes,gomesSSHCarrier_matrix]

/-- The complete SSH adjoint characteristic determinant has two transverse roots at the band gap. -/
theorem gomesSSHAdjointMass_characteristic (u v theta mu : ℝ) :
    Matrix.det (mu • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
      gomesPauliAdjointMass (gomesSSHCarrier u v theta)) =
        mu * (mu - coppoSSHGapSq u v theta)^(2 : ℕ) := by
  rw [gomesPauliAdjointMass_characteristic,gomesSSHCarrier_norm]

/-- All adjoint masses vanish exactly when the SSH band gap closes. -/
theorem gomesSSHAdjointMass_zero_iff (u v theta : ℝ) :
    gomesPauliAdjointMass (gomesSSHCarrier u v theta) = 0 ↔ coppoSSHGapSq u v theta = 0 := by
  rw [gomesPauliAdjointMass_eq_zero_iff,← dotProduct_self_eq_zero,gomesSSHCarrier_norm]

/-- Gap closure is equivalent to enlargement of the infinitesimal stabilizer to every Pauli axis. -/
theorem gomesSSHBloch_full_stabilizer (u v theta : ℝ) :
    (∀ x : Fin 3 → ℝ, coppoSSHBloch u v theta * gomesPauliCarrier x =
      gomesPauliCarrier x * coppoSSHBloch u v theta) ↔ coppoSSHGapSq u v theta = 0 := by
  rw [← gomesSSHCarrier_matrix,gomesPauliCarrier_full_stabilizer,
    ← dotProduct_self_eq_zero,gomesSSHCarrier_norm]

/-- At the Brillouin-zone boundary, complete symmetry restoration is precisely equal hopping. -/
theorem gomesSSHAdjointMass_boundary (u v : ℝ) :
    gomesPauliAdjointMass (gomesSSHCarrier u v Real.pi) = 0 ↔ u = v := by
  rw [gomesSSHAdjointMass_zero_iff]
  have hgap : coppoSSHGapSq u v Real.pi = (u-v)^(2 : ℕ) := by
    simp [coppoSSHGapSq,Real.cos_pi]
    ring
  rw [hgap,sq_eq_zero_iff,sub_eq_zero]

/-- The sublattice Pauli-Z direction is a transverse mode with squared mass equal to the SSH gap. -/
theorem gomesSSHAdjointMass_transverse (u v theta : ℝ) :
    gomesPauliAdjointMass (gomesSSHCarrier u v theta) *ᵥ ![0,0,1] =
      coppoSSHGapSq u v theta • ![0,0,1] := by
  rw [gomesPauliAdjointMass_mulVec,gomesSSHCarrier_norm]
  have horth : gomesSSHCarrier u v theta ⬝ᵥ ![0,0,1] = 0 := by
    simp [gomesSSHCarrier,dotProduct,Fin.sum_univ_three]
  rw [horth,zero_smul,sub_zero]

/-- The existing noncommutative qubit Hamiltonian occupies the XZ carrier plane. -/
theorem gomesQubitHamiltonian_carrier (b t : ℝ) :
    gomesPauliCarrier ![b,0,t] = qubitHamiltonian b t := by
  simp [gomesPauliCarrier,qubitHamiltonian,add_comm]

/-- Its spectral radius supplies the same squared carrier norm without positivity premises. -/
theorem gomesQubitHamiltonian_carrier_norm (b t : ℝ) :
    (![b,0,t] : Fin 3 → ℝ) ⬝ᵥ ![b,0,t] = qubitRadius b t ^ (2 : ℕ) := by
  rw [qubitRadius,Real.sq_sqrt (add_nonneg (sq_nonneg t) (sq_nonneg b))]
  simp [dotProduct,Fin.sum_univ_three]
  ring

/-- The actual qubit Hamiltonian has the same exact Gram-kernel/stabilizer correspondence. -/
theorem gomesQubitHamiltonian_mass_kernel (b t : ℝ) (x : Fin 3 → ℝ) :
    gomesPauliAdjointMass ![b,0,t] *ᵥ x = 0 ↔
      qubitHamiltonian b t * gomesPauliCarrier x = gomesPauliCarrier x * qubitHamiltonian b t := by
  rw [gomesPauliAdjointMass_kernel_iff_commutes,gomesQubitHamiltonian_carrier]

/-- The exact mass characteristic determinant is controlled by the existing qubit radius. -/
theorem gomesQubitHamiltonian_mass_characteristic (b t mu : ℝ) :
    Matrix.det (mu • (1 : Matrix (Fin 3) (Fin 3) ℝ) - gomesPauliAdjointMass ![b,0,t]) =
      mu * (mu - qubitRadius b t ^ (2 : ℕ))^(2 : ℕ) := by
  rw [gomesPauliAdjointMass_characteristic,gomesQubitHamiltonian_carrier_norm]

/-- Full infinitesimal qubit symmetry returns exactly when both Hamiltonian coordinates vanish. -/
theorem gomesQubitHamiltonian_full_stabilizer (b t : ℝ) :
    (∀ x : Fin 3 → ℝ, qubitHamiltonian b t * gomesPauliCarrier x =
      gomesPauliCarrier x * qubitHamiltonian b t) ↔ b = 0 ∧ t = 0 := by
  rw [← gomesQubitHamiltonian_carrier,gomesPauliCarrier_full_stabilizer]
  simp

/-- The missing Y-axis is an explicit transverse mass mode of the XZ-plane Hamiltonian. -/
theorem gomesQubitHamiltonian_mass_transverse (b t : ℝ) :
    gomesPauliAdjointMass ![b,0,t] *ᵥ ![0,1,0] =
      qubitRadius b t ^ (2 : ℕ) • ![0,1,0] := by
  rw [gomesPauliAdjointMass_mulVec,gomesQubitHamiltonian_carrier_norm]
  have horth : (![b,0,t] : Fin 3 → ℝ) ⬝ᵥ ![0,1,0] = 0 := by
    simp [dotProduct,Fin.sum_univ_three]
  rw [horth,zero_smul,sub_zero]

end GaloisForLFunctions.HTGeometry
