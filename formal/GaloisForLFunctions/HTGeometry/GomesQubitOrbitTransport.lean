import GaloisForLFunctions.HTGeometry.GomesQubitGibbsClosure
import GaloisForLFunctions.HTGeometry.GomesQuantumFrameTransport

/-!
# Y-frame transport of the literal all-real qubit Gibbs family

Applies the associated internal-frame transport law of Gomes, arXiv:2404.10461,
Section 4.2, to the existing qubit Hamiltonian, log-density, normalized density,
and adjoint Gram. Coupling and bias rotate together; radius and free energy
are invariant. The all-real Gibbs infrastructure includes every orbit point.

The tensor-reconstruction question of arXiv:2607.24901 has different exact answers
for these carriers: the full Gibbs state retains both signed parameters, whereas
the adjoint Gram construction of arXiv:2509.25276v7 retains only their simultaneous
sign class. The actual Y-gate stabilizer of the Gibbs state is classified as well.
-/

set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Coupling coordinate in the internal frame induced by the existing Y gate. -/
def gomesQubitOrbitCoupling (b t theta : ℝ) : ℝ := Real.cos theta*b+Real.sin theta*t

/-- Bias coordinate in the same internal frame. -/
def gomesQubitOrbitBias (b t theta : ℝ) : ℝ := -Real.sin theta*b+Real.cos theta*t

/-- The actual two-parameter Hamiltonian plane is invariant under the Y-frame action. -/
theorem gomesQubitOrbit_carrier (b t theta : ℝ) :
    ![gomesQubitOrbitCoupling b t theta,0,gomesQubitOrbitBias b t theta] =
      gomesYFrameMatrix theta *ᵥ ![b,0,t] := by
  ext i
  fin_cases i <;> simp [gomesQubitOrbitCoupling,gomesQubitOrbitBias,gomesYFrameMatrix,mul_comm]

/-- Internal-frame transport preserves the actual qubit radius at every point. -/
theorem gomesQubitOrbit_radius (b t theta : ℝ) :
    qubitRadius (gomesQubitOrbitCoupling b t theta) (gomesQubitOrbitBias b t theta) = qubitRadius b t := by
  unfold qubitRadius
  congr 1
  dsimp [gomesQubitOrbitCoupling,gomesQubitOrbitBias]
  linear_combination (b^2+t^2)*(Real.sin_sq_add_cos_sq theta)

/-- The existing Y gate transports the actual Hamiltonian through the complete parameter plane. -/
theorem gomesQubitOrbit_hamiltonian (b t theta : ℝ) :
    QuantumAlg.rotYOp theta * qubitHamiltonian b t * (QuantumAlg.rotYOp theta)ᴴ =
      qubitHamiltonian (gomesQubitOrbitCoupling b t theta) (gomesQubitOrbitBias b t theta) := by
  rw [← gomesQubitHamiltonian_carrier,gomesRotY_pauli_transport,← gomesQubitOrbit_carrier,
    gomesQubitHamiltonian_carrier]

/-- The partition free energy is a scalar associated invariant of the internal frame. -/
theorem gomesQubitOrbit_freeEnergy (b t theta : ℝ) :
    qubitFreeEnergy (gomesQubitOrbitCoupling b t theta) (gomesQubitOrbitBias b t theta) =
      qubitFreeEnergy b t := by
  simp only [qubitFreeEnergy,gomesQubitOrbit_radius]

/-- The full log-density transports by the actual gate, including the scalar normalizer. -/
theorem gomesQubitOrbit_logDensity (b t theta : ℝ) :
    QuantumAlg.rotYOp theta * qubitLogDensity b t * (QuantumAlg.rotYOp theta)ᴴ =
      qubitLogDensity (gomesQubitOrbitCoupling b t theta) (gomesQubitOrbitBias b t theta) := by
  have hU : QuantumAlg.rotYOp theta * (QuantumAlg.rotYOp theta)ᴴ =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    (Matrix.mem_unitaryGroup_iff).mp (QuantumAlg.rotYOp_mem_unitaryGroup theta)
  simp only [qubitLogDensity,gomesQubitOrbit_freeEnergy,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
  rw [hU,gomesQubitOrbit_hamiltonian b t theta]

/-- The normalized Gibbs state is transported by the actual gate over the whole orbit. -/
theorem gomesQubitOrbit_density (b t theta : ℝ) :
    QuantumAlg.rotYOp theta * qubitDensity b t * (QuantumAlg.rotYOp theta)ᴴ =
      qubitDensity (gomesQubitOrbitCoupling b t theta) (gomesQubitOrbitBias b t theta) := by
  have hU : QuantumAlg.rotYOp theta * (QuantumAlg.rotYOp theta)ᴴ =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    (Matrix.mem_unitaryGroup_iff).mp (QuantumAlg.rotYOp_mem_unitaryGroup theta)
  rw [gomesQubitDensity_closed,gomesQubitDensity_closed,gomesQubitOrbit_radius]
  simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_one]
  rw [hU,gomesQubitOrbit_hamiltonian b t theta]

/-- The qubit's adjoint Gram is an associated tensor under the same Y transport. -/
theorem gomesQubitOrbit_mass (b t theta : ℝ) :
    gomesPauliAdjointMass ![gomesQubitOrbitCoupling b t theta,0,gomesQubitOrbitBias b t theta] =
      gomesYFrameMatrix theta * gomesPauliAdjointMass ![b,0,t] * (gomesYFrameMatrix theta)ᵀ := by
  rw [gomesQubitOrbit_carrier,gomesYFrame_mass_transport]

/-- The massless directions transport with the physical qubit's internal frame. -/
theorem gomesQubitOrbit_kernel (b t theta : ℝ) (x : Fin 3 → ℝ) :
    gomesPauliAdjointMass ![gomesQubitOrbitCoupling b t theta,0,gomesQubitOrbitBias b t theta] *ᵥ
      (gomesYFrameMatrix theta *ᵥ x) = 0 ↔ gomesPauliAdjointMass ![b,0,t] *ᵥ x = 0 := by
  rw [gomesQubitOrbit_carrier,gomesYFrame_kernel_transport]

/-- The full Gibbs state retains both signed Hamiltonian coordinates. -/
theorem gomesQubitDensity_reconstruction (b t c s : ℝ) :
    qubitDensity b t = qubitDensity c s ↔ b = c ∧ t = s := by
  constructor
  · intro h
    have hl := congrArg CFC.log h
    rw [cfcLog_qubitDensity,cfcLog_qubitDensity] at hl
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 1).re) hl
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 0).re) hl
    have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hl
    simp [qubitLogDensity,qubitHamiltonian,QuantumAlg.pauliX,QuantumAlg.pauliZ] at h01 h00 h11
    exact ⟨h01,by linarith⟩
  · rintro ⟨rfl,rfl⟩
    rfl

/-- The qubit orbit Gram retains only the simultaneous-sign class of its parameters. -/
theorem gomesQubitMass_reconstruction (b t c s : ℝ) :
    gomesPauliAdjointMass ![b,0,t] = gomesPauliAdjointMass ![c,0,s] ↔
      (b = c ∧ t = s) ∨ (b = -c ∧ t = -s) := by
  rw [gomesPauliAdjointMass_reconstruction]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨congrFun h 0,congrFun h 2⟩
    · exact Or.inr ⟨congrFun h 0,congrFun h 2⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact Or.inl rfl
    · right
      ext i
      fin_cases i <;> simp

/-- Gibbs-state stabilizers under Y gates are exactly the carrier's fixed parameters. -/
theorem gomesQubitOrbit_density_stabilizer (b t theta : ℝ) :
    QuantumAlg.rotYOp theta * qubitDensity b t * (QuantumAlg.rotYOp theta)ᴴ = qubitDensity b t ↔
      (b = 0 ∧ t = 0) ∨ (Real.cos theta = 1 ∧ Real.sin theta = 0) := by
  rw [gomesQubitOrbit_density,gomesQubitDensity_reconstruction]
  constructor
  · rintro ⟨hb,ht⟩
    dsimp [gomesQubitOrbitCoupling,gomesQubitOrbitBias] at hb ht
    have hp : (Real.cos theta-1)*(b^2+t^2) = 0 := by
      linear_combination b*hb+t*ht
    rcases mul_eq_zero.mp hp with hc | hz
    · right
      have hc' : Real.cos theta = 1 := by linarith
      exact ⟨hc',by nlinarith [Real.sin_sq_add_cos_sq theta]⟩
    · left
      constructor <;> nlinarith [sq_nonneg b,sq_nonneg t]
  · rintro (⟨rfl,rfl⟩ | ⟨hc,hs⟩) <;>
      simp [gomesQubitOrbitCoupling,gomesQubitOrbitBias, *]

end GaloisForLFunctions.HTGeometry
