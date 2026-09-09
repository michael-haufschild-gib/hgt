import GaloisForLFunctions.HTGeometry.GomesPhaseConnection
import GaloisForLFunctions.HTGeometry.GomesTwoBandAdjointMass

/-!
# Internal-frame transport and reconstruction for the actual SSH carrier

Applies the associated-connection viewpoint of Gomes, arXiv:2404.10461,
Section 4.2 and Appendix A, to the corpus's SSH Bloch Hamiltonian. Its hopping
rotates in a negative phase frame, while its intracell term is fixed. The latter
is exactly the covariant-derivative source. Both the whole matter carrier and
its adjoint Gram tensor are parallel precisely on the zero-intracell locus.

Combining this with the tensor reconstruction problem of arXiv:2607.24901 and
the orbit Gram construction of arXiv:2509.25276v7 gives exact information-loss
classifications: one quarter-zone Gram snapshot reconstructs both hopping
coefficients up to simultaneous sign; the signed connection source removes
that ambiguity except on the pure-hopping locus. No parameter assumptions are used.
-/

set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.Elementwise
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The SSH carrier separates into a fixed intracell vector and phase-transported hopping. -/
theorem gomesSSHCarrier_frame_decomposition (u v theta : ℝ) :
    gomesSSHCarrier u v theta = ![u,0,0] + gomesPhaseFrameMatrix (-theta) *ᵥ ![v,0,0] := by
  ext i
  fin_cases i <;>
    simp [gomesSSHCarrier,coppoSSHOffDiagonal_re,coppoSSHOffDiagonal_im,
      gomesPhaseFrameMatrix]

/-- The actual SSH Bloch operator separates into a fixed term and a transported hopping operator. -/
theorem gomesSSHBloch_frame_decomposition (u v theta : ℝ) :
    coppoSSHBloch u v theta = (u : ℂ) • QuantumAlg.pauliX +
      QuantumAlg.phaseGateOp (-theta) * ((v : ℂ) • QuantumAlg.pauliX) *
        (QuantumAlg.phaseGateOp (-theta))ᴴ := by
  have hc : (v : ℂ) • QuantumAlg.pauliX = gomesPauliCarrier ![v,0,0] := by
    simp [gomesPauliCarrier]
  rw [hc,gomesPhaseGate_pauli_transport,← gomesSSHCarrier_matrix,gomesSSHCarrier_frame_decomposition]
  simp [gomesPauliCarrier,add_smul,add_assoc]

/-- The exact tangent to the actual Bloch carrier. -/
theorem gomesSSHCarrier_hasDerivAt (u v theta : ℝ) :
    HasDerivAt (gomesSSHCarrier u v) ![-v*Real.sin theta,-v*Real.cos theta,0] theta := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [gomesSSHCarrier,coppoSSHOffDiagonal_re,coppoSSHOffDiagonal_im,
      Pi.add_def,Pi.neg_def,mul_neg,neg_mul] using
      (hasDerivAt_const theta u).add ((Real.hasDerivAt_cos theta).const_mul v)
  · simpa [gomesSSHCarrier,coppoSSHOffDiagonal_re,coppoSSHOffDiagonal_im,
      Pi.neg_def,neg_mul] using ((Real.hasDerivAt_sin theta).const_mul v).neg
  · simpa [gomesSSHCarrier] using hasDerivAt_const theta (0 : ℝ)

/-- The connection selected by the SSH hopping's negative phase orientation. -/
def gomesSSHConnectionDerivative (v : ℝ → Fin 3 → ℝ) (theta : ℝ) : Fin 3 → ℝ :=
  deriv v theta + gomesPhaseGenerator *ᵥ v theta

/-- The fixed intracell term is exactly the source in the SSH connection equation. -/
theorem gomesSSHCarrier_connection_source (u v theta : ℝ) :
    gomesSSHConnectionDerivative (gomesSSHCarrier u v) theta = ![0,u,0] := by
  rw [gomesSSHConnectionDerivative,(gomesSSHCarrier_hasDerivAt u v theta).deriv]
  ext i
  fin_cases i <;>
    simp [gomesSSHCarrier,coppoSSHOffDiagonal_re,coppoSSHOffDiagonal_im,
      gomesPhaseGenerator]

/-- The whole carrier is parallel precisely when its fixed intracell coefficient vanishes. -/
theorem gomesSSHCarrier_parallel_iff (u v theta : ℝ) :
    gomesSSHConnectionDerivative (gomesSSHCarrier u v) theta = 0 ↔ u = 0 := by
  rw [gomesSSHCarrier_connection_source]
  constructor
  · intro h
    exact congrFun h 1
  · rintro rfl
    ext i
    fin_cases i <;> simp

/-- Differentiating the SSH Gram tensor retains both its norm and rank-one contributions. -/
theorem gomesSSHAdjointMass_hasDerivAt (u v theta : ℝ) :
    HasDerivAt (fun t => gomesPauliAdjointMass (gomesSSHCarrier u v t))
      ((-2*u*v*Real.sin theta) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
        Matrix.vecMulVec ![-v*Real.sin theta,-v*Real.cos theta,0] (gomesSSHCarrier u v theta) -
        Matrix.vecMulVec (gomesSSHCarrier u v theta) ![-v*Real.sin theta,-v*Real.cos theta,0]) theta := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hr := hasDerivAt_pi.mp (gomesSSHCarrier_hasDerivAt u v theta)
  have hn : HasDerivAt (coppoSSHGapSq u v) (-2*u*v*Real.sin theta) theta := by
    change HasDerivAt (fun t => u^2+v^2+2*u*v*Real.cos t) (-2*u*v*Real.sin theta) theta
    simpa [Pi.add_def,neg_mul,mul_neg,mul_assoc] using
      (hasDerivAt_const theta (u^2+v^2)).add
        ((Real.hasDerivAt_cos theta).const_mul (2*u*v))
  simpa [gomesPauliAdjointMass,gomesSSHCarrier_norm,Matrix.vecMulVec,
    Pi.sub_def,Pi.mul_def,Pi.add_def,Pi.neg_def,sub_eq_add_neg,add_assoc,add_left_comm,add_comm]
    using (hn.mul_const ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)).sub ((hr i).mul (hr j))

/-- Tensor connection induced by the SSH hopping frame. -/
def gomesSSHTensorDerivative (A : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (theta : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  deriv A theta + (gomesPhaseGenerator * A theta - A theta * gomesPhaseGenerator)

/-- The tensor connection source is the polarization of the fixed intracell source. -/
theorem gomesSSHAdjointMass_connection_source (u v theta : ℝ) :
    gomesSSHTensorDerivative (fun t => gomesPauliAdjointMass (gomesSSHCarrier u v t)) theta =
      (2*((gomesSSHCarrier u v theta) ⬝ᵥ ![0,u,0])) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
        Matrix.vecMulVec ![0,u,0] (gomesSSHCarrier u v theta) -
        Matrix.vecMulVec (gomesSSHCarrier u v theta) ![0,u,0] := by
  unfold gomesSSHTensorDerivative
  have hd := (gomesSSHAdjointMass_hasDerivAt u v theta).deriv
  rw [hd,gomesPhaseGenerator_mass_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesSSHCarrier,coppoSSHOffDiagonal_re,coppoSSHOffDiagonal_im,
      gomesPhaseGenerator,Matrix.mulVec,Matrix.vecMulVec,dotProduct,Fin.sum_univ_three] <;> ring

/-- No nonzero intracell term can make the full Gram tensor parallel around the whole zone. -/
theorem gomesSSHAdjointMass_parallel_iff (u v : ℝ) :
    (∀ theta, gomesSSHTensorDerivative
      (fun t => gomesPauliAdjointMass (gomesSSHCarrier u v t)) theta = 0) ↔ u = 0 := by
  simp only [gomesSSHAdjointMass_connection_source]
  constructor
  · intro h
    have h0 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 1) (h 0)
    have hp := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 1) (h Real.pi)
    simp [gomesSSHCarrier,coppoSSHOffDiagonal_re,coppoSSHOffDiagonal_im,
      Matrix.vecMulVec,dotProduct,Fin.sum_univ_three] at h0 hp
    rcases h0 with h0 | h0
    · rcases hp with hp | hp
      · linarith
      · exact hp
    · exact h0
  · rintro rfl theta
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec,dotProduct,Fin.sum_univ_three]

/-- On the exact parallel locus, the actual SSH Gram tensor is phase transport of one fixed tensor. -/
theorem gomesSSHAdjointMass_parallel_transport (v theta : ℝ) :
    gomesPauliAdjointMass (gomesSSHCarrier 0 v theta) =
      gomesPhaseFrameMatrix (-theta) * gomesPauliAdjointMass ![v,0,0] *
        (gomesPhaseFrameMatrix (-theta))ᵀ := by
  rw [gomesSSHCarrier_frame_decomposition]
  have hz : (![0,0,0] : Fin 3 → ℝ) = 0 := by ext i; fin_cases i <;> simp
  rw [hz,zero_add,gomesPhaseFrame_mass_transport]

/-- Simultaneous reversal of both SSH coefficients reverses the full carrier. -/
theorem gomesSSHCarrier_parameter_neg (u v theta : ℝ) :
    gomesSSHCarrier (-u) (-v) theta = -gomesSSHCarrier u v theta := by
  ext i
  fin_cases i <;>
    simp [gomesSSHCarrier,coppoSSHOffDiagonal_re,coppoSSHOffDiagonal_im,neg_add_rev,add_comm]

/-- One quarter-zone Gram snapshot reconstructs both SSH coefficients up to simultaneous sign. -/
theorem gomesSSHAdjointMass_reconstruction (u v a b : ℝ) :
    gomesPauliAdjointMass (gomesSSHCarrier u v (Real.pi/2)) =
      gomesPauliAdjointMass (gomesSSHCarrier a b (Real.pi/2)) ↔
        (u = a ∧ v = b) ∨ (u = -a ∧ v = -b) := by
  rw [gomesPauliAdjointMass_reconstruction]
  constructor
  · rintro (h | h)
    · left
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [gomesSSHCarrier,coppoSSHOffDiagonal_re,coppoSSHOffDiagonal_im] at h0 h1
      exact ⟨h0,h1⟩
    · right
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [gomesSSHCarrier,coppoSSHOffDiagonal_re,coppoSSHOffDiagonal_im] at h0 h1
      exact ⟨h0,by linarith⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (gomesSSHCarrier_parameter_neg a b (Real.pi/2))

/-- The complete SSH Gram family has exactly the same simultaneous-sign ambiguity. -/
theorem gomesSSHAdjointMass_family_reconstruction (u v a b : ℝ) :
    (∀ theta, gomesPauliAdjointMass (gomesSSHCarrier u v theta) =
      gomesPauliAdjointMass (gomesSSHCarrier a b theta)) ↔
        (u = a ∧ v = b) ∨ (u = -a ∧ v = -b) := by
  constructor
  · intro h
    exact (gomesSSHAdjointMass_reconstruction u v a b).mp (h (Real.pi/2))
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) theta
    · rfl
    · rw [gomesSSHCarrier_parameter_neg,gomesPauliAdjointMass_neg]

/-- The signed connection source removes the Gram ambiguity except on the pure-hopping locus. -/
theorem gomesSSHAdjointMass_connection_reconstruction (u v a b : ℝ) :
    (gomesPauliAdjointMass (gomesSSHCarrier u v (Real.pi/2)) =
        gomesPauliAdjointMass (gomesSSHCarrier a b (Real.pi/2)) ∧
      gomesSSHConnectionDerivative (gomesSSHCarrier u v) 0 =
        gomesSSHConnectionDerivative (gomesSSHCarrier a b) 0) ↔
      (u = a ∧ v = b) ∨ (u = 0 ∧ a = 0 ∧ v = -b) := by
  have hs : (![0,u,0] : Fin 3 → ℝ) = ![0,a,0] ↔ u = a := by
    constructor
    · intro h
      exact congrFun h 1
    · rintro rfl
      rfl
  rw [gomesSSHAdjointMass_reconstruction,gomesSSHCarrier_connection_source,
    gomesSSHCarrier_connection_source,hs]
  constructor
  · rintro ⟨h,hua⟩
    rcases h with h | ⟨hn,hv⟩
    · exact Or.inl h
    · exact Or.inr ⟨by linarith,by linarith,hv⟩
  · rintro (⟨hu,hv⟩ | ⟨hu,ha,hv⟩)
    · exact ⟨Or.inl ⟨hu,hv⟩,hu⟩
    · exact ⟨Or.inr ⟨by rw [hu,ha,neg_zero],hv⟩,by rw [hu,ha]⟩

end GaloisForLFunctions.HTGeometry
