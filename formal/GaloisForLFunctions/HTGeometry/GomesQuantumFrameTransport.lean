import GaloisForLFunctions.HTGeometry.GomesPauliFrameCovariance
import GaloisForLFunctions.QuantumAlg.Core.Components.Gates

/-!
# Associated internal frames of existing quantum gates

Applies the associated-fiber transport law of Gomes, arXiv:2404.10461,
Section 4.2, to the corpus's phase, zero-branch phase, processing Z, and Y gates.
Their adjoint actions are explicit oriented real frames. The Pauli Gram tensor
and its kernel transport through those frames, as suggested by the mass/stabilizer
construction in arXiv:2509.25276v7. All identities hold for every real gate parameter.
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The oriented internal frame induced by the corpus's one-branch quantum phase gate. -/
def gomesPhaseFrameMatrix (theta : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos theta,-Real.sin theta,0;Real.sin theta,Real.cos theta,0;0,0,1]

/-- The induced coefficient frame is orthogonal for every phase. -/
theorem gomesPhaseFrameMatrix_orthogonal (theta : ℝ) :
    gomesPhaseFrameMatrix theta ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesPhaseFrameMatrix,Matrix.mul_apply,Fin.sum_univ_three] <;>
    nlinarith [Real.sin_sq_add_cos_sq theta]

/-- The phase gate preserves the orientation of the Pauli bracket frame. -/
theorem gomesPhaseFrameMatrix_det (theta : ℝ) : Matrix.det (gomesPhaseFrameMatrix theta) = 1 := by
  simp [gomesPhaseFrameMatrix,Matrix.det_fin_three]
  nlinarith [Real.sin_sq_add_cos_sq theta]

/-- The induced associated-frame transports compose by phase addition. -/
theorem gomesPhaseFrameMatrix_add (theta phi : ℝ) :
    gomesPhaseFrameMatrix (theta+phi) = gomesPhaseFrameMatrix theta * gomesPhaseFrameMatrix phi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesPhaseFrameMatrix,Matrix.mul_apply,Fin.sum_univ_three,Real.cos_add,Real.sin_add] <;>
    ring

/-- The zero phase induces the identity internal frame. -/
theorem gomesPhaseFrameMatrix_zero : gomesPhaseFrameMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gomesPhaseFrameMatrix]

/-- Phase reversal is transpose/inverse frame transport. -/
theorem gomesPhaseFrameMatrix_neg (theta : ℝ) :
    gomesPhaseFrameMatrix (-theta) = (gomesPhaseFrameMatrix theta)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gomesPhaseFrameMatrix]

/-- The genuine associated-frame representation into the orthogonal group. -/
def gomesPhaseFrameHom : Multiplicative ℝ →* Matrix.orthogonalGroup (Fin 3) ℝ where
  toFun t := ⟨gomesPhaseFrameMatrix t.toAdd,gomesPhaseFrameMatrix_orthogonal t.toAdd⟩
  map_one' := by
    apply Subtype.ext
    exact gomesPhaseFrameMatrix_zero
  map_mul' t u := by
    apply Subtype.ext
    exact gomesPhaseFrameMatrix_add t.toAdd u.toAdd

/-- The actual quantum phase gate acts on the Pauli carrier through the associated real frame. -/
theorem gomesPhaseGate_pauli_transport (theta : ℝ) (r : Fin 3 → ℝ) :
    QuantumAlg.phaseGateOp theta * gomesPauliCarrier r * (QuantumAlg.phaseGateOp theta)ᴴ =
      gomesPauliCarrier (gomesPhaseFrameMatrix theta *ᵥ r) := by
  have hs := Real.sin_sq_add_cos_sq theta
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [QuantumAlg.phaseGateOp,gomesPauliCarrier,gomesPhaseFrameMatrix,
      QuantumAlg.pauliX,QuantumAlg.pauliY,QuantumAlg.pauliZ,Complex.exp_ofReal_mul_I,
      Matrix.mulVec,Matrix.mul_apply,Matrix.conjTranspose_apply,dotProduct,Fin.sum_univ_two,Fin.sum_univ_three,-Complex.ofReal_cos,-Complex.ofReal_sin]
  all_goals first | (solve | ring) | linear_combination (r 2) * hs | linear_combination -(r 2) * hs

/-- Phasing the zero branch produces the opposite associated-frame rotation. -/
theorem gomesPhaseGateOnZero_pauli_transport (theta : ℝ) (r : Fin 3 → ℝ) :
    QuantumAlg.phaseGateOnZeroOp theta * gomesPauliCarrier r *
      (QuantumAlg.phaseGateOnZeroOp theta)ᴴ =
        gomesPauliCarrier (gomesPhaseFrameMatrix (-theta) *ᵥ r) := by
  have hs := Real.sin_sq_add_cos_sq theta
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [QuantumAlg.phaseGateOnZeroOp,gomesPauliCarrier,gomesPhaseFrameMatrix,
      QuantumAlg.pauliX,QuantumAlg.pauliY,QuantumAlg.pauliZ,Complex.exp_ofReal_mul_I,
      Matrix.mulVec,Matrix.mul_apply,Matrix.conjTranspose_apply,dotProduct,Fin.sum_univ_two,Fin.sum_univ_three,-Complex.ofReal_cos,-Complex.ofReal_sin]
  all_goals first | (solve | ring) | linear_combination (r 2) * hs

/-- The processing Z gate induces twice the opposite phase on the adjoint frame. -/
theorem gomesRotZ_pauli_transport (theta : ℝ) (r : Fin 3 → ℝ) :
    QuantumAlg.rotZOp theta * gomesPauliCarrier r * (QuantumAlg.rotZOp theta)ᴴ =
      gomesPauliCarrier (gomesPhaseFrameMatrix (-2*theta) *ᵥ r) := by
  have hs := Real.sin_sq_add_cos_sq theta
  have hn : Complex.exp (-((theta : ℂ) * Complex.I)) =
      (Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I := by
    simpa only [Complex.ofReal_neg,neg_mul,Real.cos_neg,Real.sin_neg,sub_eq_add_neg]
      using Complex.exp_ofReal_mul_I (-theta)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [QuantumAlg.rotZOp,gomesPauliCarrier,gomesPhaseFrameMatrix,
      QuantumAlg.pauliX,QuantumAlg.pauliY,QuantumAlg.pauliZ,hn,Complex.exp_ofReal_mul_I,
      show -2*theta = -(2*theta) by ring,Real.sin_two_mul,Real.cos_two_mul,pow_two,
      Matrix.mulVec,Matrix.mul_apply,Matrix.conjTranspose_apply,dotProduct,Fin.sum_univ_two,Fin.sum_univ_three,-Complex.ofReal_cos,-Complex.ofReal_sin]
  all_goals first | (solve | ring) | linear_combination (r 2) * hs | linear_combination -(r 2) * hs |
    linear_combination (r 0) * hs | linear_combination -(r 0) * hs |
    linear_combination (r 1) * hs | linear_combination -(r 1) * hs

/-- The actual phase-frame action transports the full Pauli Gram tensor. -/
theorem gomesPhaseFrame_mass_transport (theta : ℝ) (r : Fin 3 → ℝ) :
    gomesPauliAdjointMass (gomesPhaseFrameMatrix theta *ᵥ r) =
      gomesPhaseFrameMatrix theta * gomesPauliAdjointMass r * (gomesPhaseFrameMatrix theta)ᵀ :=
  gomesPauliAdjointMass_frame_covariance (gomesPhaseFrameHom (Multiplicative.ofAdd theta)) r

/-- The associated massless directions transport exactly with the quantum phase frame. -/
theorem gomesPhaseFrame_kernel_transport (theta : ℝ) (r x : Fin 3 → ℝ) :
    gomesPauliAdjointMass (gomesPhaseFrameMatrix theta *ᵥ r) *ᵥ
      (gomesPhaseFrameMatrix theta *ᵥ x) = 0 ↔ gomesPauliAdjointMass r *ᵥ x = 0 :=
  gomesPauliAdjointMass_frame_kernel (gomesPhaseFrameHom (Multiplicative.ofAdd theta)) r x

/-- The real internal frame induced by the corpus's Y rotation gate. -/
def gomesYFrameMatrix (theta : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos theta,0,Real.sin theta;0,1,0;-Real.sin theta,0,Real.cos theta]

/-- Every Y frame is an isometry of coefficient space. -/
theorem gomesYFrameMatrix_orthogonal (theta : ℝ) :
    gomesYFrameMatrix theta ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesYFrameMatrix,Matrix.mul_apply,Fin.sum_univ_three] <;>
    nlinarith [Real.sin_sq_add_cos_sq theta]

/-- The Y gate preserves the orientation of the internal frame. -/
theorem gomesYFrameMatrix_det (theta : ℝ) : Matrix.det (gomesYFrameMatrix theta) = 1 := by
  simp [gomesYFrameMatrix,Matrix.det_fin_three]
  nlinarith [Real.sin_sq_add_cos_sq theta]

/-- Y transports compose as rotations of the associated frame. -/
theorem gomesYFrameMatrix_add (theta phi : ℝ) :
    gomesYFrameMatrix (theta+phi) = gomesYFrameMatrix theta * gomesYFrameMatrix phi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesYFrameMatrix,Matrix.mul_apply,Fin.sum_univ_three,Real.cos_add,Real.sin_add] <;>
    ring

/-- The corpus's half-angle Y gate induces the full-angle real internal frame. -/
theorem gomesRotY_pauli_transport (theta : ℝ) (r : Fin 3 → ℝ) :
    QuantumAlg.rotYOp theta * gomesPauliCarrier r * (QuantumAlg.rotYOp theta)ᴴ =
      gomesPauliCarrier (gomesYFrameMatrix theta *ᵥ r) := by
  have hs := Real.sin_sq_add_cos_sq (theta/2)
  have hc : Real.cos theta = 2*Real.cos (theta/2)^2-1 := by
    simpa only [mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)]
      using Real.cos_two_mul (theta/2)
  have hh : Real.sin theta = 2*Real.sin (theta/2)*Real.cos (theta/2) := by
    simpa only [mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)]
      using Real.sin_two_mul (theta/2)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [QuantumAlg.rotYOp,gomesPauliCarrier,gomesYFrameMatrix,
      QuantumAlg.pauliX,QuantumAlg.pauliY,QuantumAlg.pauliZ,
      Matrix.mulVec,Matrix.mul_apply,Matrix.conjTranspose_apply,dotProduct,
      Fin.sum_univ_two,Fin.sum_univ_three,hc,hh,pow_two,-Complex.ofReal_cos,-Complex.ofReal_sin]
  all_goals first | (solve | ring) | linear_combination (r 2)*hs |
    linear_combination -(r 2)*hs | linear_combination (r 0)*hs |
    linear_combination -(r 0)*hs | linear_combination (r 1)*hs |
    linear_combination -(r 1)*hs

/-- Y gates carry the same exact associated Gram-tensor transport law. -/
theorem gomesYFrame_mass_transport (theta : ℝ) (r : Fin 3 → ℝ) :
    gomesPauliAdjointMass (gomesYFrameMatrix theta *ᵥ r) =
      gomesYFrameMatrix theta * gomesPauliAdjointMass r * (gomesYFrameMatrix theta)ᵀ :=
  gomesPauliAdjointMass_frame_covariance ⟨_,gomesYFrameMatrix_orthogonal theta⟩ r

/-- The Y gate's real frame transports every massless direction, in both directions. -/
theorem gomesYFrame_kernel_transport (theta : ℝ) (r x : Fin 3 → ℝ) :
    gomesPauliAdjointMass (gomesYFrameMatrix theta *ᵥ r) *ᵥ
      (gomesYFrameMatrix theta *ᵥ x) = 0 ↔ gomesPauliAdjointMass r *ᵥ x = 0 :=
  gomesPauliAdjointMass_frame_kernel ⟨_,gomesYFrameMatrix_orthogonal theta⟩ r x

end GaloisForLFunctions.HTGeometry
