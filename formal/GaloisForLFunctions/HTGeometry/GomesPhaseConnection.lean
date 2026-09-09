import GaloisForLFunctions.HTGeometry.GomesQuantumFrameTransport
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The connection induced by quantum phase-frame transport

Applies the fundamental-vector-field and associated-connection laws of Gomes,
arXiv:2404.10461, Section 4.2 and Appendix A, to the existing quantum phase gate.
The actual frame differentiates to its skew generator. Matter vectors solve
`v' = J v`; their Pauli Gram tensors solve `M' = J M - M J`.
Both are parallel for the corresponding induced connections, and the tensor's
action on a transported vector remains parallel. No initial-vector or
nondegeneracy condition is imposed.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Matrix Matrix.Norms.Elementwise
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Infinitesimal generator of the phase gate's associated real frame. -/
def gomesPhaseGenerator : Matrix (Fin 3) (Fin 3) ℝ := !![0,-1,0;1,0,0;0,0,0]

/-- The phase generator belongs to the orthogonal Lie algebra. -/
theorem gomesPhaseGenerator_skew : gomesPhaseGeneratorᵀ = -gomesPhaseGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gomesPhaseGenerator]

/-- The generator is the fundamental vector field of rotation about the Pauli Z axis. -/
theorem gomesPhaseGenerator_cross (r : Fin 3 → ℝ) :
    gomesPhaseGenerator *ᵥ r = ![0,0,1] ⨯₃ r := by
  ext i
  fin_cases i <;> simp [gomesPhaseGenerator,Matrix.mulVec,dotProduct,
    Fin.sum_univ_three,crossProduct]

/-- Differentiating the actual associated phase frame reproduces its vertical generator. -/
theorem gomesPhaseFrame_hasDerivAt (theta : ℝ) :
    HasDerivAt gomesPhaseFrameMatrix (gomesPhaseGenerator * gomesPhaseFrameMatrix theta) theta := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [gomesPhaseFrameMatrix,gomesPhaseGenerator,Matrix.mul_apply,Fin.sum_univ_three]
  all_goals first | exact Real.hasDerivAt_cos theta | exact Real.hasDerivAt_sin theta |
    exact (Real.hasDerivAt_sin theta).neg | exact hasDerivAt_const theta (0 : ℝ) | exact hasDerivAt_const theta (1 : ℝ)

/-- A transported matter vector solves the connection equation with no initial-vector restriction. -/
theorem gomesPhaseFrame_vector_hasDerivAt (theta : ℝ) (r : Fin 3 → ℝ) :
    HasDerivAt (fun t => gomesPhaseFrameMatrix t *ᵥ r)
      (gomesPhaseGenerator *ᵥ (gomesPhaseFrameMatrix theta *ᵥ r)) theta := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [gomesPhaseFrameMatrix,gomesPhaseGenerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_three,neg_add_rev,sub_eq_add_neg,add_comm,Pi.add_def,Pi.sub_def,Pi.neg_def] using
      ((Real.hasDerivAt_cos theta).mul_const (r 0)).sub
        ((Real.hasDerivAt_sin theta).mul_const (r 1))
  · simpa [gomesPhaseFrameMatrix,gomesPhaseGenerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_three,sub_eq_add_neg,Pi.add_def,Pi.neg_def] using
      ((Real.hasDerivAt_sin theta).mul_const (r 0)).add
        ((Real.hasDerivAt_cos theta).mul_const (r 1))
  · simpa [gomesPhaseFrameMatrix,gomesPhaseGenerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_three] using hasDerivAt_const theta (r 2)

/-- The infinitesimal action on the Pauli Gram tensor is a commutator. -/
theorem gomesPhaseGenerator_mass_commutator (r : Fin 3 → ℝ) :
    gomesPhaseGenerator * gomesPauliAdjointMass r - gomesPauliAdjointMass r * gomesPhaseGenerator =
      -Matrix.vecMulVec (gomesPhaseGenerator *ᵥ r) r -
        Matrix.vecMulVec r (gomesPhaseGenerator *ᵥ r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesPhaseGenerator,gomesPauliAdjointMass,Matrix.mul_apply,Matrix.mulVec,
      Matrix.vecMulVec,Matrix.vecMul,dotProduct,Fin.sum_univ_three]
  all_goals ring

/-- The associated Gram tensor solves the induced tensor connection equation. -/
theorem gomesPhaseFrame_mass_hasDerivAt (theta : ℝ) (r : Fin 3 → ℝ) :
    HasDerivAt (fun t => gomesPauliAdjointMass (gomesPhaseFrameMatrix t *ᵥ r))
      (gomesPhaseGenerator * gomesPauliAdjointMass (gomesPhaseFrameMatrix theta *ᵥ r) -
        gomesPauliAdjointMass (gomesPhaseFrameMatrix theta *ᵥ r) * gomesPhaseGenerator) theta := by
  rw [gomesPhaseGenerator_mass_commutator]
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hr := hasDerivAt_pi.mp (gomesPhaseFrame_vector_hasDerivAt theta r)
  have hn (t : ℝ) : (gomesPhaseFrameMatrix t *ᵥ r) ⬝ᵥ (gomesPhaseFrameMatrix t *ᵥ r) = r ⬝ᵥ r :=
    gomesPauliFrame_dot (gomesPhaseFrameHom (Multiplicative.ofAdd t)) r r
  simpa [gomesPauliAdjointMass,hn,Matrix.vecMulVec,sub_eq_add_neg,add_comm,add_left_comm,add_assoc,Pi.add_def,Pi.sub_def,Pi.neg_def,Pi.mul_def]
    using (hasDerivAt_const theta ((r ⬝ᵥ r) * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)).sub
      ((hr i).mul (hr j))

/-- Covariant derivative on the phase-frame matter representation. -/
def gomesPhaseCovariantDerivative (v : ℝ → Fin 3 → ℝ) (theta : ℝ) : Fin 3 → ℝ :=
  deriv v theta - gomesPhaseGenerator *ᵥ v theta

/-- The induced covariant derivative on endomorphism-valued tensors. -/
def gomesPhaseTensorDerivative (A : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (theta : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  deriv A theta - (gomesPhaseGenerator * A theta - A theta * gomesPhaseGenerator)

/-- Every associated matter trajectory is parallel for the phase-frame connection. -/
theorem gomesPhaseFrame_vector_parallel (theta : ℝ) (r : Fin 3 → ℝ) :
    gomesPhaseCovariantDerivative (fun t => gomesPhaseFrameMatrix t *ᵥ r) theta = 0 := by
  rw [gomesPhaseCovariantDerivative,(gomesPhaseFrame_vector_hasDerivAt theta r).deriv,sub_self]

/-- The mass Gram tensor is parallel for the induced tensor connection. -/
theorem gomesPhaseFrame_mass_parallel (theta : ℝ) (r : Fin 3 → ℝ) :
    gomesPhaseTensorDerivative (fun t => gomesPauliAdjointMass (gomesPhaseFrameMatrix t *ᵥ r)) theta = 0 := by
  unfold gomesPhaseTensorDerivative
  apply sub_eq_zero.mpr
  exact (gomesPhaseFrame_mass_hasDerivAt theta r).deriv

/-- Transporting a Gram operator and a vector gives the transport of their original product. -/
theorem gomesPhaseFrame_mass_action (theta : ℝ) (r x : Fin 3 → ℝ) :
    gomesPauliAdjointMass (gomesPhaseFrameMatrix theta *ᵥ r) *ᵥ
      (gomesPhaseFrameMatrix theta *ᵥ x) =
        gomesPhaseFrameMatrix theta *ᵥ (gomesPauliAdjointMass r *ᵥ x) :=
  gomesPauliAdjointMass_frame_action (gomesPhaseFrameHom (Multiplicative.ofAdd theta)) r x

/-- Applying a parallel Gram tensor to a parallel vector gives a parallel matter vector. -/
theorem gomesPhaseFrame_mass_action_parallel (theta : ℝ) (r x : Fin 3 → ℝ) :
    gomesPhaseCovariantDerivative (fun t =>
      gomesPauliAdjointMass (gomesPhaseFrameMatrix t *ᵥ r) *ᵥ
        (gomesPhaseFrameMatrix t *ᵥ x)) theta = 0 := by
  simp only [gomesPhaseFrame_mass_action]
  exact gomesPhaseFrame_vector_parallel theta (gomesPauliAdjointMass r *ᵥ x)

end GaloisForLFunctions.HTGeometry
