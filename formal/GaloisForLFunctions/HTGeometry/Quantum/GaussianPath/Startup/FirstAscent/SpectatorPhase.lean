import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch
import GaloisForLFunctions.HTGeometry.UnitaryFlowSmoothing
import GaloisForLFunctions.HTGeometry.TensorConcatenation
import GaloisForLFunctions.HTGeometry.Quantum.DisjointSiteCircuitApproximation

/-! # Restricting a circuit to one eigenstate of its support -/
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

private abbrev productState (x : EuclideanSpace ℂ I) (y : EuclideanSpace ℂ A) :=
  WithLp.toLp 2 (binaryTensorVec x.ofLp y.ofLp)

omit [DecidableEq I] [DecidableEq A] in
private theorem product_norm (x : EuclideanSpace ℂ I) (y : EuclideanSpace ℂ A) :
    ‖productState x y‖=‖x‖*‖y‖ := norm_tensorVec x y

private theorem tensor_action (V : Matrix I I ℂ) (C : Matrix A A ℂ) {z : ℂ}
    (x : I→ℂ) (y : A→ℂ) (he : C *ᵥ y=z • y) :
    (V ⊗ₖ (1 : Matrix A A ℂ)-(1 : Matrix I I ℂ) ⊗ₖ C) *ᵥ binaryTensorVec x y =
      binaryTensorVec ((V-z • 1) *ᵥ x) y := by
  rw [Matrix.sub_mulVec,kronecker_mulVec_binaryTensorVec,kronecker_mulVec_binaryTensorVec,
    Matrix.one_mulVec,Matrix.one_mulVec,he,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
  funext ⟨i,a⟩
  change (V *ᵥ x) i*y a - x i*(z*y a) = ((V *ᵥ x) i-z*x i)*y a
  ring

private theorem tensor_restriction (V : Matrix I I ℂ) (C : Matrix A A ℂ)
    {z : ℂ} {y : EuclideanSpace ℂ A} (hy : y≠0) (he : C *ᵥ y.ofLp=z • y.ofLp) :
    ‖V-z • 1‖ ≤ ‖V ⊗ₖ (1 : Matrix A A ℂ)-(1 : Matrix I I ℂ) ⊗ₖ C‖ := by
  let B := V ⊗ₖ (1 : Matrix A A ℂ)-(1 : Matrix I I ℂ) ⊗ₖ C
  let T := toEuclideanCLM (𝕜 := ℂ) (V-z • 1)
  change ‖T‖ ≤ ‖B‖
  apply T.opNorm_le_bound (norm_nonneg B)
  intro x
  have action : toEuclideanCLM (𝕜 := ℂ) B (productState x y)=productState (T x) y :=
    congrArg (WithLp.toLp 2) (tensor_action V C x.ofLp y.ofLp he)
  have h : ‖toEuclideanCLM (𝕜 := ℂ) B (productState x y)‖ ≤ ‖B‖*‖productState x y‖ :=
    (toEuclideanCLM (𝕜 := ℂ) B).le_opNorm (productState x y)
  rw [action,product_norm,product_norm,←mul_assoc] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hy)

/-- One eigenphase of a disjoint unitary approximates the entire other
factor at the same error. The phase works for every input on that factor. -/
theorem spectator_phase [Nonempty A] (V : Matrix I I ℂ) (C : unitary (Matrix A A ℂ)) :
    ∃ z : ℂ, ‖z‖=1 ∧
      ‖V-z • 1‖ ≤ ‖V ⊗ₖ (1 : Matrix A A ℂ)-(1 : Matrix I I ℂ) ⊗ₖ C.val‖ := by
  let Φ := toEuclideanCLM (n := A) (𝕜 := ℂ)
  have hC : Φ C.val ∈ unitary _ := by
    apply Unitary.mem_iff.mpr
    obtain ⟨hl,hr⟩ := Unitary.mem_iff.mp C.property
    constructor
    · rw [←map_star,←map_mul,hl,map_one]
    · rw [←map_star,←map_mul,hr,map_one]
  obtain ⟨y,z,hy,he,hz⟩ := exists_unimodular_eigenvector
    (Unitary.linearIsometryEquiv ⟨Φ C.val,hC⟩)
  refine ⟨z,hz,tensor_restriction V C.val hy ?_⟩
  exact congrArg (WithLp.ofLp : EuclideanSpace ℂ A → A→ℂ) he

#print axioms spectator_phase
end
end GaloisForLFunctions.HTGeometry.FirstAscent
