import GaloisForLFunctions.HTGeometry.SchurComplementKernel

/-!
# QNMQuadraticPencil

The quadratic frequency residual in Ferrer-Sánchez et al., arXiv:2608.19774,
equation (3.5), admits an exact companion realization using the existing Schur block
operator. The kernel equivalence requires no inverse of the mass operator.
-/

namespace GaloisForLFunctions.HTGeometry
variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

def qnmQuadraticPencil (A B W : E →ₗ[R] E) (z : R) : E →ₗ[R] E :=
  A + z • B - z ^ (2 : ℕ) • W

def qnmCompanionLeft (A B : E →ₗ[R] E) : E × E →ₗ[R] E × E :=
  schurBlockOperator 0 LinearMap.id A B

def qnmCompanionMass (W : E →ₗ[R] E) : E × E →ₗ[R] E × E :=
  schurBlockOperator LinearMap.id 0 0 W

theorem qnmCompanion_residual (A B W : E →ₗ[R] E) (z : R) (x : E) :
    qnmCompanionLeft A B (x, z • x) - z • qnmCompanionMass W (x, z • x) =
      (0, qnmQuadraticPencil A B W z x) := by
  simp [qnmCompanionLeft, qnmCompanionMass, qnmQuadraticPencil,
    Prod.smul_mk, smul_smul, pow_two]

theorem qnmCompanion_eigen_iff (A B W : E →ₗ[R] E) (z : R) (p : E × E) :
    qnmCompanionLeft A B p = z • qnmCompanionMass W p ↔
      p.2 = z • p.1 ∧ qnmQuadraticPencil A B W z p.1 = 0 := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp [qnmCompanionLeft, qnmCompanionMass] at h1 h2
    refine ⟨h1, ?_⟩
    simp only [qnmQuadraticPencil, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply]
    rw [h1, map_smul, map_smul, smul_smul, ← pow_two] at h2
    exact sub_eq_zero.mpr h2
  · rintro ⟨h1, h2⟩
    have h := qnmCompanion_residual A B W z p.1
    rw [h2] at h
    have hp : (p.1, z • p.1) = p := Prod.ext rfl h1.symm
    rw [hp] at h
    exact sub_eq_zero.mp h

def qnmCompanionKernelEquiv (A B W : E →ₗ[R] E) (z : R) :
    LinearMap.ker (qnmQuadraticPencil A B W z) ≃ₗ[R]
      LinearMap.ker (qnmCompanionLeft A B - z • qnmCompanionMass W) where
  toFun x := ⟨(x.1, z • x.1), by
    change qnmCompanionLeft A B _ - z • qnmCompanionMass W _ = 0
    rw [qnmCompanion_residual]
    exact Prod.ext rfl x.property⟩
  invFun p := ⟨p.1.1, by
    have h : qnmCompanionLeft A B p.1 = z • qnmCompanionMass W p.1 :=
      sub_eq_zero.mp p.property
    exact ((qnmCompanion_eigen_iff A B W z p.1).mp h).2⟩
  left_inv x := rfl
  right_inv p := by
    apply Subtype.ext
    have h : qnmCompanionLeft A B p.1 = z • qnmCompanionMass W p.1 :=
      sub_eq_zero.mp p.property
    exact Prod.ext rfl ((qnmCompanion_eigen_iff A B W z p.1).mp h).1.symm
  map_add' x y := by ext <;> simp [smul_add]
  map_smul' c x := by ext <;> simp [smul_smul, mul_comm]

end GaloisForLFunctions.HTGeometry
