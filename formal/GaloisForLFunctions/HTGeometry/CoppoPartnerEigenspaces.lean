import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage
import GaloisForLFunctions.HTGeometry.SuperPoincareBlockFactorization
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Supersymmetric pairing of positive-energy eigenspaces

The pairing argument in arXiv:2405.03454, Supplement IV, applies to every
factorization, including rectangular ones. The inverse is the opposite factor
divided by energy. A positive exponential energy discharges nonvanishing internally.
-/

noncomputable section
namespace HTGeometry

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Positive-energy eigenspaces of the two partner factorizations are canonically equivalent. -/
def coppoPositiveEnergyPartnerEquiv (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (e : ℝ) :
    Module.End.eigenspace (B.comp A) (Real.exp e : ℂ) ≃ₗ[ℂ]
      Module.End.eigenspace (A.comp B) (Real.exp e : ℂ) where
  toFun x := ⟨A x, by
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    apply Module.End.mem_eigenspace_iff.mpr
    change A (B (A x)) = (Real.exp e : ℂ) • A x
    simpa only [LinearMap.comp_apply, map_smul] using congrArg A hx⟩
  invFun y := ⟨(Real.exp e : ℂ)⁻¹ • B y, by
    have hy := Module.End.mem_eigenspace_iff.mp y.property
    apply Module.End.mem_eigenspace_iff.mpr
    change B (A ((Real.exp e : ℂ)⁻¹ • B y)) =
      (Real.exp e : ℂ) • ((Real.exp e : ℂ)⁻¹ • B y)
    simp only [LinearMap.comp_apply] at hy
    rw [map_smul, map_smul, hy, map_smul]
    simp only [smul_smul, mul_comm]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    change (Real.exp e : ℂ)⁻¹ • B (A x) = (x : V)
    rw [show B (A x) = (Real.exp e : ℂ) • x from hx, smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero e)), one_smul]
  right_inv y := by
    apply Subtype.ext
    have hy := Module.End.mem_eigenspace_iff.mp y.property
    change A ((Real.exp e : ℂ)⁻¹ • B y) = (y : W)
    rw [map_smul, show A (B y) = (Real.exp e : ℂ) • y from hy, smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero e)), one_smul]
  map_add' x y := by apply Subtype.ext; exact A.map_add _ _
  map_smul' c x := by apply Subtype.ext; exact A.map_smul c _

/-- The forward spectral pairing is exactly the first factor. -/
theorem coppoPositiveEnergyPartnerEquiv_apply (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (e : ℝ)
    (x : Module.End.eigenspace (B.comp A) (Real.exp e : ℂ)) :
    (coppoPositiveEnergyPartnerEquiv A B e x : W) = A x := rfl

/-- The inverse pairing includes the necessary energy denominator. -/
theorem coppoPositiveEnergyPartnerEquiv_symm_apply (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (e : ℝ)
    (y : Module.End.eigenspace (A.comp B) (Real.exp e : ℂ)) :
    ((coppoPositiveEnergyPartnerEquiv A B e).symm y : V) = (Real.exp e : ℂ)⁻¹ • B y := rfl

/-- Partner multiplicities agree at every constructed positive energy. -/
theorem coppoPositiveEnergyPartner_finrank (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (e : ℝ) :
    Module.finrank ℂ (Module.End.eigenspace (B.comp A) (Real.exp e : ℂ)) =
      Module.finrank ℂ (Module.End.eigenspace (A.comp B) (Real.exp e : ℂ)) :=
  (coppoPositiveEnergyPartnerEquiv A B e).finrank_eq

/-- The pairing preserves the existence of nonzero eigenvectors. -/
theorem coppoPositiveEnergyPartner_nontrivial (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (e : ℝ) :
    Nontrivial (Module.End.eigenspace (B.comp A) (Real.exp e : ℂ)) ↔
      Nontrivial (Module.End.eigenspace (A.comp B) (Real.exp e : ℂ)) :=
  (coppoPositiveEnergyPartnerEquiv A B e).toEquiv.nontrivial_congr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The corpus's bounded master constraints have paired positive-energy eigenspaces. -/
def coppoMasterConstraintPartnerEquiv (C : E →L[ℂ] E) (e : ℝ) :
    Module.End.eigenspace (quantumMasterConstraint C).toLinearMap (Real.exp e : ℂ) ≃ₗ[ℂ]
      Module.End.eigenspace (quantumMasterConstraint C.adjoint).toLinearMap (Real.exp e : ℂ) := by
  unfold quantumMasterConstraint
  rw [ContinuousLinearMap.adjoint_adjoint]
  exact coppoPositiveEnergyPartnerEquiv C.toLinearMap C.adjoint.toLinearMap e

/-- The two master-constraint Hamiltonians have exactly equal positive spectral multiplicities. -/
theorem coppoMasterConstraintPartner_finrank (C : E →L[ℂ] E) (e : ℝ) :
    Module.finrank ℂ (Module.End.eigenspace (quantumMasterConstraint C).toLinearMap (Real.exp e : ℂ)) =
      Module.finrank ℂ (Module.End.eigenspace (quantumMasterConstraint C.adjoint).toLinearMap
        (Real.exp e : ℂ)) :=
  (coppoMasterConstraintPartnerEquiv C e).finrank_eq

end HTGeometry
