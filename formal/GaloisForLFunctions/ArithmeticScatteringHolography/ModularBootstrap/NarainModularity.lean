import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainTriality
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinLineInvariance

/-!
# Modular invariance of the actual Narain partition

Poisson inversion and integer-spin translation give invariance under the
standard generators. Subgroup closure extends these identities to every
element of the modular group.
-/

open Complex RHTower Set UpperHalfPlane
open scoped MatrixGroups
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The actual Narain partition as a function on the upper half-plane. -/
def narainPartitionOnUpperHalfPlane (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (τ : UpperHalfPlane) : ℂ := narainPartition ρ σ τ.re τ.im

theorem narainPartitionOnUpperHalfPlane_S (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (τ : UpperHalfPlane) :
    narainPartitionOnUpperHalfPlane ρ σ (ModularGroup.S • τ) =
      narainPartitionOnUpperHalfPlane ρ σ τ := by
  simpa only [narainPartitionOnUpperHalfPlane, modular_S_smul_re,
    modular_S_smul_im, d4BMEisensteinInvertCoordinate] using
    narainPartition_worldsheetInversion ρ σ ⟨τ.re, τ.im, τ.im_pos⟩

theorem narainPartitionOnUpperHalfPlane_T (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (τ : UpperHalfPlane) :
    narainPartitionOnUpperHalfPlane ρ σ (ModularGroup.T • τ) =
      narainPartitionOnUpperHalfPlane ρ σ τ := by
  simpa only [narainPartitionOnUpperHalfPlane, ModularGroup.re_T_smul,
    ModularGroup.im_T_smul] using narainPartition_add_one ρ σ τ.re τ.im

/-- Poisson triality and integer spin give invariance under the full modular group. -/
theorem narainPartitionOnUpperHalfPlane_modular (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    narainPartitionOnUpperHalfPlane ρ σ (γ • τ) = narainPartitionOnUpperHalfPlane ρ σ τ := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  induction hγ using Subgroup.closure_induction generalizing τ with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact narainPartitionOnUpperHalfPlane_S ρ σ τ
    · exact narainPartitionOnUpperHalfPlane_T ρ σ τ
  | one => rw [one_smul]
  | mul x y _ _ hx hy => rw [mul_smul, hx, hy]
  | inv x _ hx =>
    have h := hx (x⁻¹ • τ)
    rw [smul_inv_smul] at h
    exact h.symm

#print axioms narainPartitionOnUpperHalfPlane_modular
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
