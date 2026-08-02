import GaloisForLFunctions.HTGeometry.IteratedHermitianObserverFamilyLeafExtension
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Physical realizations of observer spectral systems

The recursive spectral invariant is useful only if its eigenbasis and its
site probes remain tied to one physical tensor realization.  This file
packages that missing provenance and supplies the exact tensor-unitary
identities needed by a physical leaf extension.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix Kronecker BigOperators

universe u

/-- A physical realization of a packaged spectral system.  Columns of
`basis` are the spectral eigenvectors in the physical basis.  The two
unitarity identities are stated separately because physical and spectral
index types need not be definitionally equal. -/
structure GoodObserverSpectralSystem.PhysicalRealization
    (X : GoodObserverSpectralSystem.{u})
    [Fintype X.State] [DecidableEq X.State] where
  PhysicalState : Type u
  [physicalFintype : Fintype PhysicalState]
  [physicalDecidableEq : DecidableEq PhysicalState]
  basis : Matrix PhysicalState X.State ℂ
  star_basis_mul_basis :
    basisᴴ * basis = (1 : Matrix X.State X.State ℂ)
  basis_mul_star_basis :
    basis * basisᴴ =
      (1 : Matrix PhysicalState PhysicalState ℂ)
  hamiltonian : Matrix PhysicalState PhysicalState ℂ
  hamiltonian_eq_diagonal :
    hamiltonian =
      basis *
        Matrix.diagonal (fun i => (X.energy i : ℂ)) *
        basisᴴ
  physicalProbe :
    ∀ s, X.Probe s → Matrix PhysicalState PhysicalState ℂ
  transition_eq_coordinate :
    ∀ s q,
      X.transition s q =
        basisᴴ * physicalProbe s q * basis

/-- Tensor the physical-to-spectral eigenbasis with the identity on a newly
adjoined finite factor. -/
def tensorIdentityBasis
    {P I ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (U : Matrix P I ℂ) :
    Matrix (P × ρ) (I × ρ) ℂ :=
  U ⊗ₖ (1 : Matrix ρ ρ ℂ)

theorem conjTranspose_tensorIdentityBasis
    {P I ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (U : Matrix P I ℂ) :
    (tensorIdentityBasis (ρ := ρ) U)ᴴ =
      Uᴴ ⊗ₖ (1 : Matrix ρ ρ ℂ) := by
  rw [tensorIdentityBasis, Matrix.conjTranspose_kronecker]
  simp

/-- A rectangular unitary basis remains rectangular unitary after tensoring
with an identity factor. -/
theorem star_tensorIdentityBasis_mul_self
    {P I ρ : Type*}
    [Fintype P] [Fintype I] [Fintype ρ]
    [DecidableEq P] [DecidableEq I] [DecidableEq ρ]
    (U : Matrix P I ℂ)
    (hU : Uᴴ * U = (1 : Matrix I I ℂ)) :
    (tensorIdentityBasis (ρ := ρ) U)ᴴ *
        tensorIdentityBasis (ρ := ρ) U =
      (1 : Matrix (I × ρ) (I × ρ) ℂ) := by
  rw [conjTranspose_tensorIdentityBasis, tensorIdentityBasis,
    ← Matrix.mul_kronecker_mul, hU]
  simp

theorem tensorIdentityBasis_mul_star_self
    {P I ρ : Type*}
    [Fintype P] [Fintype I] [Fintype ρ]
    [DecidableEq P] [DecidableEq I] [DecidableEq ρ]
    (U : Matrix P I ℂ)
    (hU : U * Uᴴ = (1 : Matrix P P ℂ)) :
    tensorIdentityBasis (ρ := ρ) U *
        (tensorIdentityBasis (ρ := ρ) U)ᴴ =
      (1 : Matrix (P × ρ) (P × ρ) ℂ) := by
  rw [conjTranspose_tensorIdentityBasis, tensorIdentityBasis,
    ← Matrix.mul_kronecker_mul, hU]
  simp

/-- Real linear combinations commute with passage to exact spectral
coordinates.  This is the parent-site locality identity for the attachment
channel selected by the leaf theorem. -/
theorem realMatrixFamilyCombination_coordinate
    {P I η : Type*}
    [Fintype P] [Fintype I] [Fintype η]
    (U : Matrix P I ℂ)
    (physical : η → Matrix P P ℂ)
    (spectral : η → Matrix I I ℂ)
    (coefficient : η → ℝ)
    (hcoordinate :
      ∀ q, spectral q = Uᴴ * physical q * U) :
    realMatrixFamilyCombination spectral coefficient =
      Uᴴ *
        realMatrixFamilyCombination physical coefficient *
        U := by
  classical
  have hsum
      (family : η → Matrix P P ℂ) :
      realMatrixFamilyCombination family coefficient =
        ∑ q, (coefficient q : ℂ) • family q := by
    ext a b
    rw [realMatrixFamilyCombination_apply]
    symm
    calc
      (∑ q, (coefficient q : ℂ) • family q) a b =
          (∑ q, ((coefficient q : ℂ) • family q) a) b := by
        exact congrFun
          (Finset.sum_apply a Finset.univ
            (fun q => (coefficient q : ℂ) • family q)) b
      _ = ∑ q, ((coefficient q : ℂ) • family q) a b := by
        exact Finset.sum_apply b Finset.univ
          (fun q => ((coefficient q : ℂ) • family q) a)
      _ = _ := by simp
  have hsumSpectral :
      realMatrixFamilyCombination spectral coefficient =
        ∑ q, (coefficient q : ℂ) • spectral q := by
    ext a b
    rw [realMatrixFamilyCombination_apply]
    symm
    calc
      (∑ q, (coefficient q : ℂ) • spectral q) a b =
          (∑ q, ((coefficient q : ℂ) • spectral q) a) b := by
        exact congrFun
          (Finset.sum_apply a Finset.univ
            (fun q => (coefficient q : ℂ) • spectral q)) b
      _ = ∑ q, ((coefficient q : ℂ) • spectral q) a b := by
        exact Finset.sum_apply b Finset.univ
          (fun q => ((coefficient q : ℂ) • spectral q) a)
      _ = _ := by simp
  rw [hsumSpectral, hsum]
  simp_rw [hcoordinate]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp [Matrix.mul_smul, Matrix.smul_mul]

/-- Conjugating the spectral attachment back by a rectangular unitary
recovers the parent-site physical combination exactly. -/
theorem physicalCombination_eq_basis_mul_spectralCombination
    {P I η : Type*}
    [Fintype P] [Fintype I] [Fintype η]
    [DecidableEq P] [DecidableEq I]
    (U : Matrix P I ℂ)
    (physical : η → Matrix P P ℂ)
    (spectral : η → Matrix I I ℂ)
    (coefficient : η → ℝ)
    (hleft :
      U * Uᴴ = (1 : Matrix P P ℂ))
    (hcoordinate :
      ∀ q, spectral q = Uᴴ * physical q * U) :
    realMatrixFamilyCombination physical coefficient =
      U * realMatrixFamilyCombination spectral coefficient * Uᴴ := by
  rw [realMatrixFamilyCombination_coordinate
    U physical spectral coefficient hcoordinate]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uᴴ, hleft]
  simp

@[simp] theorem layerMatrixCoupling_eq_kronecker
    {P ρ : Type*}
    (A : Matrix P P ℂ) (B : Matrix ρ ρ ℂ) :
    layerMatrixCoupling A B = A ⊗ₖ B := by
  rfl

/-- One leaf is added by an onsite term and one two-factor interaction.
No dressed operator on the previous tensor factors is introduced. -/
def physicalLeafHamiltonian
    {P ρ : Type*} [DecidableEq P] [DecidableEq ρ]
    (oldHamiltonian parentOperator : Matrix P P ℂ)
    (shift : ρ → ℂ) (edge : Matrix ρ ρ ℂ) :
    Matrix (P × ρ) (P × ρ) ℂ :=
  layerMatrixCoupling oldHamiltonian
      (1 : Matrix ρ ρ ℂ) +
    layerMatrixCoupling
      (1 : Matrix P P ℂ) (Matrix.diagonal shift) +
    layerMatrixCoupling parentOperator edge

/-- The chart Hamiltonian is exactly the sum of the inherited Hamiltonian,
the new onsite term, and one parent--leaf interaction. -/
theorem localExtensionMatrix_eq_leafHamiltonian
    {I ρ : Type*} [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ) (edge : Matrix ρ ρ ℂ) :
    localExtensionMatrix energy shift attachment edge =
      physicalLeafHamiltonian
        (Matrix.diagonal energy) attachment shift edge := by
  ext x y
  simp only [localExtensionMatrix, physicalLeafHamiltonian,
    Matrix.add_apply, Matrix.diagonal_apply,
    layerMatrixCoupling, layeredEnergy]
  by_cases hxy : x = y
  · subst y
    simp
  · have hfirstOrSecond :
        x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
      contrapose! hxy
      exact Prod.ext hxy.1 hxy.2
    rcases hfirstOrSecond with hfirst | hsecond
    · simp [hxy, hfirst]
    · simp [hxy, hsecond]

/-- Exact spectral coordinates of the inherited physical Hamiltonian. -/
theorem GoodObserverSpectralSystem.PhysicalRealization.hamiltonian_coordinate
    {X : GoodObserverSpectralSystem.{u}}
    [Fintype X.State] [DecidableEq X.State]
    (R : X.PhysicalRealization) :
    letI : Fintype R.PhysicalState := R.physicalFintype
    letI : DecidableEq R.PhysicalState :=
      R.physicalDecidableEq
    R.basisᴴ * R.hamiltonian * R.basis =
      Matrix.diagonal (fun i => (X.energy i : ℂ)) := by
  letI : Fintype R.PhysicalState := R.physicalFintype
  letI : DecidableEq R.PhysicalState :=
    R.physicalDecidableEq
  rw [R.hamiltonian_eq_diagonal]
  calc
    R.basisᴴ *
          (R.basis *
            Matrix.diagonal (fun i => (X.energy i : ℂ)) *
            R.basisᴴ) *
          R.basis =
        (R.basisᴴ * R.basis) *
          Matrix.diagonal (fun i => (X.energy i : ℂ)) *
          (R.basisᴴ * R.basis) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal (fun i => (X.energy i : ℂ)) := by
      rw [R.star_basis_mul_basis]
      simp

/-- Tensor extension commutes exactly with spectral coordinate change. -/
theorem tensorIdentityBasis_coordinate_layer
    {P I ρ : Type*}
    [Fintype P] [Fintype I] [Fintype ρ]
    [DecidableEq P] [DecidableEq I] [DecidableEq ρ]
    (U : Matrix P I ℂ)
    (physical : Matrix P P ℂ)
    (spectral : Matrix I I ℂ)
    (edge : Matrix ρ ρ ℂ)
    (hcoordinate : Uᴴ * physical * U = spectral) :
    (tensorIdentityBasis (ρ := ρ) U)ᴴ *
        layerMatrixCoupling physical edge *
        tensorIdentityBasis (ρ := ρ) U =
      layerMatrixCoupling spectral edge := by
  rw [conjTranspose_tensorIdentityBasis, tensorIdentityBasis,
    layerMatrixCoupling_eq_kronecker,
    layerMatrixCoupling_eq_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul]
  rw [← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one, hcoordinate]

/-- Physical parent--leaf locality is invariant under the old spectral
basis change. -/
theorem tensorIdentityBasis_coordinate_physicalLeafHamiltonian
    {P I ρ : Type*}
    [Fintype P] [Fintype I] [Fintype ρ]
    [DecidableEq P] [DecidableEq I] [DecidableEq ρ]
    (U : Matrix P I ℂ)
    (oldHamiltonian parentOperator : Matrix P P ℂ)
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ) (edge : Matrix ρ ρ ℂ)
    (hU : Uᴴ * U = (1 : Matrix I I ℂ))
    (hHamiltonian :
      Uᴴ * oldHamiltonian * U = Matrix.diagonal energy)
    (hParent :
      Uᴴ * parentOperator * U = attachment) :
    (tensorIdentityBasis (ρ := ρ) U)ᴴ *
        physicalLeafHamiltonian
          oldHamiltonian parentOperator shift edge *
        tensorIdentityBasis (ρ := ρ) U =
      localExtensionMatrix energy shift attachment edge := by
  rw [localExtensionMatrix_eq_leafHamiltonian]
  simp only [physicalLeafHamiltonian, Matrix.mul_add,
    Matrix.add_mul]
  rw [tensorIdentityBasis_coordinate_layer
      U oldHamiltonian (Matrix.diagonal energy)
      (1 : Matrix ρ ρ ℂ) hHamiltonian]
  have hIdentity :
      Uᴴ * (1 : Matrix P P ℂ) * U =
        (1 : Matrix I I ℂ) := by
    simpa [Matrix.mul_assoc] using hU
  rw [tensorIdentityBasis_coordinate_layer
      U (1 : Matrix P P ℂ) (1 : Matrix I I ℂ)
      (Matrix.diagonal shift) hIdentity]
  rw [tensorIdentityBasis_coordinate_layer
      U parentOperator attachment edge hParent]

/-- Compose the tensorized old physical basis with the exact eigenbasis of
the spectral leaf Hamiltonian. -/
def physicalLeafSpectralBasis
    {P I ρ : Type*}
    [Fintype I] [Fintype ρ] [DecidableEq ρ]
    (U : Matrix P I ℂ)
    (V : Matrix (I × ρ) (I × ρ) ℂ) :
    Matrix (P × ρ) (I × ρ) ℂ :=
  tensorIdentityBasis (ρ := ρ) U * V

theorem conjTranspose_physicalLeafSpectralBasis
    {P I ρ : Type*}
    [Fintype I] [Fintype ρ] [DecidableEq ρ]
    (U : Matrix P I ℂ)
    (V : Matrix (I × ρ) (I × ρ) ℂ) :
    (physicalLeafSpectralBasis U V)ᴴ =
      Vᴴ * (tensorIdentityBasis (ρ := ρ) U)ᴴ := by
  rw [physicalLeafSpectralBasis, Matrix.conjTranspose_mul]

/-- Composition with a square unitary preserves the left rectangular
unitary identity. -/
theorem physicalLeafSpectralBasis_star_mul_self
    {P I ρ : Type*}
    [Fintype P] [Fintype I] [Fintype ρ]
    [DecidableEq P] [DecidableEq I] [DecidableEq ρ]
    (U : Matrix P I ℂ)
    (V : Matrix (I × ρ) (I × ρ) ℂ)
    (hU : Uᴴ * U = (1 : Matrix I I ℂ))
    (hV :
      Vᴴ * V =
        (1 : Matrix (I × ρ) (I × ρ) ℂ)) :
    (physicalLeafSpectralBasis U V)ᴴ *
        physicalLeafSpectralBasis U V =
      (1 : Matrix (I × ρ) (I × ρ) ℂ) := by
  rw [conjTranspose_physicalLeafSpectralBasis,
    physicalLeafSpectralBasis]
  simp only [Matrix.mul_assoc]
  calc
    Vᴴ *
          ((tensorIdentityBasis (ρ := ρ) U)ᴴ *
            (tensorIdentityBasis (ρ := ρ) U * V)) =
        Vᴴ *
          (((tensorIdentityBasis (ρ := ρ) U)ᴴ *
            tensorIdentityBasis (ρ := ρ) U) * V) := by
      rw [Matrix.mul_assoc]
    _ = Vᴴ * V := by
      rw [star_tensorIdentityBasis_mul_self U hU]
      simp
    _ = 1 := hV

/-- Composition with a square unitary preserves the right rectangular
unitary identity. -/
theorem physicalLeafSpectralBasis_mul_star_self
    {P I ρ : Type*}
    [Fintype P] [Fintype I] [Fintype ρ]
    [DecidableEq P] [DecidableEq I] [DecidableEq ρ]
    (U : Matrix P I ℂ)
    (V : Matrix (I × ρ) (I × ρ) ℂ)
    (hU :
      U * Uᴴ = (1 : Matrix P P ℂ))
    (hV :
      V * Vᴴ =
        (1 : Matrix (I × ρ) (I × ρ) ℂ)) :
    physicalLeafSpectralBasis U V *
        (physicalLeafSpectralBasis U V)ᴴ =
      (1 : Matrix (P × ρ) (P × ρ) ℂ) := by
  rw [conjTranspose_physicalLeafSpectralBasis,
    physicalLeafSpectralBasis]
  calc
    tensorIdentityBasis (ρ := ρ) U * V *
          (Vᴴ * (tensorIdentityBasis (ρ := ρ) U)ᴴ) =
        tensorIdentityBasis (ρ := ρ) U *
          (V * Vᴴ) *
          (tensorIdentityBasis (ρ := ρ) U)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = tensorIdentityBasis (ρ := ρ) U *
          (tensorIdentityBasis (ρ := ρ) U)ᴴ := by
      rw [hV]
      simp
    _ = 1 := tensorIdentityBasis_mul_star_self U hU

end

end GaloisForLFunctions.HTGeometry
