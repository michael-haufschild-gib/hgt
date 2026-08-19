/-
# Physical endpoint-complete path extension

This module packages the exact data needed to iterate the spectral-action witness while preserving
literal tensor locality.  One extension tensors the old spectral basis with the new qubit, applies
the exact canonical eigenbasis of the leaf Hamiltonian, and records that the new endpoint probe is
one-site while the Hamiltonian changes by one onsite term and one parent--leaf interaction.
-/
import GaloisForLFunctions.HTGeometry.EndpointCompleteMaximalLeafExtension
import GaloisForLFunctions.HTGeometry.PhysicalObserverSpectralRealization
import GaloisForLFunctions.HTGeometry.ArbitraryGraphLocalHamiltonianGenericityLaw

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix Kronecker BigOperators

/-- A maximally-projective Hamiltonian with a fully supported one-site endpoint channel and exact
tensor-tree locality provenance. -/
structure PhysicallyRealizedEndpointCompleteSystem where
  State : Type
  PhysicalState : Type
  Observer : Type
  [stateFintype : Fintype State]
  [stateDecidableEq : DecidableEq State]
  [stateNonempty : Nonempty State]
  [physicalFintype : Fintype PhysicalState]
  [physicalDecidableEq : DecidableEq PhysicalState]
  [observerFintype : Fintype Observer]
  [observerDecidableEq : DecidableEq Observer]
  energy : State → ℝ
  energy_maximallyProjective : MaximallyProjectiveEnergy energy
  three_le_stateCard : 3 ≤ Fintype.card State
  basis : Matrix PhysicalState State ℂ
  star_basis_mul_basis : basisᴴ * basis = (1 : Matrix State State ℂ)
  basis_mul_star_basis : basis * basisᴴ =
    (1 : Matrix PhysicalState PhysicalState ℂ)
  hamiltonian : Matrix PhysicalState PhysicalState ℂ
  hamiltonian_eq_diagonal :
    hamiltonian = basis * Matrix.diagonal (fun i => (energy i : ℂ)) * basisᴴ
  tree : RootedTensorTree PhysicalState Observer
  endpoint : Observer
  hamiltonian_local : tree.IsLocalHamiltonian hamiltonian
  endpointProbe : Matrix PhysicalState PhysicalState ℂ
  endpointProbe_isHermitian : endpointProbe.IsHermitian
  endpointProbe_local : tree.IsOneSite endpoint endpointProbe
  endpointTransition_ne_zero :
    ∀ a b : State, a ≠ b → (basisᴴ * endpointProbe * basis) a b ≠ 0

attribute [instance]
  PhysicallyRealizedEndpointCompleteSystem.stateFintype
  PhysicallyRealizedEndpointCompleteSystem.stateDecidableEq
  PhysicallyRealizedEndpointCompleteSystem.stateNonempty
  PhysicallyRealizedEndpointCompleteSystem.physicalFintype
  PhysicallyRealizedEndpointCompleteSystem.physicalDecidableEq
  PhysicallyRealizedEndpointCompleteSystem.observerFintype
  PhysicallyRealizedEndpointCompleteSystem.observerDecidableEq

/-- Spectral coordinates of the stored endpoint probe. -/
def PhysicallyRealizedEndpointCompleteSystem.endpointTransition
    (Z : PhysicallyRealizedEndpointCompleteSystem) : Matrix Z.State Z.State ℂ :=
  Z.basisᴴ * Z.endpointProbe * Z.basis

theorem PhysicallyRealizedEndpointCompleteSystem.hamiltonian_coordinate
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    Z.basisᴴ * Z.hamiltonian * Z.basis =
      Matrix.diagonal (fun i => (Z.energy i : ℂ)) := by
  rw [Z.hamiltonian_eq_diagonal]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Z.basisᴴ Z.basis, Z.star_basis_mul_basis,
    Matrix.one_mul]
  simp

/-- **Physical endpoint-complete leaf extension.**  One qubit is attached to the stored endpoint.
The returned Hamiltonian has maximal projective spectrum, is local on the leaf-extended tree, and
has a Hermitian one-site probe at the new endpoint with no zero off-diagonal spectral entry. -/
theorem PhysicallyRealizedEndpointCompleteSystem.exists_leafExtension
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    ∃ Z' : PhysicallyRealizedEndpointCompleteSystem,
      Z'.State = (Z.State × Bool) ∧
      Z'.PhysicalState = (Z.PhysicalState × Bool) ∧
      Z'.Observer = Sum Z.Observer Unit := by
  classical
  let M : Matrix Z.State Z.State ℂ := Z.endpointTransition
  have hMherm : M.IsHermitian := by
    exact Matrix.isHermitian_conjTranspose_mul_mul
      Z.basis Z.endpointProbe_isHermitian
  have hM : ∀ a b : Z.State, a ≠ b → M a b ≠ 0 := by
    exact Z.endpointTransition_ne_zero
  obtain ⟨z, C, q, hH, e, X, hp, hmaxCanonical, he, hXherm, hXfull⟩ :=
    exists_maximallyProjective_unitaryEndpointComplete_realLeafParameter
      Z.three_le_stateCard Z.energy Z.energy_maximallyProjective M hMherm hM
  let p := realLocalExtensionParameter (localExtensionSliceParameter q)
  let nextEnergy : Z.State × Bool → ℝ :=
    C.realBranchEnergy (fun i => (Z.energy i : ℂ))
      (boolShift (z : ℂ)) M p
  let V : Matrix (Z.State × Bool) (Z.State × Bool) ℂ :=
    C.unitaryEigenvectorMatrix hH e
  let nextBasis : Matrix (Z.PhysicalState × Bool) (Z.State × Bool) ℂ :=
    physicalLeafSpectralBasis Z.basis V
  let nextHamiltonian : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ :=
    physicalLeafHamiltonian Z.hamiltonian Z.endpointProbe p.1 p.2
  let nextProbe : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ :=
    layerMatrixCoupling (1 : Matrix Z.PhysicalState Z.PhysicalState ℂ) X
  let nextTree : RootedTensorTree (Z.PhysicalState × Bool) (Sum Z.Observer Unit) :=
    RootedTensorTree.leaf Z.tree Bool Z.endpoint

  have hVleft : Vᴴ * V = (1 : Matrix (Z.State × Bool) (Z.State × Bool) ℂ) := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      C.star_unitaryEigenvectorMatrix_mul_self hH e
  have hVright : V * Vᴴ = (1 : Matrix (Z.State × Bool) (Z.State × Bool) ℂ) := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      C.unitaryEigenvectorMatrix_mul_star_self hH e
  have hnextBasisLeft : nextBasisᴴ * nextBasis =
      (1 : Matrix (Z.State × Bool) (Z.State × Bool) ℂ) := by
    exact physicalLeafSpectralBasis_star_mul_self
      Z.basis V Z.star_basis_mul_basis hVleft
  have hnextBasisRight : nextBasis * nextBasisᴴ =
      (1 : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) := by
    exact physicalLeafSpectralBasis_mul_star_self
      Z.basis V Z.basis_mul_star_basis hVright

  have hphysicalCoordinate :
      (tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ * nextHamiltonian *
          tensorIdentityBasis (ρ := Bool) Z.basis =
        localExtensionMatrix (fun i => (Z.energy i : ℂ)) p.1 M p.2 := by
    exact tensorIdentityBasis_coordinate_physicalLeafHamiltonian
      Z.basis Z.hamiltonian Z.endpointProbe
      (fun i => (Z.energy i : ℂ)) p.1 M p.2
      Z.star_basis_mul_basis Z.hamiltonian_coordinate rfl
  have hTensorRight :
      tensorIdentityBasis (ρ := Bool) Z.basis *
          (tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ =
        (1 : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) :=
    tensorIdentityBasis_mul_star_self Z.basis Z.basis_mul_star_basis
  have hphysicalRecover :
      nextHamiltonian =
        tensorIdentityBasis (ρ := Bool) Z.basis *
          localExtensionMatrix (fun i => (Z.energy i : ℂ)) p.1 M p.2 *
          (tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ := by
    calc
      nextHamiltonian =
          (1 : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) *
            nextHamiltonian *
            (1 : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) := by simp
      _ = (tensorIdentityBasis (ρ := Bool) Z.basis *
              (tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ) *
            nextHamiltonian *
            (tensorIdentityBasis (ρ := Bool) Z.basis *
              (tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ) := by
          rw [hTensorRight]
      _ = tensorIdentityBasis (ρ := Bool) Z.basis *
            ((tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ * nextHamiltonian *
              tensorIdentityBasis (ρ := Bool) Z.basis) *
            (tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = tensorIdentityBasis (ρ := Bool) Z.basis *
            localExtensionMatrix (fun i => (Z.energy i : ℂ)) p.1 M p.2 *
            (tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ := by
          rw [hphysicalCoordinate]
  have hlocalDiagonal :
      localExtensionMatrix (fun i => (Z.energy i : ℂ)) p.1 M p.2 =
        V * Matrix.diagonal (fun i => (nextEnergy i : ℂ)) * Vᴴ := by
    exact C.localExtensionMatrix_eq_unitary_diagonal
      (fun i => (Z.energy i : ℂ)) (boolShift (z : ℂ)) M p hH e he
  have hnextHamiltonianDiagonal :
      nextHamiltonian = nextBasis *
        Matrix.diagonal (fun i => (nextEnergy i : ℂ)) * nextBasisᴴ := by
    rw [hphysicalRecover, hlocalDiagonal]
    simp [nextBasis, physicalLeafSpectralBasis, Matrix.mul_assoc]
  have hnextMax : MaximallyProjectiveEnergy nextEnergy := by
    have hEq : nextEnergy = fun i => hH.eigenvalues (e i) := funext he
    rw [hEq]
    exact maximallyProjectiveEnergy_equiv e hmaxCanonical
  have hnextLocal : nextTree.IsLocalHamiltonian nextHamiltonian := by
    exact RootedTensorTree.isLocalHamiltonian_physicalLeafHamiltonian
      Z.tree Z.endpoint Z.hamiltonian Z.endpointProbe p.1 p.2
      Z.hamiltonian_local Z.endpointProbe_local
  have hnextProbeHerm : nextProbe.IsHermitian := by
    exact layerMatrixCoupling_isHermitian Matrix.isHermitian_one hXherm
  have hnextProbeLocal : nextTree.IsOneSite (Sum.inr ()) nextProbe := by
    change ∃ R : Matrix Bool Bool ℂ,
      nextProbe = layerMatrixCoupling
        (1 : Matrix Z.PhysicalState Z.PhysicalState ℂ) R
    exact ⟨X, rfl⟩
  have hidentityCoordinate :
      Z.basisᴴ * (1 : Matrix Z.PhysicalState Z.PhysicalState ℂ) * Z.basis =
        (1 : Matrix Z.State Z.State ℂ) := by
    simpa [Matrix.mul_assoc] using Z.star_basis_mul_basis
  have hprobeTensorCoordinate :
      (tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ * nextProbe *
          tensorIdentityBasis (ρ := Bool) Z.basis =
        layerMatrixCoupling (1 : Matrix Z.State Z.State ℂ) X := by
    exact tensorIdentityBasis_coordinate_layer Z.basis
      (1 : Matrix Z.PhysicalState Z.PhysicalState ℂ)
      (1 : Matrix Z.State Z.State ℂ) X hidentityCoordinate
  have hnextTransition :
      nextBasisᴴ * nextProbe * nextBasis =
        C.unitaryProbeMatrix hH e
          (layerMatrixCoupling (1 : Matrix Z.State Z.State ℂ) X) := by
    rw [conjTranspose_physicalLeafSpectralBasis]
    simp only [nextBasis, physicalLeafSpectralBasis, Matrix.mul_assoc]
    calc
      Vᴴ * ((tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ *
          (nextProbe * (tensorIdentityBasis (ρ := Bool) Z.basis * V))) =
          Vᴴ * (((tensorIdentityBasis (ρ := Bool) Z.basis)ᴴ * nextProbe *
            tensorIdentityBasis (ρ := Bool) Z.basis) * V) := by
              simp only [Matrix.mul_assoc]
      _ = Vᴴ * (layerMatrixCoupling (1 : Matrix Z.State Z.State ℂ) X * V) := by
            rw [hprobeTensorCoordinate]
      _ = _ := by
        simp [LocalExtensionEigenbranchChart.unitaryProbeMatrix, V,
          Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  let Z' : PhysicallyRealizedEndpointCompleteSystem :=
    { State := Z.State × Bool
      PhysicalState := Z.PhysicalState × Bool
      Observer := Sum Z.Observer Unit
      stateFintype := inferInstance
      stateDecidableEq := inferInstance
      stateNonempty := inferInstance
      physicalFintype := inferInstance
      physicalDecidableEq := inferInstance
      observerFintype := inferInstance
      observerDecidableEq := inferInstance
      energy := nextEnergy
      energy_maximallyProjective := hnextMax
      three_le_stateCard := by
        have hthree := Z.three_le_stateCard
        rw [Fintype.card_prod, Fintype.card_bool]
        omega
      basis := nextBasis
      star_basis_mul_basis := hnextBasisLeft
      basis_mul_star_basis := hnextBasisRight
      hamiltonian := nextHamiltonian
      hamiltonian_eq_diagonal := hnextHamiltonianDiagonal
      tree := nextTree
      endpoint := Sum.inr ()
      hamiltonian_local := hnextLocal
      endpointProbe := nextProbe
      endpointProbe_isHermitian := hnextProbeHerm
      endpointProbe_local := hnextProbeLocal
      endpointTransition_ne_zero := by
        intro a b hab
        rw [hnextTransition]
        exact hXfull a b hab }
  exact ⟨Z', rfl, rfl, rfl⟩

end

end GaloisForLFunctions.HTGeometry
