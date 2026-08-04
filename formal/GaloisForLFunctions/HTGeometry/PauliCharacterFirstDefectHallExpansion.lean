import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectCovariance
import GaloisForLFunctions.HTGeometry.GradedSelectorHallExpansion

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped DirectSum

/-- Sum of all nonzero Pauli-character components contained in a subspace. -/
def finiteTwoReplicaNonzeroPauliResolvedSubspace
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (U : Submodule ℂ (FiniteTwoReplicaMatrix σ)) :
    Submodule ℂ (FiniteTwoReplicaMatrix σ) :=
  ⨆ P : NonzeroPauliCharacter σ,
    U ⊓ finiteTwoReplicaPauliCharacterSubspace P.1

/-- Every resolved nonzero Pauli-character subspace satisfies Hall expansion
under the literal weight-one collective Pauli family. -/
theorem finiteTwoReplicaNonzeroPauliResolvedSubspace_finrank_le_shadow
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (U : Submodule ℂ (FiniteTwoReplicaMatrix σ)) :
    Module.finrank ℂ (finiteTwoReplicaNonzeroPauliResolvedSubspace U) ≤
      Module.finrank ℂ (linearFamilyShadow
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ 1)
        (finiteTwoReplicaNonzeroPauliResolvedSubspace U)) := by
  classical
  let grades : NonzeroPauliCharacter σ →
      Submodule ℂ (FiniteTwoReplicaMatrix σ) :=
    fun P => finiteTwoReplicaPauliCharacterSubspace P.1
  let source : NonzeroPauliCharacter σ →
      Submodule ℂ (FiniteTwoReplicaMatrix σ) :=
    fun P => U ⊓ grades P
  let selector : NonzeroPauliCharacter σ → FiniteQLocalPauliLabel σ 1 :=
    fun P => ⟨firstDefectPauliLabel P, by
      rw [finitePauliWeight_firstDefectPauliLabel]⟩
  let target : NonzeroPauliCharacter σ → NonzeroPauliCharacter σ :=
    rotateFirstPauliCharacterEquiv σ
  have hgrades : iSupIndep grades := by
    exact (finiteTwoReplicaPauliCharacterSubspace_iSupIndep (σ := σ)).comp
      Subtype.val_injective
  have hsourceIndep : iSupIndep source := by
    apply hgrades.mono
    intro P
    exact inf_le_right
  let assemble : (⨁ P, ↥(source P)) →ₗ[ℂ] FiniteTwoReplicaMatrix σ :=
    DFinsupp.lsum ℕ fun P => (source P).subtype
  have hassemble : Function.Injective assemble := by
    exact hsourceIndep.dfinsupp_lsum_injective
  have hrange : LinearMap.range assemble =
      finiteTwoReplicaNonzeroPauliResolvedSubspace U := by
    change LinearMap.range (DFinsupp.lsum ℕ fun P => (source P).subtype) =
      ⨆ P, source P
    rw [Submodule.iSup_eq_range_dfinsupp_lsum]
  have hUrank :
      Module.finrank ℂ (finiteTwoReplicaNonzeroPauliResolvedSubspace U) =
        ∑ P, Module.finrank ℂ (source P) := by
    have hfin := LinearEquiv.finrank_eq
      (LinearEquiv.ofInjective assemble hassemble)
    rw [Module.finrank_directSum, hrange] at hfin
    exact hfin.symm
  apply gradedInjectiveSelector_subspace_finrank
      (A := finiteTwoReplicaQLocalCollectiveCommutatorLinear σ 1)
      (grades := grades) (source := source)
      (U := finiteTwoReplicaNonzeroPauliResolvedSubspace U)
      (selector := selector) (target := target)
  · exact hgrades
  · intro P
    exact le_iSup source P
  · exact hUrank
  · exact (rotateFirstPauliCharacterEquiv σ).injective
  · intro P
    rintro Y ⟨X, hX, rfl⟩
    change finiteTwoReplicaCollectiveCommutatorLinear
        (firstDefectPauliLabel P) X ∈ grades (target P)
    exact firstDefectCollectiveCommutator_mem_rotatedCharacter P X hX.2
  · intro P X Y hXY
    apply Subtype.ext
    have hgrade := firstDefectCollectiveCommutator_injective_on_character P
    have h := hgrade
      (a₁ := (⟨X.1, X.2.2⟩ : finiteTwoReplicaPauliCharacterSubspace P.1))
      (a₂ := (⟨Y.1, Y.2.2⟩ : finiteTwoReplicaPauliCharacterSubspace P.1))
      (by simpa [selector,
          finiteTwoReplicaQLocalCollectiveCommutatorLinear] using hXY)
    exact congrArg
      (fun Z : finiteTwoReplicaPauliCharacterSubspace P.1 =>
        (Z : FiniteTwoReplicaMatrix σ)) h

end

end GaloisForLFunctions.HTGeometry
