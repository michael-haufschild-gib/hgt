import GaloisForLFunctions.HTGeometry.TwoReplicaFirstOrderCliffordInterpolation
import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectHallExpansion

/-!
# Internal reproduction of the nonzero Pauli-character sector

An injective collision-free graded selector does more than prove a rank
inequality when all selected images remain inside the resolved input: its
images have the full input dimension and therefore reproduce the input inside
its own one-step family shadow.

First-order Clifford interpolation supplies this internality for every
nonzero paired-Pauli character of a canonical greatest two-replica Hall
obstruction.  Consequently its complete resolved nonzero-character sector is
reproduced by literal weight-one collective Pauli commutators.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped DirectSum

/-- Collision-free injective selectors reproduce a resolved subspace when
every selected image lies back inside that subspace. -/
theorem gradedInjectiveSelector_subspace_le_shadow_of_internal
    {K X G J : Type*}
    [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [Fintype G]
    (A : J → X →ₗ[K] X)
    (grades source : G → Submodule K X)
    (U : Submodule K X)
    (selector : G → J) (target : G → G)
    (hgrades : iSupIndep grades)
    (hsourceU : ∀ g, source g ≤ U)
    (hUrank : Module.finrank K U = ∑ g, Module.finrank K (source g))
    (htarget : Function.Injective target)
    (hmap : ∀ g, (source g).map (A (selector g)) ≤ grades (target g))
    (hinjective : ∀ g,
      Function.Injective ((A (selector g)).domRestrict (source g)))
    (hinternal : ∀ g, (source g).map (A (selector g)) ≤ U) :
    U ≤ linearFamilyShadow A U := by
  classical
  let imageGrade : G → Submodule K X := fun g =>
    (source g).map (A (selector g))
  have himageIndep : iSupIndep imageGrade := by
    apply (hgrades.comp htarget).mono
    intro g
    exact hmap g
  let image := ⨆ g, imageGrade g
  have himageU : image ≤ U := by
    exact iSup_le hinternal
  let assemble : (⨁ g, ↥(imageGrade g)) →ₗ[K] X :=
    DFinsupp.lsum ℕ fun g => (imageGrade g).subtype
  have hassemble : Function.Injective assemble := by
    exact himageIndep.dfinsupp_lsum_injective
  have hrange : LinearMap.range assemble = image := by
    change LinearMap.range (DFinsupp.lsum ℕ fun g => (imageGrade g).subtype) =
      ⨆ g, imageGrade g
    rw [Submodule.iSup_eq_range_dfinsupp_lsum]
  have himageRank : ∀ g,
      Module.finrank K (imageGrade g) = Module.finrank K (source g) := by
    intro g
    let F := (A (selector g)).domRestrict (source g)
    have heq := LinearEquiv.finrank_eq
      (LinearEquiv.ofInjective F (hinjective g))
    dsimp [F, imageGrade] at heq
    rw [LinearMap.range_domRestrict] at heq
    exact heq.symm
  have himageFinrank : Module.finrank K image = Module.finrank K U := by
    have hfin := LinearEquiv.finrank_eq
      (LinearEquiv.ofInjective assemble hassemble)
    rw [Module.finrank_directSum, hrange] at hfin
    rw [show (∑ g, Module.finrank K (imageGrade g)) =
        ∑ g, Module.finrank K (source g) by
      apply Finset.sum_congr rfl
      intro g _hg
      exact himageRank g] at hfin
    exact hfin.symm.trans hUrank.symm
  have himageEq : image = U :=
    Submodule.eq_of_le_of_finrank_le himageU (by rw [himageFinrank])
  rw [← himageEq]
  apply iSup_le
  intro g
  have hsourceImage : source g ≤ image := by
    rw [himageEq]
    exact hsourceU g
  exact (Submodule.map_mono hsourceImage).trans
    (le_iSup (fun j => image.map (A j)) (selector g))

/-- The complete resolved nonzero paired-Pauli-character sector of every
canonical greatest q-local obstruction is reproduced by the literal
weight-one collective Pauli family. -/
theorem finiteTwoReplicaNonzeroPauliResolvedSubspace_le_shadow_of_greatestMaximizer
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix V),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U →
      W ≤ U) :
    finiteTwoReplicaNonzeroPauliResolvedSubspace U ≤
      linearFamilyShadow
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear V 1)
        (finiteTwoReplicaNonzeroPauliResolvedSubspace U) := by
  classical
  let grades : NonzeroPauliCharacter V →
      Submodule ℂ (FiniteTwoReplicaMatrix V) :=
    fun P => finiteTwoReplicaPauliCharacterSubspace P.1
  let source : NonzeroPauliCharacter V →
      Submodule ℂ (FiniteTwoReplicaMatrix V) :=
    fun P => U ⊓ grades P
  let selector : NonzeroPauliCharacter V → FiniteQLocalPauliLabel V 1 :=
    fun P => ⟨firstDefectPauliLabel P, by
      rw [finitePauliWeight_firstDefectPauliLabel]⟩
  let target : NonzeroPauliCharacter V → NonzeroPauliCharacter V :=
    rotateFirstPauliCharacterEquiv V
  have hgrades : iSupIndep grades := by
    exact (finiteTwoReplicaPauliCharacterSubspace_iSupIndep (σ := V)).comp
      Subtype.val_injective
  have hsourceIndep : iSupIndep source := by
    apply hgrades.mono
    intro P
    exact inf_le_right
  let assemble : (⨁ P, ↥(source P)) →ₗ[ℂ] FiniteTwoReplicaMatrix V :=
    DFinsupp.lsum ℕ fun P => (source P).subtype
  have hassemble : Function.Injective assemble := by
    exact hsourceIndep.dfinsupp_lsum_injective
  have hrange : LinearMap.range assemble =
      finiteTwoReplicaNonzeroPauliResolvedSubspace U := by
    change LinearMap.range (DFinsupp.lsum ℕ fun P => (source P).subtype) =
      ⨆ P, source P
    rw [Submodule.iSup_eq_range_dfinsupp_lsum]
  have hUrank : Module.finrank ℂ
      (finiteTwoReplicaNonzeroPauliResolvedSubspace U) =
        ∑ P, Module.finrank ℂ (source P) := by
    have hfin := LinearEquiv.finrank_eq
      (LinearEquiv.ofInjective assemble hassemble)
    rw [Module.finrank_directSum, hrange] at hfin
    exact hfin.symm
  apply gradedInjectiveSelector_subspace_le_shadow_of_internal
      (A := finiteTwoReplicaQLocalCollectiveCommutatorLinear V 1)
      (grades := grades) (source := source)
      (U := finiteTwoReplicaNonzeroPauliResolvedSubspace U)
      (selector := selector) (target := target)
  · exact hgrades
  · intro P
    exact le_iSup source P
  · exact hUrank
  · exact (rotateFirstPauliCharacterEquiv V).injective
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
        (Z : FiniteTwoReplicaMatrix V)) h
  · intro P
    rintro Y ⟨X, hX, rfl⟩
    apply le_iSup source (target P)
    constructor
    · exact firstDefectCollectiveCommutator_mem_greatestMaximizer
        q U hgreatest P X hX.1 hX.2
    · exact firstDefectCollectiveCommutator_mem_rotatedCharacter P X hX.2

end

end GaloisForLFunctions.HTGeometry
