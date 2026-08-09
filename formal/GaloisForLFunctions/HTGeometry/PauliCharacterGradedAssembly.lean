import GaloisForLFunctions.HTGeometry.TwoReplicaPauliCharacterCompleteness
import GaloisForLFunctions.HTGeometry.JointEigenspaceExhaustion
import GaloisForLFunctions.HTGeometry.SimultaneousParityGrading
import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectHallExpansion

/-!
# The graded output assembly

A subspace stable under every paired-Pauli conjugation is the sum of its Pauli-character
components.  The parity grading of an invariant subspace is indexed by sign patterns; the character
subspaces realize only some of those patterns, and the unrealized ones carry no vector at all,
because the character subspaces are independent and exhaust the space.

Consequently the intersection of an invariant subspace with the sum of the nonzero character
subspaces is exactly its resolved nonzero-character part, and the Hall expansion proved for the
resolved part is the expansion for the intersection.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Paired-Pauli conjugation as a linear equivalence. -/
def pairedPauliConjugationEquiv (Q : σ → Option (Fin 3)) :
    FiniteTwoReplicaMatrix σ ≃ₗ[ℂ] FiniteTwoReplicaMatrix σ :=
  LinearEquiv.ofLinear (finiteTwoReplicaPairedPauliConjugationLinear Q)
    (finiteTwoReplicaPairedPauliConjugationLinear Q)
    (LinearMap.ext fun X => finiteTwoReplicaPairedPauliConjugationLinear_involutive Q X)
    (LinearMap.ext fun X => finiteTwoReplicaPairedPauliConjugationLinear_involutive Q X)

@[simp] theorem pairedPauliConjugationEquiv_apply (Q : σ → Option (Fin 3))
    (X : FiniteTwoReplicaMatrix σ) :
    pairedPauliConjugationEquiv Q X = finiteTwoReplicaPairedPauliConjugationLinear Q X := rfl

/-- The character subspaces are the joint eigenspaces of the paired conjugations. -/
theorem finiteTwoReplicaPauliCharacterSubspace_eq_jointEigenspace (P : σ → Option (Fin 3)) :
    finiteTwoReplicaPauliCharacterSubspace P
      = jointEigenspace (finiteTwoReplicaPairedPauliConjugationLinear (σ := σ))
          (fun Q => finitePauliConjugationSign Q P) := by
  ext X
  rw [mem_finiteTwoReplicaPauliCharacterSubspace_iff, mem_jointEigenspace_iff]

/-- **A sign pattern realized by no Pauli word carries no vector.** -/
theorem jointEigenspace_eq_bot_of_not_character
    (s : (σ → Option (Fin 3)) → ℂ)
    (hs : ∀ P : σ → Option (Fin 3), (fun Q => finitePauliConjugationSign Q P) ≠ s) :
    jointEigenspace (finiteTwoReplicaPairedPauliConjugationLinear (σ := σ)) s = ⊥ :=
  jointEigenspace_eq_bot_of_forall_ne _ (finiteTwoReplicaPauliCharacterSubspace (σ := σ))
    (fun P Q => finitePauliConjugationSign Q P)
    finiteTwoReplicaPauliCharacterSubspace_iSupIndep
    (finiteTwoReplicaPauliCharacterSubspace_iSup_eq_top σ)
    (fun P X hX Q => (mem_finiteTwoReplicaPauliCharacterSubspace_iff P X).mp hX Q)
    s hs

/-- The parity subspaces of the paired conjugations are their joint eigenspaces. -/
theorem simultaneousParitySubspace_eq_jointEigenspace (b : (σ → Option (Fin 3)) → Bool) :
    simultaneousParitySubspace (pairedPauliConjugationEquiv (σ := σ)) Finset.univ b
      = jointEigenspace (finiteTwoReplicaPairedPauliConjugationLinear (σ := σ))
          (fun Q => if b Q then (1 : ℂ) else -1) := by
  ext X
  simp only [simultaneousParitySubspace, Submodule.mem_iInf, mem_jointEigenspace_iff]
  constructor
  · intro h Q
    have hQ := h Q (Finset.mem_univ Q)
    by_cases hb : b Q
    · rw [if_pos hb] at hQ ⊢
      rw [one_smul]
      exact (mem_involutiveEvenSubspace_iff _ X).mp hQ
    · rw [if_neg hb] at hQ ⊢
      rw [neg_one_smul]
      exact (mem_involutiveOddSubspace_iff _ X).mp hQ
  · intro h Q _
    have hQ := h Q
    by_cases hb : b Q
    · rw [if_pos hb] at hQ ⊢
      rw [one_smul] at hQ
      exact (mem_involutiveEvenSubspace_iff _ X).mpr hQ
    · rw [if_neg hb] at hQ ⊢
      rw [neg_one_smul] at hQ
      exact (mem_involutiveOddSubspace_iff _ X).mpr hQ

/-- **An invariant subspace is the sum of its Pauli-character components.**  This is the character
resolution the selector law's step `(5)` asserts. -/
theorem invariantSubspace_eq_iSup_inf_characterSubspace
    (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hstable : ∀ Q, U.map (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤ U) :
    U = ⨆ P : σ → Option (Fin 3), (U ⊓ finiteTwoReplicaPauliCharacterSubspace P) := by
  classical
  have hgrad := invariantSubspace_eq_iSup_simultaneousParitySubspace
    (K := ℂ) (by norm_num) (pairedPauliConjugationEquiv (σ := σ))
    (fun Q X => finiteTwoReplicaPairedPauliConjugationLinear_involutive Q X)
    (fun Q R X => finiteTwoReplicaPairedPauliConjugationLinear_comm Q R X)
    Finset.univ U hstable
  refine le_antisymm (hgrad.le.trans (iSup_le fun b => ?_)) (iSup_le fun P => inf_le_left)
  by_cases hreal : ∃ P : σ → Option (Fin 3),
      (fun Q => finitePauliConjugationSign Q P) = fun Q => if b Q then (1 : ℂ) else -1
  · obtain ⟨P, hP⟩ := hreal
    refine le_trans ?_ (le_iSup _ P)
    rw [simultaneousParitySubspace_eq_jointEigenspace, ← hP,
      ← finiteTwoReplicaPauliCharacterSubspace_eq_jointEigenspace]
  · have hs : ∀ P : σ → Option (Fin 3),
        (fun Q => finitePauliConjugationSign Q P) ≠ fun Q => if b Q then (1 : ℂ) else -1 := by
      intro P hP
      exact hreal ⟨P, hP⟩
    rw [simultaneousParitySubspace_eq_jointEigenspace,
      jointEigenspace_eq_bot_of_not_character _ hs]
    simp

/-- **The invariant intersection with the nonzero characters is the resolved part.** -/
theorem inf_iSup_nonzeroCharacter_eq_resolvedSubspace
    (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hstable : ∀ Q, U.map (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤ U) :
    U ⊓ (⨆ P : NonzeroPauliCharacter σ, finiteTwoReplicaPauliCharacterSubspace P.1)
      = finiteTwoReplicaNonzeroPauliResolvedSubspace U := by
  classical
  have hsub : (⨆ P : NonzeroPauliCharacter σ, finiteTwoReplicaPauliCharacterSubspace P.1)
      = ⨆ P ∈ {P : σ → Option (Fin 3) | P ≠ pauliCharacterZero},
          finiteTwoReplicaPauliCharacterSubspace P :=
    iSup_subtype' (p := fun P : σ → Option (Fin 3) => P ≠ pauliCharacterZero)
      (f := fun P _ => finiteTwoReplicaPauliCharacterSubspace P) |>.symm
  have hres : finiteTwoReplicaNonzeroPauliResolvedSubspace U
      = ⨆ P ∈ {P : σ → Option (Fin 3) | P ≠ pauliCharacterZero},
          (U ⊓ finiteTwoReplicaPauliCharacterSubspace P) :=
    iSup_subtype' (p := fun P : σ → Option (Fin 3) => P ≠ pauliCharacterZero)
      (f := fun P _ => U ⊓ finiteTwoReplicaPauliCharacterSubspace P) |>.symm
  rw [hsub, hres]
  exact inf_biSup_eq_biSup_inf_of_graded _ finiteTwoReplicaPauliCharacterSubspace_iSupIndep U
    (invariantSubspace_eq_iSup_inf_characterSubspace U hstable) _

/-- **The selector law in the card's own terms.**  For a subspace stable under every paired-Pauli
conjugation, the intersection with the nonzero character sum expands under the literal weight-one
collective Pauli family. -/
theorem invariantSubspace_inf_nonzeroCharacter_finrank_le_shadow [LinearOrder σ]
    (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hstable : ∀ Q, U.map (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤ U) :
    Module.finrank ℂ
        ↥(U ⊓ (⨆ P : NonzeroPauliCharacter σ, finiteTwoReplicaPauliCharacterSubspace P.1)) ≤
      Module.finrank ℂ (linearFamilyShadow
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ 1)
        (U ⊓ (⨆ P : NonzeroPauliCharacter σ, finiteTwoReplicaPauliCharacterSubspace P.1))) := by
  rw [inf_iSup_nonzeroCharacter_eq_resolvedSubspace U hstable]
  exact finiteTwoReplicaNonzeroPauliResolvedSubspace_finrank_le_shadow U

end

end GaloisForLFunctions.HTGeometry
