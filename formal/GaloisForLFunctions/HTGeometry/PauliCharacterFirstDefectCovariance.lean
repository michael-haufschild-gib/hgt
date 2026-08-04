import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalPauliHallSymmetryReduction
import Mathlib.LinearAlgebra.Eigenspace.Pi

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem boolPauliConjugationSign_next_eq_selected_mul_source
    (q : Option (Fin 3)) (a : Fin 3) :
    boolPauliConjugationSign q (some (pauliAxisNext a)) =
      boolPauliConjugationSign q (some (pauliAxisPrev a)) *
        boolPauliConjugationSign q (some a) := by
  fin_cases q <;> fin_cases a <;>
    norm_num [boolPauliConjugationSign, pauliAxisNext, pauliAxisPrev] <;>
    simp_all

theorem boolPauliConjugationSign_prev_source_eq_neg_one
    (a : Fin 3) :
    boolPauliConjugationSign (some (pauliAxisPrev a)) (some a) = -1 := by
  fin_cases a <;>
    norm_num [boolPauliConjugationSign, pauliAxisPrev] <;> simp_all

/-- The first-defect rotation translates every paired-Pauli character by
the exact character of its selected weight-one Pauli. -/
theorem finitePauliConjugationSign_rotateFirst
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (Q : σ → Option (Fin 3)) (P : NonzeroPauliCharacter σ) :
    finitePauliConjugationSign Q
        (rotateFirstPauliCharacter pauliAxisNext P).1 =
      finitePauliConjugationSign Q (firstDefectPauliLabel P) *
        finitePauliConjugationSign Q P.1 := by
  rw [finitePauliConjugationSign, finitePauliConjugationSign,
    finitePauliConjugationSign, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases hfirst : i = firstActivePauliSite P
  · subst i
    rw [rotateFirstPauliCharacter_value_first,
      ← firstActivePauliAxis_spec P]
    simp only [firstDefectPauliLabel, if_pos]
    exact boolPauliConjugationSign_next_eq_selected_mul_source
      (Q (firstActivePauliSite P)) (firstActivePauliAxis P)
  · rw [rotateFirstPauliCharacter_value_of_ne_first P i hfirst]
    simp [firstDefectPauliLabel, hfirst, boolPauliConjugationSign]

/-- The selected weight-one Pauli sees its source character as exactly odd. -/
theorem finitePauliConjugationSign_firstDefect_source
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    finitePauliConjugationSign (firstDefectPauliLabel P) P.1 = -1 := by
  rw [finitePauliConjugationSign]
  refine (Finset.prod_eq_single (firstActivePauliSite P) ?_ ?_).trans ?_
  · intro i _hi hne
    simp [firstDefectPauliLabel, hne, boolPauliConjugationSign]
  · intro hnot
    exact absurd (Finset.mem_univ (firstActivePauliSite P)) hnot
  · rw [firstDefectPauliLabel, if_pos rfl, ← firstActivePauliAxis_spec P]
    exact boolPauliConjugationSign_prev_source_eq_neg_one
      (firstActivePauliAxis P)

/-- Simultaneous paired-Pauli character subspace labelled by a phase-free
global Pauli word. -/
def finiteTwoReplicaPauliCharacterSubspace
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) : Submodule ℂ (FiniteTwoReplicaMatrix σ) :=
  ⨅ Q : σ → Option (Fin 3), LinearMap.ker
    (finiteTwoReplicaPairedPauliConjugationLinear Q -
      finitePauliConjugationSign Q P • LinearMap.id)

theorem mem_finiteTwoReplicaPauliCharacterSubspace_iff
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) (X : FiniteTwoReplicaMatrix σ) :
    X ∈ finiteTwoReplicaPauliCharacterSubspace P ↔
      ∀ Q : σ → Option (Fin 3),
        finiteTwoReplicaPairedPauliConjugationLinear Q X =
          finitePauliConjugationSign Q P • X := by
  simp only [finiteTwoReplicaPauliCharacterSubspace, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

/-- The selected first-defect collective commutator translates the source
character to the rotated target character. -/
theorem firstDefectCollectiveCommutator_mem_rotatedCharacter
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) (X : FiniteTwoReplicaMatrix σ)
    (hX : X ∈ finiteTwoReplicaPauliCharacterSubspace P.1) :
    finiteTwoReplicaCollectiveCommutatorLinear (firstDefectPauliLabel P) X ∈
      finiteTwoReplicaPauliCharacterSubspace
        (rotateFirstPauliCharacter pauliAxisNext P).1 := by
  rw [mem_finiteTwoReplicaPauliCharacterSubspace_iff]
  intro Q
  rw [finiteTwoReplicaPairedPauli_collectiveCommutator_intertwines,
    (mem_finiteTwoReplicaPauliCharacterSubspace_iff P.1 X).mp hX Q,
    map_smul, smul_smul, finitePauliConjugationSign_rotateFirst]

/-- The selected first-defect collective commutator is injective on every
subspace of its source character grade. -/
theorem firstDefectCollectiveCommutator_injective_on_character
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    Function.Injective
      ((finiteTwoReplicaCollectiveCommutatorLinear
        (firstDefectPauliLabel P)).domRestrict
          (finiteTwoReplicaPauliCharacterSubspace P.1)) := by
  intro X Y hXY
  apply Subtype.ext
  have hmem : X.1 - Y.1 ∈ finiteTwoReplicaPauliCharacterSubspace P.1 :=
    (finiteTwoReplicaPauliCharacterSubspace P.1).sub_mem X.2 Y.2
  have hchar := (mem_finiteTwoReplicaPauliCharacterSubspace_iff P.1 _).mp hmem
    (firstDefectPauliLabel P)
  rw [finitePauliConjugationSign_firstDefect_source] at hchar
  have hodd : finiteTwoReplicaPairedPauli (firstDefectPauliLabel P) *
      (X.1 - Y.1) * finiteTwoReplicaPairedPauli (firstDefectPauliLabel P) =
        -(X.1 - Y.1) := by
    simpa [finiteTwoReplicaPairedPauliConjugationLinear] using hchar
  have hzero : finiteTwoReplicaCollectiveCommutator
      (firstDefectPauliLabel P) (X.1 - Y.1) = 0 := by
    change finiteTwoReplicaCollectiveCommutatorLinear
      (firstDefectPauliLabel P) (X.1 - Y.1) = 0
    rw [map_sub]
    rw [sub_eq_zero]
    exact hXY
  exact sub_eq_zero.mp
    ((finiteTwoReplicaCollectiveCommutator_eq_zero_iff_of_relativeOdd
      (firstDefectPauliLabel P) (X.1 - Y.1) hodd).mp hzero)

def singlePauliAxisLabel
    {σ : Type*} [DecidableEq σ] (i : σ) (a : Fin 3) :
    σ → Option (Fin 3) :=
  fun j => if j = i then some a else none

theorem finitePauliConjugationSign_singlePauliAxisLabel
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) (i : σ) (a : Fin 3) :
    finitePauliConjugationSign (singlePauliAxisLabel i a) P =
      boolPauliConjugationSign (some a) (P i) := by
  rw [finitePauliConjugationSign]
  refine (Finset.prod_eq_single i ?_ ?_).trans ?_
  · intro j _hj hji
    simp [singlePauliAxisLabel, hji, boolPauliConjugationSign]
  · intro hnot
    exact absurd (Finset.mem_univ i) hnot
  · simp [singlePauliAxisLabel]

theorem exists_pauliAxis_conjugationSign_ne
    {p r : Option (Fin 3)} (hpr : p ≠ r) :
    ∃ a : Fin 3,
      boolPauliConjugationSign (some a) p ≠
        boolPauliConjugationSign (some a) r := by
  cases p with
  | none =>
      cases r with
      | none => exact (hpr rfl).elim
      | some b =>
          refine ⟨pauliAxisNext b, ?_⟩
          simp [boolPauliConjugationSign, pauliAxisNext_ne b]
          norm_num
  | some a =>
      cases r with
      | none =>
          refine ⟨pauliAxisNext a, ?_⟩
          simp [boolPauliConjugationSign, pauliAxisNext_ne a]
          norm_num
      | some b =>
          have hab : a ≠ b := by
            intro hab
            apply hpr
            simp [hab]
          refine ⟨a, ?_⟩
          simp [boolPauliConjugationSign, hab]
          norm_num

theorem exists_finitePauliConjugationSign_ne
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {P R : σ → Option (Fin 3)} (hPR : P ≠ R) :
    ∃ Q : σ → Option (Fin 3),
      finitePauliConjugationSign Q P ≠ finitePauliConjugationSign Q R := by
  obtain ⟨i, hi⟩ : ∃ i, P i ≠ R i := Function.ne_iff.mp hPR
  obtain ⟨a, ha⟩ := exists_pauliAxis_conjugationSign_ne hi
  exact ⟨singlePauliAxisLabel i a, by
    simpa only [finitePauliConjugationSign_singlePauliAxisLabel] using ha⟩

def finitePauliConjugationCharacter
    {σ : Type*} [Fintype σ]
    (P : σ → Option (Fin 3)) : (σ → Option (Fin 3)) → ℂ :=
  fun Q => finitePauliConjugationSign Q P

theorem finitePauliConjugationCharacter_injective
    {σ : Type*} [Fintype σ] [DecidableEq σ] :
    Function.Injective (finitePauliConjugationCharacter (σ := σ)) := by
  intro P R hchar
  by_contra hPR
  obtain ⟨Q, hQ⟩ := exists_finitePauliConjugationSign_ne hPR
  exact hQ (congrFun hchar Q)

/-- The simultaneous paired-Pauli character subspaces form an independent
family. -/
theorem finiteTwoReplicaPauliCharacterSubspace_iSupIndep
    {σ : Type*} [Fintype σ] [DecidableEq σ] :
    iSupIndep (finiteTwoReplicaPauliCharacterSubspace (σ := σ)) := by
  let C : (σ → Option (Fin 3)) →
      Module.End ℂ (FiniteTwoReplicaMatrix σ) :=
    finiteTwoReplicaPairedPauliConjugationLinear
  have hcomm : ∀ Q R, Commute (C Q) (C R) := by
    intro Q R
    apply LinearMap.ext
    intro X
    exact finiteTwoReplicaPairedPauliConjugationLinear_comm Q R X
  have hmax : iSupIndep fun χ : (σ → Option (Fin 3)) → ℂ =>
      ⨅ Q, (C Q).maxGenEigenspace (χ Q) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo C
      (fun Q R μ => Module.End.mapsTo_maxGenEigenspace_of_comm
        (hcomm R Q) μ)
  have hcomp := hmax.comp
    (finitePauliConjugationCharacter_injective (σ := σ))
  apply hcomp.mono
  intro P
  apply iInf_mono
  intro Q
  have h := Module.End.eigenspace_le_maxGenEigenspace
    (f := C Q) (μ := finitePauliConjugationCharacter P Q)
  simpa [Module.End.eigenspace_def, Module.End.one_eq_id, C,
    finitePauliConjugationCharacter] using h

end

end GaloisForLFunctions.HTGeometry
