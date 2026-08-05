import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectHallExpansion

/-!
# Exact finite Pauli-character projectors

The paired-Pauli conjugation characters form a Walsh system on every finite
register. Their normalized character averages are exact spectral projectors.
The final extraction theorem shows that membership of a character-graded sum
in any paired-Pauli-invariant subspace forces membership of every component.
-/

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One-site Pauli conjugation signs are exactly orthogonal. -/
theorem boolPauliConjugationSign_orthogonality
    (p r : Option (Fin 3)) :
    (∑ q : Option (Fin 3),
      boolPauliConjugationSign q p * boolPauliConjugationSign q r) =
      if p = r then 4 else 0 := by
  rcases p with _ | p
  · rcases r with _ | r
    · simp [boolPauliConjugationSign]
    · fin_cases r
      all_goals simp [Fintype.sum_option, boolPauliConjugationSign,
        Fin.sum_univ_succ]
      all_goals norm_num
  · rcases r with _ | r
    · fin_cases p
      all_goals simp [Fintype.sum_option, boolPauliConjugationSign,
        Fin.sum_univ_succ]
      all_goals norm_num
    · fin_cases p <;> fin_cases r
      all_goals simp [Fintype.sum_option, boolPauliConjugationSign,
        Fin.sum_univ_succ]
      all_goals norm_num

/-- Product Pauli conjugation characters are orthogonal on every finite
register, including the empty register. -/
theorem finitePauliConjugationSign_orthogonality
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P R : σ → Option (Fin 3)) :
    (∑ Q : σ → Option (Fin 3),
      finitePauliConjugationSign Q P *
        finitePauliConjugationSign Q R) =
      if P = R then (4 : ℂ) ^ Fintype.card σ else 0 := by
  rw [show (∑ Q : σ → Option (Fin 3),
      finitePauliConjugationSign Q P *
        finitePauliConjugationSign Q R) =
      ∑ Q : σ → Option (Fin 3),
        ∏ s, boolPauliConjugationSign (Q s) (P s) *
          boolPauliConjugationSign (Q s) (R s) by
    apply Finset.sum_congr rfl
    intro Q _hQ
    rw [finitePauliConjugationSign,
      finitePauliConjugationSign, Finset.prod_mul_distrib]]
  rw [show (∑ Q : σ → Option (Fin 3),
      ∏ s, boolPauliConjugationSign (Q s) (P s) *
        boolPauliConjugationSign (Q s) (R s)) =
      ∏ s, ∑ q : Option (Fin 3),
        boolPauliConjugationSign q (P s) *
          boolPauliConjugationSign q (R s) from
    (Fintype.prod_sum fun s (q : Option (Fin 3)) =>
      boolPauliConjugationSign q (P s) *
        boolPauliConjugationSign q (R s)).symm]
  simp_rw [boolPauliConjugationSign_orthogonality]
  by_cases hPR : P = R
  · subst R
    simp [Finset.prod_const]
  · rw [if_neg hPR]
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hPR
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    rw [if_neg hs]

/-- Normalized paired-Pauli character projector. -/
def finiteTwoReplicaPauliCharacterProjector
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) :
    FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ :=
  ((4 : ℂ) ^ Fintype.card σ)⁻¹ •
    ∑ Q : σ → Option (Fin 3),
      finitePauliConjugationSign Q P •
        finiteTwoReplicaPairedPauliConjugationLinear Q

/-- The character projector is identity on its own exact grade and zero on
every other exact grade. -/
theorem finiteTwoReplicaPauliCharacterProjector_apply_grade
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P R : σ → Option (Fin 3))
    (X : FiniteTwoReplicaMatrix σ)
    (hX : X ∈ finiteTwoReplicaPauliCharacterSubspace R) :
    finiteTwoReplicaPauliCharacterProjector P X =
      if P = R then X else 0 := by
  rw [finiteTwoReplicaPauliCharacterProjector]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  have hgrade := (mem_finiteTwoReplicaPauliCharacterSubspace_iff R X).mp hX
  simp_rw [hgrade]
  simp only [smul_smul]
  rw [← Finset.sum_smul]
  rw [finitePauliConjugationSign_orthogonality]
  by_cases hPR : P = R
  · rw [if_pos hPR, if_pos hPR]
    rw [smul_smul, inv_mul_cancel₀]
    · exact one_smul ℂ X
    · exact pow_ne_zero _ (by norm_num)
  · rw [if_neg hPR, if_neg hPR]
    simp

/-- Every character projector preserves a subspace invariant under all
paired-Pauli conjugations. -/
theorem finiteTwoReplicaPauliCharacterProjector_mem_of_invariant
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3))
    (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hU : ∀ Q : σ → Option (Fin 3),
      U.map (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤ U)
    {X : FiniteTwoReplicaMatrix σ} (hX : X ∈ U) :
    finiteTwoReplicaPauliCharacterProjector P X ∈ U := by
  rw [finiteTwoReplicaPauliCharacterProjector]
  apply U.smul_mem
  simp only [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro Q _hQ
  apply U.smul_mem
  exact hU Q (Submodule.mem_map_of_mem hX)

/-- Exact graded extraction: if a finite sum of exact character components
belongs to a paired-Pauli-invariant subspace, every component belongs to it. -/
theorem finiteTwoReplicaPauliCharacter_component_mem_of_sum_mem
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hU : ∀ Q : σ → Option (Fin 3),
      U.map (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤ U)
    (x : (σ → Option (Fin 3)) → FiniteTwoReplicaMatrix σ)
    (hx : ∀ R, x R ∈ finiteTwoReplicaPauliCharacterSubspace R)
    (hsum : (∑ R, x R) ∈ U)
    (P : σ → Option (Fin 3)) :
    x P ∈ U := by
  have hproject :=
    finiteTwoReplicaPauliCharacterProjector_mem_of_invariant
      P U hU hsum
  rw [map_sum] at hproject
  simp_rw [finiteTwoReplicaPauliCharacterProjector_apply_grade
    P _ _ (hx _)] at hproject
  simpa using hproject

end

end GaloisForLFunctions.HTGeometry
