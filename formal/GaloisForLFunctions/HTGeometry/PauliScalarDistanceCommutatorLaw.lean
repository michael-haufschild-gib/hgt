import GaloisForLFunctions.HTGeometry.PauliUniformCommutatorEnergy
import GaloisForLFunctions.HTGeometry.PauliTwoLocalLabels

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def pauliNonScalarCoefficient
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : (σ → Option (Fin 3)) → ℂ)
    (P : σ → Option (Fin 3)) : ℂ :=
  if P = pauliCharacterZero then 0 else J P

theorem sum_norm_pauliNonScalarCoefficient_sq
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : (σ → Option (Fin 3)) → ℂ) :
    (∑ P, ‖pauliNonScalarCoefficient J P‖ ^ 2) =
      ∑ P : NonzeroPauliCharacter σ, ‖J P.1‖ ^ 2 := by
  let nz : Finset (σ → Option (Fin 3)) :=
    Finset.univ.filter fun P => P ≠ pauliCharacterZero
  have hsub :
      (∑ P ∈ nz, ‖J P‖ ^ 2) =
        ∑ P : NonzeroPauliCharacter σ, ‖J P.1‖ ^ 2 := by
    exact Finset.sum_subtype nz (by simp [nz]) (fun P => ‖J P‖ ^ 2)
  calc
    (∑ P, ‖pauliNonScalarCoefficient J P‖ ^ 2) =
        ∑ P ∈ nz, ‖pauliNonScalarCoefficient J P‖ ^ 2 := by
      symm
      apply Finset.sum_subset (by simp [nz])
      intro P _ hP
      simp only [nz, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hP
      simp [pauliNonScalarCoefficient, hP]
    _ = ∑ P ∈ nz, ‖J P‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro P hP
      simp only [nz, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      simp [pauliNonScalarCoefficient, hP]
    _ = ∑ P : NonzeroPauliCharacter σ, ‖J P.1‖ ^ 2 := hsub

theorem pauliCombination_sub_scalar_eq_nonScalar
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : (σ → Option (Fin 3)) → ℂ) :
    (∑ P, J P • finitePauliMatrix P) -
        J pauliCharacterZero • finitePauliMatrix pauliCharacterZero =
      ∑ P, pauliNonScalarCoefficient J P • finitePauliMatrix P := by
  classical
  have hsingle :
      J pauliCharacterZero • finitePauliMatrix pauliCharacterZero =
        ∑ P, if P = pauliCharacterZero then
          J P • finitePauliMatrix P else 0 := by
    symm
    simpa using Finset.sum_ite_eq' Finset.univ pauliCharacterZero
      (fun P => J P • finitePauliMatrix P)
  rw [hsingle]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hP : P = pauliCharacterZero
  · subst P
    simp [pauliNonScalarCoefficient]
  · simp [pauliNonScalarCoefficient, hP]

theorem frobSq_pauliCombination_sub_scalar
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : (σ → Option (Fin 3)) → ℂ) :
    frobSq
        ((∑ P, J P • finitePauliMatrix P) -
          J pauliCharacterZero • finitePauliMatrix pauliCharacterZero) =
      2 ^ Fintype.card σ *
        ∑ P : NonzeroPauliCharacter σ, ‖J P.1‖ ^ 2 := by
  rw [pauliCombination_sub_scalar_eq_nonScalar,
    frobSq_pauliCombination, sum_norm_pauliNonScalarCoefficient_sq]

theorem finitePauliMatrix_pauliCharacterZero
    {σ : Type*} [Fintype σ] [DecidableEq σ] :
    finitePauliMatrix (pauliCharacterZero (σ := σ)) = 1 := by
  classical
  ext x y
  rw [finitePauliMatrix, Matrix.one_apply]
  by_cases hxy : x = y
  · subst y
    simp [pauliCharacterZero, boolPauliOptionEntry_none]
  · rw [if_neg hxy]
    obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by
      rw [pauliCharacterZero, boolPauliOptionEntry_none, if_neg hs])

theorem trace_eq_card_mul_pauliScalarCoefficient
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    Matrix.trace A =
      (2 : ℂ) ^ Fintype.card σ * pauliCoeff A pauliCharacterZero := by
  simpa [finitePauliMatrix_pauliCharacterZero] using
    trace_star_pauli_mul A (pauliCharacterZero (σ := σ))

def pauliScalarPart
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  pauliCoeff A pauliCharacterZero • finitePauliMatrix pauliCharacterZero

theorem pauliScalarPart_eq_normalizedTrace_smul_one
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    pauliScalarPart A =
      (((2 : ℂ) ^ Fintype.card σ)⁻¹ * Matrix.trace A) • 1 := by
  rw [pauliScalarPart, finitePauliMatrix_pauliCharacterZero,
    trace_eq_card_mul_pauliScalarCoefficient]
  have htwo : (2 : ℂ) ^ Fintype.card σ ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

def pauliScalarShiftCoefficient
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : (σ → Option (Fin 3)) → ℂ) (c : ℂ)
    (P : σ → Option (Fin 3)) : ℂ :=
  if P = pauliCharacterZero then J P - c else J P

theorem pauliCombination_sub_scalarShift_eq
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : (σ → Option (Fin 3)) → ℂ) (c : ℂ) :
    (∑ P, J P • finitePauliMatrix P) -
        c • finitePauliMatrix pauliCharacterZero =
      ∑ P, pauliScalarShiftCoefficient J c P • finitePauliMatrix P := by
  classical
  have hsingle :
      c • finitePauliMatrix pauliCharacterZero =
        ∑ P : σ → Option (Fin 3), if P = pauliCharacterZero then
          c • finitePauliMatrix P else 0 := by
    symm
    simpa using Finset.sum_ite_eq' Finset.univ pauliCharacterZero
      (fun P => c • finitePauliMatrix P)
  rw [hsingle, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hP : P = pauliCharacterZero
  · subst P
    simp [pauliScalarShiftCoefficient, sub_smul]
  · simp [pauliScalarShiftCoefficient, hP]

theorem sum_norm_pauliScalarShiftCoefficient_sq
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : (σ → Option (Fin 3)) → ℂ) (c : ℂ) :
    (∑ P, ‖pauliScalarShiftCoefficient J c P‖ ^ 2) =
      ‖J pauliCharacterZero - c‖ ^ 2 +
        ∑ P : NonzeroPauliCharacter σ, ‖J P.1‖ ^ 2 := by
  let nz : Finset (σ → Option (Fin 3)) :=
    Finset.univ.erase pauliCharacterZero
  have hsub :
      (∑ P ∈ nz, ‖J P‖ ^ 2) =
        ∑ P : NonzeroPauliCharacter σ, ‖J P.1‖ ^ 2 := by
    exact Finset.sum_subtype nz (by simp [nz]) (fun P => ‖J P‖ ^ 2)
  rw [← hsub, ← Finset.add_sum_erase Finset.univ
    (fun P => ‖pauliScalarShiftCoefficient J c P‖ ^ 2)
    (Finset.mem_univ pauliCharacterZero)]
  simp only [pauliScalarShiftCoefficient, if_pos]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hne : P ≠ pauliCharacterZero := by simpa [nz] using hP
  simp [pauliScalarShiftCoefficient, hne]

theorem frobSq_pauliCombination_sub_scalarShift
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : (σ → Option (Fin 3)) → ℂ) (c : ℂ) :
    frobSq
        ((∑ P, J P • finitePauliMatrix P) -
          c • finitePauliMatrix pauliCharacterZero) =
      2 ^ Fintype.card σ *
        (‖J pauliCharacterZero - c‖ ^ 2 +
          ∑ P : NonzeroPauliCharacter σ, ‖J P.1‖ ^ 2) := by
  rw [pauliCombination_sub_scalarShift_eq,
    frobSq_pauliCombination, sum_norm_pauliScalarShiftCoefficient_sq]

theorem frobSq_sub_scalar_smul_one
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (c : ℂ) :
    frobSq (A - c • (1 : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ)) =
      2 ^ Fintype.card σ *
        (‖pauliCoeff A pauliCharacterZero - c‖ ^ 2 +
          ∑ P : NonzeroPauliCharacter σ, ‖pauliCoeff A P.1‖ ^ 2) := by
  have h := frobSq_pauliCombination_sub_scalarShift (pauliCoeff A) c
  rw [sum_pauliCoeff_smul A, finitePauliMatrix_pauliCharacterZero] at h
  exact h

theorem frobSq_sub_pauliScalarPart
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    frobSq (A - pauliScalarPart A) =
      2 ^ Fintype.card σ *
        ∑ P : NonzeroPauliCharacter σ, ‖pauliCoeff A P.1‖ ^ 2 := by
  have h := frobSq_pauliCombination_sub_scalar (pauliCoeff A)
  rw [sum_pauliCoeff_smul A] at h
  exact h

theorem pauliScalarPart_minimizes_frobSq_scalarDistance
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (c : ℂ) :
    frobSq (A - pauliScalarPart A) ≤
      frobSq (A - c • (1 : Matrix (FiniteQubitConfiguration σ)
        (FiniteQubitConfiguration σ) ℂ)) := by
  rw [frobSq_sub_pauliScalarPart, frobSq_sub_scalar_smul_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Universal scalar-quotient commutator coercivity: the complete bounded-local
Pauli dictionary detects every operator's exact Hilbert--Schmidt distance from
the scalar subspace with a dimension-linear factor. -/
theorem boundedLocalPauli_commutator_energy_ge_scalarDistance
    {n q : ℕ} (hq : 2 ≤ q)
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    4 * ((n - 1 : ℕ) : ℝ) * frobSq (A - pauliScalarPart A) ≤
      ∑ Q : boundedLocalPauliLabel n q,
        frobSq
          (finitePauliMatrix Q.1 * A - A * finitePauliMatrix Q.1) := by
  rw [frobSq_sub_pauliScalarPart]
  simp only [Fintype.card_fin]
  convert boundedLocalPauli_total_commutator_energy_matrix_ge hq A using 1 <;> ring

end

end GaloisForLFunctions.HTGeometry
