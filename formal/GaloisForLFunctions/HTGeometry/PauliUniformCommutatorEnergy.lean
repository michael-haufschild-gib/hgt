import GaloisForLFunctions.HTGeometry.PauliUniformAnticommutingIncidenceMass
import GaloisForLFunctions.HTGeometry.PauliHilbertSchmidtNorm
import GaloisForLFunctions.HTGeometry.PauliCommutatorActiveFanLowerTail

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def optMulLabelEquiv
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3)) :
    (σ → Option (Fin 3)) ≃ (σ → Option (Fin 3)) where
  toFun := optMulLabel Q
  invFun := optMulLabel Q
  left_inv := optMulLabel_optMulLabel_self Q
  right_inv := optMulLabel_optMulLabel_self Q

def pauliCommutatorResponseCoefficient
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3))
    (J : (σ → Option (Fin 3)) → ℂ)
    (R : σ → Option (Fin 3)) : ℂ :=
  J (optMulLabel Q R) *
    (optPhaseProd Q (optMulLabel Q R) -
      optPhaseProd (optMulLabel Q R) Q)

theorem pauli_commutator_sum_eq_response
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3))
    (J : (σ → Option (Fin 3)) → ℂ) :
    finitePauliMatrix Q * (∑ P, J P • finitePauliMatrix P) -
        (∑ P, J P • finitePauliMatrix P) * finitePauliMatrix Q =
      ∑ R, pauliCommutatorResponseCoefficient Q J R • finitePauliMatrix R := by
  classical
  rw [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib]
  have hleft :
      (∑ P, (finitePauliMatrix Q * (J P • finitePauliMatrix P) -
          (J P • finitePauliMatrix P) * finitePauliMatrix Q)) =
        ∑ P, (J P * (optPhaseProd Q P - optPhaseProd P Q)) •
          finitePauliMatrix (optMulLabel Q P) := by
    apply Finset.sum_congr rfl
    intro P _
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub,
      finitePauliMatrix_commutator]
    change J P • ((optPhaseProd Q P - optPhaseProd P Q) •
      finitePauliMatrix (optMulLabel Q P)) = _
    rw [smul_smul]
  rw [hleft]
  apply Fintype.sum_equiv (optMulLabelEquiv Q)
  intro P
  simp [pauliCommutatorResponseCoefficient, optMulLabelEquiv,
    optMulLabel_optMulLabel_self]

theorem frobSq_pauli_commutator_sum
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → Option (Fin 3))
    (J : (σ → Option (Fin 3)) → ℂ) :
    frobSq
        (finitePauliMatrix Q * (∑ P, J P • finitePauliMatrix P) -
          (∑ P, J P • finitePauliMatrix P) * finitePauliMatrix Q) =
      2 ^ Fintype.card σ *
        ∑ P, ‖J P‖ ^ (2 : ℕ) * ‖optPhaseProd Q P - optPhaseProd P Q‖ ^ (2 : ℕ) := by
  rw [pauli_commutator_sum_eq_response, frobSq_pauliCombination]
  congr 1
  apply Fintype.sum_equiv (optMulLabelEquiv Q).symm
  intro P
  simp [pauliCommutatorResponseCoefficient, optMulLabelEquiv,
    mul_pow]

theorem norm_phaseDifference_sq_eq_indicator
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q P : σ → Option (Fin 3)) :
    ‖optPhaseProd Q P - optPhaseProd P Q‖ ^ (2 : ℕ) =
      if finitePauliConjugationSign Q P = -1 then 4 else 0 := by
  by_cases hanti : finitePauliConjugationSign Q P = -1
  · rw [if_pos hanti,
      norm_optPhaseProd_sub_swap_of_conjugationSign_eq_neg_one hanti]
    norm_num
  · rw [if_neg hanti]
    have hsq : finitePauliConjugationSign Q P ^ (2 : ℕ) = 1 := by
      simpa [pow_two] using finitePauliConjugationSign_sq Q P
    have hone : finitePauliConjugationSign Q P = 1 := by
      rcases (sq_eq_one_iff.mp hsq) with h | h
      · exact h
      · exact False.elim (hanti h)
    rw [optPhaseProd_eq_conjugationSign_mul_swap, hone]
    simp

theorem four_mul_pauliAnticommutingIncidenceMass_le_phaseEnergy
    {n q : ℕ}
    (J : (Fin n → Option (Fin 3)) → ℂ)
    (Q : boundedLocalPauliLabel n q) :
    4 * pauliAnticommutingIncidenceMass
          (fun P => ‖J P.1‖ ^ (2 : ℕ)) Q ≤
      ∑ P : Fin n → Option (Fin 3),
        ‖J P‖ ^ (2 : ℕ) * ‖optPhaseProd Q.1 P - optPhaseProd P Q.1‖ ^ (2 : ℕ) := by
  let nz : Finset (Fin n → Option (Fin 3)) :=
    Finset.univ.filter fun P => P ≠ pauliCharacterZero
  let energy : (Fin n → Option (Fin 3)) → ℝ := fun P =>
    ‖J P‖ ^ (2 : ℕ) * ‖optPhaseProd Q.1 P - optPhaseProd P Q.1‖ ^ (2 : ℕ)
  have hsub :
      (∑ P ∈ nz, energy P) =
        ∑ P : NonzeroPauliCharacter (Fin n), energy P.1 := by
    exact Finset.sum_subtype nz (by simp [nz]) energy
  have hnonneg : ∀ P, 0 ≤ energy P := fun P =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    4 * pauliAnticommutingIncidenceMass
          (fun P => ‖J P.1‖ ^ (2 : ℕ)) Q =
        ∑ P : NonzeroPauliCharacter (Fin n), energy P.1 := by
      rw [pauliAnticommutingIncidenceMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      rw [show energy P.1 = ‖J P.1‖ ^ (2 : ℕ) *
          (if finitePauliConjugationSign Q.1 P.1 = -1 then 4 else 0) by
        simp only [energy]
        rw [norm_phaseDifference_sq_eq_indicator]]
      by_cases hanti : finitePauliConjugationSign Q.1 P.1 = -1 <;>
        simp [hanti] <;> ring
    _ = ∑ P ∈ nz, energy P := hsub.symm
    _ ≤ ∑ P, energy P := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [nz])
        (fun P _ _ => hnonneg P)
    _ = ∑ P : Fin n → Option (Fin 3),
        ‖J P‖ ^ (2 : ℕ) * ‖optPhaseProd Q.1 P - optPhaseProd P Q.1‖ ^ (2 : ℕ) := rfl

/-- Exact form of the incidence law.  The apparent inequality above comes
only from retaining the scalar Pauli label; its phase energy vanishes exactly,
so non-scalar anticommutation incidence is the full commutator energy. -/
theorem four_mul_pauliAnticommutingIncidenceMass_eq_phaseEnergy
    {n q : ℕ}
    (J : (Fin n → Option (Fin 3)) → ℂ)
    (Q : boundedLocalPauliLabel n q) :
    4 * pauliAnticommutingIncidenceMass
          (fun P => ‖J P.1‖ ^ (2 : ℕ)) Q =
      ∑ P : Fin n → Option (Fin 3),
        ‖J P‖ ^ (2 : ℕ) * ‖optPhaseProd Q.1 P - optPhaseProd P Q.1‖ ^ (2 : ℕ) := by
  let nz : Finset (Fin n → Option (Fin 3)) :=
    Finset.univ.filter fun P => P ≠ pauliCharacterZero
  let energy : (Fin n → Option (Fin 3)) → ℝ := fun P =>
    ‖J P‖ ^ (2 : ℕ) * ‖optPhaseProd Q.1 P - optPhaseProd P Q.1‖ ^ (2 : ℕ)
  have hsub :
      (∑ P ∈ nz, energy P) =
        ∑ P : NonzeroPauliCharacter (Fin n), energy P.1 := by
    exact Finset.sum_subtype nz (by simp [nz]) energy
  have hfull : (∑ P, energy P) = ∑ P ∈ nz, energy P := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro P _ hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      not_ne_iff] at hP
    subst P
    have hsign : finitePauliConjugationSign Q.1
        (pauliCharacterZero (σ := Fin n)) = 1 := by
      rw [finitePauliConjugationSign]
      apply Finset.prod_eq_one
      intro s _
      simp [pauliCharacterZero, boolPauliConjugationSign]
    rw [show energy pauliCharacterZero =
        ‖J pauliCharacterZero‖ ^ (2 : ℕ) *
          (if finitePauliConjugationSign Q.1 pauliCharacterZero = -1
            then 4 else 0) by
      simp only [energy]
      rw [norm_phaseDifference_sq_eq_indicator]]
    rw [hsign]
    norm_num
  calc
    4 * pauliAnticommutingIncidenceMass
          (fun P => ‖J P.1‖ ^ (2 : ℕ)) Q =
        ∑ P : NonzeroPauliCharacter (Fin n), energy P.1 := by
      rw [pauliAnticommutingIncidenceMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      rw [show energy P.1 = ‖J P.1‖ ^ (2 : ℕ) *
          (if finitePauliConjugationSign Q.1 P.1 = -1 then 4 else 0) by
        simp only [energy]
        rw [norm_phaseDifference_sq_eq_indicator]]
      by_cases hanti : finitePauliConjugationSign Q.1 P.1 = -1 <;>
        simp [hanti] <;> ring
    _ = ∑ P ∈ nz, energy P := hsub.symm
    _ = ∑ P, energy P := hfull.symm

/-- Exact target-specific total energy law.  This retains the complete Pauli
incidence profile instead of replacing it by its worst-target lower bound. -/
theorem boundedLocalPauli_total_commutator_energy_eq_incidenceMass
    {n q : ℕ}
    (J : (Fin n → Option (Fin 3)) → ℂ) :
    (∑ Q : boundedLocalPauliLabel n q,
        frobSq
          (finitePauliMatrix Q.1 * (∑ P, J P • finitePauliMatrix P) -
            (∑ P, J P • finitePauliMatrix P) * finitePauliMatrix Q.1)) =
      4 * (2 : ℝ) ^ n *
        ∑ Q : boundedLocalPauliLabel n q,
          pauliAnticommutingIncidenceMass
            (fun P => ‖J P.1‖ ^ (2 : ℕ)) Q := by
  calc
    (∑ Q : boundedLocalPauliLabel n q,
        frobSq
          (finitePauliMatrix Q.1 * (∑ P, J P • finitePauliMatrix P) -
            (∑ P, J P • finitePauliMatrix P) * finitePauliMatrix Q.1)) =
      ∑ Q : boundedLocalPauliLabel n q,
        (2 : ℝ) ^ n *
          (4 * pauliAnticommutingIncidenceMass
            (fun P => ‖J P.1‖ ^ (2 : ℕ)) Q) := by
      apply Finset.sum_congr rfl
      intro Q _
      rw [frobSq_pauli_commutator_sum]
      simp only [Fintype.card_fin]
      rw [four_mul_pauliAnticommutingIncidenceMass_eq_phaseEnergy]
    _ = 4 * (2 : ℝ) ^ n *
        ∑ Q : boundedLocalPauliLabel n q,
          pauliAnticommutingIncidenceMass
            (fun P => ‖J P.1‖ ^ (2 : ℕ)) Q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      ring

theorem boundedLocalPauli_total_commutator_energy_matrix_eq_incidenceMass
    {n q : ℕ}
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (∑ Q : boundedLocalPauliLabel n q,
        frobSq
          (finitePauliMatrix Q.1 * A - A * finitePauliMatrix Q.1)) =
      4 * (2 : ℝ) ^ n *
        ∑ Q : boundedLocalPauliLabel n q,
          pauliAnticommutingIncidenceMass
            (fun P => ‖pauliCoeff A P.1‖ ^ (2 : ℕ)) Q := by
  simpa only [sum_pauliCoeff_smul] using
    boundedLocalPauli_total_commutator_energy_eq_incidenceMass
      (q := q) (pauliCoeff A)

/-- Every arbitrary Pauli coefficient profile pays a dimension-linear total
commutator energy against the complete bounded-local dictionary, measured by
its non-scalar Hilbert--Schmidt mass. -/
theorem boundedLocalPauli_total_commutator_energy_ge
    {n q : ℕ} (hq : 2 ≤ q)
    (J : (Fin n → Option (Fin 3)) → ℂ) :
    4 * (2 : ℝ) ^ n * ((n - 1 : ℕ) : ℝ) *
        ∑ P : NonzeroPauliCharacter (Fin n), ‖J P.1‖ ^ (2 : ℕ) ≤
      ∑ Q : boundedLocalPauliLabel n q,
        frobSq
          (finitePauliMatrix Q.1 * (∑ P, J P • finitePauliMatrix P) -
            (∑ P, J P • finitePauliMatrix P) * finitePauliMatrix Q.1) := by
  let mass : NonzeroPauliCharacter (Fin n) → ℝ := fun P => ‖J P.1‖ ^ (2 : ℕ)
  have hinc := total_pauliAnticommutingIncidenceMass_ge hq mass
    (fun P => sq_nonneg ‖J P.1‖)
  have hscale_nonneg : 0 ≤ 4 * (2 : ℝ) ^ n := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hinc hscale_nonneg
  calc
    4 * (2 : ℝ) ^ n * ((n - 1 : ℕ) : ℝ) *
          ∑ P : NonzeroPauliCharacter (Fin n), ‖J P.1‖ ^ (2 : ℕ) =
        (4 * (2 : ℝ) ^ n) *
          (((n - 1 : ℕ) : ℝ) * ∑ P, mass P) := by
      simp only [mass]
      ring
    _ ≤ (4 * (2 : ℝ) ^ n) *
        ∑ Q : boundedLocalPauliLabel n q,
          pauliAnticommutingIncidenceMass mass Q := hscaled
    _ = ∑ Q : boundedLocalPauliLabel n q,
        (2 : ℝ) ^ n *
          (4 * pauliAnticommutingIncidenceMass mass Q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      ring
    _ ≤ ∑ Q : boundedLocalPauliLabel n q,
        frobSq
          (finitePauliMatrix Q.1 * (∑ P, J P • finitePauliMatrix P) -
            (∑ P, J P • finitePauliMatrix P) * finitePauliMatrix Q.1) := by
      apply Finset.sum_le_sum
      intro Q _
      rw [frobSq_pauli_commutator_sum]
      simp only [Fintype.card_fin]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [mass] using
        four_mul_pauliAnticommutingIncidenceMass_le_phaseEnergy J Q

/-- Coordinate-free form: the law applies to every operator after expanding
it in the Pauli basis. -/
theorem boundedLocalPauli_total_commutator_energy_matrix_ge
    {n q : ℕ} (hq : 2 ≤ q)
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    4 * (2 : ℝ) ^ n * ((n - 1 : ℕ) : ℝ) *
        ∑ P : NonzeroPauliCharacter (Fin n), ‖pauliCoeff A P.1‖ ^ (2 : ℕ) ≤
      ∑ Q : boundedLocalPauliLabel n q,
        frobSq
          (finitePauliMatrix Q.1 * A - A * finitePauliMatrix Q.1) := by
  simpa only [sum_pauliCoeff_smul] using
    boundedLocalPauli_total_commutator_energy_ge hq (pauliCoeff A)

end

end GaloisForLFunctions.HTGeometry
