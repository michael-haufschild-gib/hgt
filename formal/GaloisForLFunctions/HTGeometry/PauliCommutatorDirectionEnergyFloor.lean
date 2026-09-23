import GaloisForLFunctions.HTGeometry.PauliScalarDistanceCommutatorLaw
import GaloisForLFunctions.HTGeometry.GaussianStableRankTraceCapCompiler
import GaloisForLFunctions.HTGeometry.FiniteUnitaryAdjointAutocorrelationLaw

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def boundedLocalPauliCommutatorWeight
    {n q : ℕ}
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (Q : boundedLocalPauliLabel n q) : ℝ :=
  frobSq (finitePauliMatrix Q.1 * A - A * finitePauliMatrix Q.1)

theorem boundedLocalPauliCommutatorWeight_nonneg
    {n q : ℕ}
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (Q : boundedLocalPauliLabel n q) :
    0 ≤ boundedLocalPauliCommutatorWeight A Q := by
  exact frobSq_nonneg _

theorem boundedLocalPauliCommutatorWeight_le
    {n q : ℕ}
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (Q : boundedLocalPauliLabel n q) :
    boundedLocalPauliCommutatorWeight A Q ≤ 4 * frobSq A := by
  rw [boundedLocalPauliCommutatorWeight, ← sum_pauliCoeff_smul A,
    frobSq_pauli_commutator_sum]
  simp only [Fintype.card_fin]
  rw [frobSq_pauliCombination]
  simp only [Fintype.card_fin]
  calc
    (2 : ℝ) ^ n *
        ∑ P, ‖pauliCoeff A P‖ ^ (2 : ℕ) *
          ‖optPhaseProd Q.1 P - optPhaseProd P Q.1‖ ^ (2 : ℕ) ≤
        (2 : ℝ) ^ n * (4 * ∑ P, ‖pauliCoeff A P‖ ^ (2 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro P _
      rw [norm_phaseDifference_sq_eq_indicator]
      by_cases hanti : finitePauliConjugationSign Q.1 P = -1
      · simpa [hanti, mul_comm]
      · simp [hanti]
    _ = 4 * ((2 : ℝ) ^ n * ∑ P, ‖pauliCoeff A P‖ ^ (2 : ℕ)) := by ring

def boundedLocalPauliCommutatorDirectionEnergyRatio
    {n q : ℕ}
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) : ℝ :=
  (∑ Q : boundedLocalPauliLabel n q,
      boundedLocalPauliCommutatorWeight A Q) ^ (2 : ℕ) /
    ∑ Q : boundedLocalPauliLabel n q,
      boundedLocalPauliCommutatorWeight A Q ^ (2 : ℕ)

theorem boundedLocalPauliCommutatorDirectionEnergyRatio_nonneg
    {n q : ℕ}
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    0 ≤ boundedLocalPauliCommutatorDirectionEnergyRatio (q := q) A := by
  rw [boundedLocalPauliCommutatorDirectionEnergyRatio]
  exact div_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun Q _ => sq_nonneg _)

/-- Unconditional direction-energy dispersion law for the ordinary two-local
Pauli dictionary. This diagonal weight ratio is not the Gram stable rank unless
the response directions are orthogonal; the correlated Gram theorem is proved
separately. -/
theorem twoLocalPauliCommutatorDirectionEnergyRatio_ge
    {n : ℕ}
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((n - 1 : ℕ) : ℝ) * frobSq (A - pauliScalarPart A) / frobSq A ≤
      boundedLocalPauliCommutatorDirectionEnergyRatio (q := 2) A := by
  let distance := frobSq (A - pauliScalarPart A)
  by_cases hdistance : distance = 0
  · change ((n - 1 : ℕ) : ℝ) * distance / frobSq A ≤ _
    rw [hdistance, mul_zero, zero_div]
    exact boundedLocalPauliCommutatorDirectionEnergyRatio_nonneg A
  have hdistancePos : 0 < distance :=
    lt_of_le_of_ne (frobSq_nonneg _) (Ne.symm hdistance)
  have hdistanceLe : distance ≤ frobSq A := by
    simpa [distance] using
      pauliScalarPart_minimizes_frobSq_scalarDistance A 0
  have hAPos : 0 < frobSq A := hdistancePos.trans_le hdistanceLe
  by_cases hn : n ≤ 1
  · have hz : n - 1 = 0 := by omega
    change ((n - 1 : ℕ) : ℝ) * distance / frobSq A ≤ _
    rw [hz, Nat.cast_zero, zero_mul, zero_div]
    exact boundedLocalPauliCommutatorDirectionEnergyRatio_nonneg A
  have hnPos : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (by omega : 1 < n))
  have hmassPos :
      0 < 4 * ((n - 1 : ℕ) : ℝ) * distance := by positivity
  have hcapPos : 0 < 4 * frobSq A := by positivity
  have hmass :
      4 * ((n - 1 : ℕ) : ℝ) * distance ≤
        ∑ Q : boundedLocalPauliLabel n 2,
          boundedLocalPauliCommutatorWeight A Q := by
    simpa [distance, boundedLocalPauliCommutatorWeight] using
      boundedLocalPauli_commutator_energy_ge_scalarDistance
        (n := n) (q := 2) (by omega) A
  have hratio := weightedStableRatio_ge_mass_div_cap
    (fun Q : boundedLocalPauliLabel n 2 =>
      boundedLocalPauliCommutatorWeight A Q)
    (boundedLocalPauliCommutatorWeight_nonneg A)
    hmassPos hcapPos hmass
    (boundedLocalPauliCommutatorWeight_le A)
  change ((n - 1 : ℕ) : ℝ) * distance / frobSq A ≤ _
  rw [boundedLocalPauliCommutatorDirectionEnergyRatio]
  convert hratio using 1
  field_simp [ne_of_gt hAPos]
  <;> ring

theorem frobSq_unitaryGroup_finiteQubit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    frobSq (U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) = (2 : ℝ) ^ n := by
  rw [frobSq]
  calc
    (∑ a, ∑ b, ‖(U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) a b‖ ^ (2 : ℕ)) =
        ∑ a, ∑ b, finiteUnitaryEntryWeight U a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp [finiteUnitaryEntryWeight, Complex.sq_norm]
    _ = ∑ _a : FiniteQubitConfiguration (Fin n), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      exact sum_finiteUnitaryEntryWeight_row U a
    _ = (2 : ℝ) ^ n := by
      simp [FiniteQubitConfiguration]

theorem norm_pauliScalarCoefficient_sq_eq_normalizedTrace
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    ‖pauliCoeff A pauliCharacterZero‖ ^ (2 : ℕ) =
      ‖Matrix.trace A‖ ^ (2 : ℕ) / ((2 : ℝ) ^ Fintype.card σ) ^ (2 : ℕ) := by
  rw [trace_eq_card_mul_pauliScalarCoefficient, norm_mul, norm_pow]
  norm_num
  have hpow : (0 : ℝ) < (2 : ℝ) ^ Fintype.card σ := by positivity
  field_simp

theorem unitary_pauliCoeff_total_mass_eq_one
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    (∑ P : Fin n → Option (Fin 3),
        ‖pauliCoeff (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) P‖ ^ (2 : ℕ)) = 1 := by
  let A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ := U
  have hparseval := frobSq_pauliCombination (pauliCoeff A)
  rw [sum_pauliCoeff_smul A, frobSq_unitaryGroup_finiteQubit U] at hparseval
  simp only [Fintype.card_fin] at hparseval
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  nlinarith

theorem unitary_nonzero_pauliCoeff_mass_eq_traceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    (∑ P : NonzeroPauliCharacter (Fin n),
        ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ)) =
      1 - ‖pauliCoeff
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)
        pauliCharacterZero‖ ^ (2 : ℕ) := by
  let A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ := U
  have hsplit := sum_norm_pauliScalarShiftCoefficient_sq
    (pauliCoeff A) 0
  simp only [pauliScalarShiftCoefficient, sub_zero, ite_self] at hsplit
  have htotal : (∑ P : Fin n → Option (Fin 3), ‖pauliCoeff A P‖ ^ (2 : ℕ)) = 1 :=
    unitary_pauliCoeff_total_mass_eq_one U
  simp only [A] at hsplit htotal ⊢
  rw [htotal] at hsplit
  linarith

theorem unitary_scalarDistance_ratio_eq_traceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    frobSq
        ((U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) -
          pauliScalarPart
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)) /
        frobSq (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) =
      1 - ‖pauliCoeff
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)
        pauliCharacterZero‖ ^ (2 : ℕ) := by
  let A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ := U
  have hnonzero :
      (∑ P : NonzeroPauliCharacter (Fin n), ‖pauliCoeff A P.1‖ ^ (2 : ℕ)) =
        1 - ‖pauliCoeff A pauliCharacterZero‖ ^ (2 : ℕ) := by
    simpa only [A] using unitary_nonzero_pauliCoeff_mass_eq_traceDeficit U
  rw [frobSq_sub_pauliScalarPart, frobSq_unitaryGroup_finiteQubit U]
  simp only [Fintype.card_fin, A] at hnonzero ⊢
  rw [hnonzero]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  field_simp

/-- Closed two-local unitary form of the diagonal direction-energy law. -/
theorem twoLocalPauliCommutatorDirectionEnergyRatio_unitary_ge_traceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((n - 1 : ℕ) : ℝ) *
        (1 - ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
          pauliCharacterZero‖ ^ (2 : ℕ)) ≤
      boundedLocalPauliCommutatorDirectionEnergyRatio (q := 2)
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) := by
  rw [← unitary_scalarDistance_ratio_eq_traceDeficit U]
  simpa [mul_div_assoc] using
    twoLocalPauliCommutatorDirectionEnergyRatio_ge
      (U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)

/-- Physical normalized-trace form of the diagonal direction-energy law. -/
theorem twoLocalPauliCommutatorDirectionEnergyRatio_unitary_ge_normalizedTraceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((n - 1 : ℕ) : ℝ) *
        (1 - ‖Matrix.trace
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
          ((2 : ℝ) ^ n) ^ (2 : ℕ)) ≤
      boundedLocalPauliCommutatorDirectionEnergyRatio (q := 2)
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) := by
  have htrace := norm_pauliScalarCoefficient_sq_eq_normalizedTrace
    (U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
  simp only [Fintype.card_fin] at htrace
  rw [← htrace]
  exact twoLocalPauliCommutatorDirectionEnergyRatio_unitary_ge_traceDeficit U

end

end GaloisForLFunctions.HTGeometry
