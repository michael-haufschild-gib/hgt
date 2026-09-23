import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.HTGeometry.EnergyMatchedEigenframeSourceMemory
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

structure FiniteEigenstate (ι : Type*) [Fintype ι] where
  mass : ι → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  sum_mass : ∑ i, mass i = 1

def inverseParticipationRatioTwo {ι : Type*} [Fintype ι]
    (ψ : FiniteEigenstate ι) : ℝ :=
  ∑ i, (ψ.mass i) ^ (2 : ℕ)

theorem eigenstate_mass_le_one {ι : Type*} [Fintype ι]
    (ψ : FiniteEigenstate ι) (i : ι) : ψ.mass i ≤ 1 := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := ψ.mass)
    (fun j _ => ψ.mass_nonneg j) (Finset.mem_univ i)
  simpa [ψ.sum_mass] using h

theorem inverseParticipationRatioTwo_le_one {ι : Type*} [Fintype ι]
    (ψ : FiniteEigenstate ι) : inverseParticipationRatioTwo ψ ≤ 1 := by
  calc
    inverseParticipationRatioTwo ψ ≤ ∑ i, ψ.mass i := by
      unfold inverseParticipationRatioTwo
      apply Finset.sum_le_sum
      intro i _
      nlinarith [ψ.mass_nonneg i, eigenstate_mass_le_one ψ i]
    _ = 1 := ψ.sum_mass

theorem one_div_card_le_inverseParticipationRatioTwo
    {ι : Type*} [Fintype ι] [Nonempty ι] (ψ : FiniteEigenstate ι) :
    1 / (Fintype.card ι : ℝ) ≤ inverseParticipationRatioTwo ψ := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  have hcs : (∑ i, ψ.mass i) ^ (2 : ℕ) ≤
      (Fintype.card ι : ℝ) * ∑ i, (ψ.mass i) ^ (2 : ℕ) := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := ψ.mass))
  rw [ψ.sum_mass] at hcs
  apply (div_le_iff₀ hcard).2
  simpa [inverseParticipationRatioTwo, mul_comm] using hcs

theorem inverseParticipationRatioTwo_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] (ψ : FiniteEigenstate ι) :
    0 < inverseParticipationRatioTwo ψ := by
  have hlower := one_div_card_le_inverseParticipationRatioTwo ψ
  exact lt_of_lt_of_le (by positivity) hlower

structure MultifractalEigenstate (ι : Type*) [Fintype ι] extends FiniteEigenstate ι where
  card_gt_one : 1 < Fintype.card ι

def correlationDimensionTwo {ι : Type*} [Fintype ι]
    (ψ : MultifractalEigenstate ι) : ℝ :=
  -Real.log (inverseParticipationRatioTwo ψ.toFiniteEigenstate) /
    Real.log (Fintype.card ι : ℝ)

theorem correlationDimensionTwo_nonneg {ι : Type*} [Fintype ι]
    (ψ : MultifractalEigenstate ι) : 0 ≤ correlationDimensionTwo ψ := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt ψ.card_gt_one)
  have hipr0 := inverseParticipationRatioTwo_pos ψ.toFiniteEigenstate
  have hipr1 := inverseParticipationRatioTwo_le_one ψ.toFiniteEigenstate
  have hlogCard : 0 < Real.log (Fintype.card ι : ℝ) := by
    apply Real.log_pos
    exact_mod_cast ψ.card_gt_one
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hipr0.le hipr1)) hlogCard.le

theorem correlationDimensionTwo_le_one {ι : Type*} [Fintype ι]
    (ψ : MultifractalEigenstate ι) : correlationDimensionTwo ψ ≤ 1 := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt ψ.card_gt_one)
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  have hlogCard : 0 < Real.log (Fintype.card ι : ℝ) := by
    apply Real.log_pos
    exact_mod_cast ψ.card_gt_one
  have hipr0 := inverseParticipationRatioTwo_pos ψ.toFiniteEigenstate
  have hlower := one_div_card_le_inverseParticipationRatioTwo ψ.toFiniteEigenstate
  have hlog := Real.log_le_log (by positivity : 0 < 1 / (Fintype.card ι : ℝ)) hlower
  rw [show (1 / (Fintype.card ι : ℝ)) = (Fintype.card ι : ℝ)⁻¹ by rw [one_div],
    Real.log_inv] at hlog
  unfold correlationDimensionTwo
  apply (div_le_iff₀ hlogCard).2
  linarith

theorem correlationDimensionTwo_mem_unitInterval {ι : Type*} [Fintype ι]
    (ψ : MultifractalEigenstate ι) : correlationDimensionTwo ψ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨correlationDimensionTwo_nonneg ψ, correlationDimensionTwo_le_one ψ⟩

structure NonzeroCoefficientVector (ι : Type*) [Fintype ι] where
  coefficient : ι → ℝ
  coefficient_ne_zero : coefficient ≠ 0

def coefficientEigenstate {ι : Type*} [Fintype ι]
    (h : NonzeroCoefficientVector ι) : FiniteEigenstate ι where
  mass i := |h.coefficient i| / finiteCoefficientL1Mass h.coefficient
  mass_nonneg i := div_nonneg (abs_nonneg _) (finiteCoefficientL1Mass_pos _ h.coefficient_ne_zero).le
  sum_mass := by
    rw [← Finset.sum_div]
    unfold finiteCoefficientL1Mass
    exact div_self (finiteCoefficientL1Mass_pos _ h.coefficient_ne_zero).ne'

theorem inverseParticipationRatioTwo_coefficientEigenstate
    {ι : Type*} [Fintype ι] (h : NonzeroCoefficientVector ι) :
    inverseParticipationRatioTwo (coefficientEigenstate h) =
      (∑ i, (h.coefficient i) ^ (2 : ℕ)) / (finiteCoefficientL1Mass h.coefficient) ^ (2 : ℕ) := by
  unfold inverseParticipationRatioTwo
  change (∑ i, (|h.coefficient i| / finiteCoefficientL1Mass h.coefficient) ^ (2 : ℕ)) = _
  calc
    (∑ i, (|h.coefficient i| / finiteCoefficientL1Mass h.coefficient) ^ (2 : ℕ)) =
        ∑ i, (h.coefficient i) ^ (2 : ℕ) / (finiteCoefficientL1Mass h.coefficient) ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [div_pow, sq_abs]
    _ = (∑ i, (h.coefficient i) ^ (2 : ℕ)) /
        (finiteCoefficientL1Mass h.coefficient) ^ (2 : ℕ) := by
      rw [Finset.sum_div]

structure FixedTransferCoordinate (σ ι : Type*)
    [Fintype σ] [DecidableEq σ] [Fintype ι] where
  label : ι → σ → Option (Fin 3)
  coefficient : NonzeroCoefficientVector ι
  evolution : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ
  fixed : dictionaryPauliTransfer label evolution *ᵥ coefficient.coefficient =
    coefficient.coefficient

theorem energyMatchedEigenframeAmplitude_eq_inverseParticipationRatioTwo
    {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
    (coordinate : FixedTransferCoordinate σ ι) :
    energyMatchedEigenframeAmplitude coordinate.label coordinate.coefficient.coefficient
        coordinate.evolution =
      inverseParticipationRatioTwo (coefficientEigenstate coordinate.coefficient) := by
  rw [energyMatchedEigenframeAmplitude_eq_of_fixed _ _ _ coordinate.fixed,
    inverseParticipationRatioTwo_coefficientEigenstate]

end

end GaloisForLFunctions.HTGeometry.RandomMixedGraph

