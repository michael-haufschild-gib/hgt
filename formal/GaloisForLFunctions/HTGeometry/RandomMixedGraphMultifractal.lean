import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.HTGeometry.EnergyMatchedEigenframeSourceMemory
import Mathlib.Algebra.Order.Chebyshev

/-!
# Inverse participation ratio and correlation dimension of finite eigenstates

A finite eigenstate is a probability vector `p` on a finite index set `ι`. Its second inverse
participation ratio `IPR₂ = ∑ pᵢ²` satisfies `1 / |ι| ≤ IPR₂ ≤ 1` (Cauchy-Schwarz and `pᵢ ≤ 1`),
so the correlation dimension `D₂ = -log IPR₂ / log |ι|` lies in `[0, 1]` once `|ι| > 1`. A nonzero
real coefficient vector `h` defines the eigenstate `pᵢ = |hᵢ| / ‖h‖₁` with `IPR₂ = ‖h‖₂² / ‖h‖₁²`,
and for a coefficient vector fixed by the dictionary Pauli-transfer matrix of an evolution `U`,
the energy-matched eigenframe statistic equals this inverse participation ratio.

## Main results

- `one_div_card_le_inverseParticipationRatioTwo`, `inverseParticipationRatioTwo_le_one`:
  `1 / |ι| ≤ ∑ pᵢ² ≤ 1`.
- `correlationDimensionTwo_mem_unitInterval`: `D₂ ∈ [0, 1]` for a probability vector on more
  than one point.
- `inverseParticipationRatioTwo_coefficientEigenstate`: `IPR₂` of the `ℓ¹`-normalized state of
  `h` is `‖h‖₂² / ‖h‖₁²`.
- `energyMatchedEigenframeAmplitude_eq_inverseParticipationRatioTwo`: for a fixed transfer
  coordinate, the energy-matched eigenframe amplitude equals that `IPR₂`.

## Hypotheses

Unconditional. The structures `FiniteEigenstate`, `MultifractalEigenstate`,
`NonzeroCoefficientVector` and `FixedTransferCoordinate` carry their defining data: nonnegative
masses summing to 1, `1 < |ι|`, a nonzero coefficient vector, and the fixed-point equation
`T h = h` for the dictionary Pauli-transfer matrix `T` of `U`.
-/

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

/-- A finite eigenstate profile: a probability vector `mass` on the finite index set `ι`. -/
structure FiniteEigenstate (ι : Type*) [Fintype ι] where
  mass : ι → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  sum_mass : ∑ i, mass i = 1

/-- Second inverse participation ratio `IPR₂ = ∑ pᵢ²` of a finite probability vector. -/
def inverseParticipationRatioTwo {ι : Type*} [Fintype ι]
    (ψ : FiniteEigenstate ι) : ℝ :=
  ∑ i, (ψ.mass i) ^ (2 : ℕ)

/-- Each mass of a probability vector is at most 1. -/
theorem eigenstate_mass_le_one {ι : Type*} [Fintype ι]
    (ψ : FiniteEigenstate ι) (i : ι) : ψ.mass i ≤ 1 := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := ψ.mass)
    (fun j _ => ψ.mass_nonneg j) (Finset.mem_univ i)
  simpa [ψ.sum_mass] using h

/-- `IPR₂ ≤ 1`, since `pᵢ² ≤ pᵢ` and the masses sum to 1. -/
theorem inverseParticipationRatioTwo_le_one {ι : Type*} [Fintype ι]
    (ψ : FiniteEigenstate ι) : inverseParticipationRatioTwo ψ ≤ 1 := by
  calc
    inverseParticipationRatioTwo ψ ≤ ∑ i, ψ.mass i := by
      unfold inverseParticipationRatioTwo
      apply Finset.sum_le_sum
      intro i _
      nlinarith [ψ.mass_nonneg i, eigenstate_mass_le_one ψ i]
    _ = 1 := ψ.sum_mass

/-- Cauchy-Schwarz lower bound `1 / |ι| ≤ IPR₂` on a nonempty finite index set. -/
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

/-- `IPR₂` is strictly positive on a nonempty index set. -/
theorem inverseParticipationRatioTwo_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] (ψ : FiniteEigenstate ι) :
    0 < inverseParticipationRatioTwo ψ := by
  have hlower := one_div_card_le_inverseParticipationRatioTwo ψ
  exact lt_of_lt_of_le (by positivity) hlower

/-- A finite eigenstate on an index set with more than one point, so `log |ι| > 0`. -/
structure MultifractalEigenstate (ι : Type*) [Fintype ι] extends FiniteEigenstate ι where
  card_gt_one : 1 < Fintype.card ι

/-- Correlation dimension `D₂ = -log IPR₂ / log |ι|`. -/
def correlationDimensionTwo {ι : Type*} [Fintype ι]
    (ψ : MultifractalEigenstate ι) : ℝ :=
  -Real.log (inverseParticipationRatioTwo ψ.toFiniteEigenstate) /
    Real.log (Fintype.card ι : ℝ)

/-- `D₂ ≥ 0`, from `IPR₂ ≤ 1`. -/
theorem correlationDimensionTwo_nonneg {ι : Type*} [Fintype ι]
    (ψ : MultifractalEigenstate ι) : 0 ≤ correlationDimensionTwo ψ := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt ψ.card_gt_one)
  have hipr0 := inverseParticipationRatioTwo_pos ψ.toFiniteEigenstate
  have hipr1 := inverseParticipationRatioTwo_le_one ψ.toFiniteEigenstate
  have hlogCard : 0 < Real.log (Fintype.card ι : ℝ) := by
    apply Real.log_pos
    exact_mod_cast ψ.card_gt_one
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hipr0.le hipr1)) hlogCard.le

/-- `D₂ ≤ 1`, from `1 / |ι| ≤ IPR₂`. -/
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

/-- The correlation dimension lies in the unit interval `[0, 1]`. -/
theorem correlationDimensionTwo_mem_unitInterval {ι : Type*} [Fintype ι]
    (ψ : MultifractalEigenstate ι) : correlationDimensionTwo ψ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨correlationDimensionTwo_nonneg ψ, correlationDimensionTwo_le_one ψ⟩

/-- A nonzero real coefficient vector on a finite index set. -/
structure NonzeroCoefficientVector (ι : Type*) [Fintype ι] where
  coefficient : ι → ℝ
  coefficient_ne_zero : coefficient ≠ 0

/-- The probability vector `pᵢ = |hᵢ| / ‖h‖₁` attached to a nonzero coefficient vector `h`. -/
def coefficientEigenstate {ι : Type*} [Fintype ι]
    (h : NonzeroCoefficientVector ι) : FiniteEigenstate ι where
  mass i := |h.coefficient i| / finiteCoefficientL1Mass h.coefficient
  mass_nonneg i := div_nonneg (abs_nonneg _) (finiteCoefficientL1Mass_pos _ h.coefficient_ne_zero).le
  sum_mass := by
    rw [← Finset.sum_div]
    unfold finiteCoefficientL1Mass
    exact div_self (finiteCoefficientL1Mass_pos _ h.coefficient_ne_zero).ne'

/-- `IPR₂` of the `ℓ¹`-normalized coefficient state equals `‖h‖₂² / ‖h‖₁²`. -/
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

/-- A Pauli dictionary `label`, a nonzero coefficient vector `h` and an evolution `U` whose
dictionary Pauli-transfer matrix fixes `h`. -/
structure FixedTransferCoordinate (σ ι : Type*)
    [Fintype σ] [DecidableEq σ] [Fintype ι] where
  label : ι → σ → Option (Fin 3)
  coefficient : NonzeroCoefficientVector ι
  evolution : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ
  fixed : dictionaryPauliTransfer label evolution *ᵥ coefficient.coefficient =
    coefficient.coefficient

/-- For a fixed transfer coordinate, the energy-matched eigenframe amplitude equals the inverse
participation ratio `‖h‖₂² / ‖h‖₁²` of the coefficient state. -/
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

