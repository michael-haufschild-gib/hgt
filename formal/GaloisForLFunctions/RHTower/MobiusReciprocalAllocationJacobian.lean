import GaloisForLFunctions.RHTower.MobiusFixedTokenReservoirConservation

/-!
# Reciprocal allocation and square-root Jacobian cancellation

This module formalizes the exact finite probability and Jacobian core of the Route E reciprocal
allocation law.  Allocation representations are retained rather than quotiented: coincident
physical terminals receive the sum of all representation weights.  Reciprocal allocation mass
then gives an exactly stochastic row kernel.  The companion algebraic theorem proves exact
cancellation between a square-root forward token law and its inverse physical Jacobian, and
identifies exponent one as the unique scale-neutral reciprocal tilt.
-/

namespace RHTower

open Finset

/-- Finite allocation data with positive allocation scales and nonempty physical terminal fibres. -/
structure ReciprocalAllocationSystem
    (Anchor Allocation Target : Type*) [Fintype Target] [DecidableEq Target] where
  admissible : Anchor → Finset Allocation
  terminals : Anchor → Allocation → Finset Target
  scale : Allocation → ℝ
  scale_pos : ∀ ρ, 0 < scale ρ
  admissible_nonempty : ∀ n, (admissible n).Nonempty
  terminals_nonempty : ∀ n ρ, ρ ∈ admissible n → (terminals n ρ).Nonempty

namespace ReciprocalAllocationSystem

variable {Anchor Allocation Target : Type*}
  [Fintype Target] [DecidableEq Target]
  (A : ReciprocalAllocationSystem Anchor Allocation Target)

/-- Harmonic normalizer of all admissible allocation representations of one anchor. -/
noncomputable def harmonicNormalizer (n : Anchor) : ℝ :=
  ∑ ρ ∈ A.admissible n, (A.scale ρ)⁻¹

/-- Number of distinct physical terminals within one fixed allocation representation. -/
def terminalCount (n : Anchor) (ρ : Allocation) : ℕ :=
  (A.terminals n ρ).card

/-- Reciprocal-allocation physical kernel.  If several allocations yield the same physical
terminal, their weights are added. -/
noncomputable def harmonicKernel (n : Anchor) (v : Target) : ℝ :=
  ∑ ρ ∈ A.admissible n,
    if v ∈ A.terminals n ρ then
      1 / (A.harmonicNormalizer n * A.scale ρ * A.terminalCount n ρ)
    else 0

/-- Harmonic normalizer is strictly positive. -/
theorem harmonicNormalizer_pos (n : Anchor) :
    0 < A.harmonicNormalizer n := by
  apply Finset.sum_pos
  · intro ρ hρ
    exact inv_pos.mpr (A.scale_pos ρ)
  · exact A.admissible_nonempty n

/-- Every reciprocal-allocation kernel entry is nonnegative. -/
theorem harmonicKernel_nonneg (n : Anchor) (v : Target) :
    0 ≤ A.harmonicKernel n v := by
  apply Finset.sum_nonneg
  intro ρ hρ
  split_ifs
  · have hcount : 0 < (A.terminalCount n ρ : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (A.terminals_nonempty n ρ hρ)
    exact (one_div_pos.mpr
      (mul_pos (mul_pos (A.harmonicNormalizer_pos n) (A.scale_pos ρ)) hcount)).le
  · exact le_rfl

private theorem sum_terminal_indicator (n : Anchor) (ρ : Allocation)
    (hρ : ρ ∈ A.admissible n) :
    ∑ v : Target,
      (if v ∈ A.terminals n ρ then
        1 / (A.harmonicNormalizer n * A.scale ρ * A.terminalCount n ρ)
      else 0) =
      1 / (A.harmonicNormalizer n * A.scale ρ) := by
  have hcard : A.terminalCount n ρ ≠ 0 := by
    exact Nat.ne_of_gt (Finset.card_pos.mpr (A.terminals_nonempty n ρ hρ))
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  have hfilter :
      (Finset.univ.filter fun v : Target => v ∈ A.terminals n ρ) =
        A.terminals n ρ := by
    ext v
    simp
  rw [hfilter]
  rw [Finset.sum_const, nsmul_eq_mul]
  unfold terminalCount
  have hcardReal : ((A.terminals n ρ).card : ℝ) ≠ 0 := by
    exact_mod_cast hcard
  field_simp

/-- **Exact row stochasticity.**  Projection from allocation labels to physical terminals loses
no mass because coincident representations are added. -/
theorem sum_harmonicKernel (n : Anchor) :
    ∑ v : Target, A.harmonicKernel n v = 1 := by
  have hH : A.harmonicNormalizer n ≠ 0 :=
    ne_of_gt (A.harmonicNormalizer_pos n)
  calc
    ∑ v : Target, A.harmonicKernel n v =
        ∑ ρ ∈ A.admissible n,
          ∑ v : Target,
            (if v ∈ A.terminals n ρ then
              1 / (A.harmonicNormalizer n * A.scale ρ * A.terminalCount n ρ)
            else 0) := by
      simp only [harmonicKernel]
      rw [Finset.sum_comm]
    _ = ∑ ρ ∈ A.admissible n,
          1 / (A.harmonicNormalizer n * A.scale ρ) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact A.sum_terminal_indicator n ρ hρ
    _ = (A.harmonicNormalizer n)⁻¹ *
          ∑ ρ ∈ A.admissible n, (A.scale ρ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      field_simp
    _ = 1 := by
      rw [← harmonicNormalizer, inv_mul_cancel₀ hH]

end ReciprocalAllocationSystem

section Jacobian

/-- Exact cancellation of reciprocal allocation mass against matching square-root forward and
inverse physical Jacobians. -/
theorem reciprocalAllocation_squareRootJacobian_cancel
    {H T forwardConstant inverseConstant : ℝ}
    (hH : H ≠ 0) (hT : 0 < T) (hforward : forwardConstant ≠ 0) :
    (1 / (H * T * (forwardConstant / √T))) *
        (inverseConstant * √T) =
      inverseConstant / (H * forwardConstant) := by
  have hsqrt : √T ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hT)
  field_simp
  rw [Real.sq_sqrt hT.le]

/-- Column-scale exponent left after a reciprocal power tilt and two square-root Jacobians. -/
def reciprocalAllocationColumnExponent (tilt : ℝ) : ℝ :=
  1 - tilt

/-- Reciprocal exponent one is scale-neutral. -/
theorem reciprocalAllocationColumnExponent_one :
    reciprocalAllocationColumnExponent 1 = 0 := by
  simp [reciprocalAllocationColumnExponent]

/-- Reciprocal exponent one is the unique scale-neutral allocation tilt. -/
theorem reciprocalAllocation_scaleNeutral_iff (tilt : ℝ) :
    reciprocalAllocationColumnExponent tilt = 0 ↔ tilt = 1 := by
  unfold reciprocalAllocationColumnExponent
  constructor <;> intro h <;> linarith

end Jacobian

section Capacity

/-- A finite nonnegative row-stochastic kernel. -/
structure FiniteRowStochasticKernel (Anchor Target : Type*)
    [Fintype Anchor] [Fintype Target] where
  weight : Anchor → Target → ℝ
  weight_nonneg : ∀ n v, 0 ≤ weight n v
  row_sum : ∀ n, ∑ v, weight n v = 1

namespace FiniteRowStochasticKernel

variable {Anchor Target : Type*} [Fintype Anchor] [Fintype Target]
  (P : FiniteRowStochasticKernel Anchor Target)

/-- Total mass of a finite row-stochastic kernel equals number of source anchors. -/
theorem total_mass :
    ∑ v : Target, ∑ n : Anchor, P.weight n v = Fintype.card Anchor := by
  rw [Finset.sum_comm]
  simp_rw [P.row_sum]
  simp

/-- **Finite capacity lower bound.**  Some physical terminal carries at least average column
load.  In particular, a terminal universe of sublinear cardinality cannot support asymptotically
unit load for a linear-density source universe. -/
theorem exists_average_le_column [Nonempty Target] :
    ∃ v : Target,
      (Fintype.card Anchor : ℝ) / Fintype.card Target ≤
        ∑ n : Anchor, P.weight n v := by
  by_contra h
  have hstrict : ∀ v : Target,
      ∑ n : Anchor, P.weight n v <
        (Fintype.card Anchor : ℝ) / Fintype.card Target := by
    intro v
    exact lt_of_not_ge fun hv => h ⟨v, hv⟩
  have hTarget : (Finset.univ : Finset Target).Nonempty := Finset.univ_nonempty
  have hsum :
      ∑ v : Target, ∑ n : Anchor, P.weight n v <
        ∑ v : Target,
          ((Fintype.card Anchor : ℝ) / Fintype.card Target) :=
    Finset.sum_lt_sum_of_nonempty hTarget fun v hv => hstrict v
  rw [P.total_mass] at hsum
  have hcard : (Fintype.card Target : ℝ) ≠ 0 := by
    positivity
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hsum
  field_simp [hcard] at hsum
  exact (lt_irrefl _ hsum)

end FiniteRowStochasticKernel

end Capacity

end RHTower
