/-
# Guinand--Weil event-source reflection

This module isolates the exact source-reflection law for the finite Guinand--Weil event matrix.
At integral Fourier modes, reflection of a horizon `omega` across `1 / 2` negates the sine source
but preserves the cosine factor.  Consequently the sum of an event matrix and its reflected event
matrix is exactly diagonal.  Every off-diagonal divided-difference incidence is reflection-odd.

The zero mode reads only total event weight.  In contrast, the reflected half-horizon event has
diagonal value `-2` at mode one, so central four-unit normalization cannot imply eventwise positive
semidefiniteness.  Any CCM positivity producer must therefore control the reflection-odd sector
across events or in the cofinal limit, before reducing to the scalar four-unit budget.
-/
import GaloisForLFunctions.RHTower.CCMDividedDifferenceInstantiation
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

namespace RHTower

open Matrix
open scoped BigOperators

/-- Source coefficient of a Guinand--Weil horizon event at an integral Fourier mode. -/
def ccmGuinandWeilEventSource (omega : ℝ) (mode : ℤ) : ℝ :=
  Real.sin (2 * Real.pi * omega * (mode : ℝ)) / Real.pi

/-- Diagonal derivative of the Guinand--Weil event source coefficient. -/
def ccmGuinandWeilEventDiagonal (omega : ℝ) (mode : ℤ) : ℝ :=
  2 * omega * Real.cos (2 * Real.pi * omega * (mode : ℝ))

/-- At integral modes, reflection of the horizon across `1 / 2` negates the event source. -/
theorem ccmGuinandWeilEventSource_one_sub (omega : ℝ) (mode : ℤ) :
    ccmGuinandWeilEventSource (1 - omega) mode =
      -ccmGuinandWeilEventSource omega mode := by
  rw [ccmGuinandWeilEventSource, ccmGuinandWeilEventSource]
  rw [show 2 * Real.pi * (1 - omega) * (mode : ℝ) =
    (mode : ℝ) * (2 * Real.pi) - 2 * Real.pi * omega * (mode : ℝ) by ring]
  rw [Real.sin_int_mul_two_pi_sub]
  ring

/-- At integral modes, reflection of the horizon preserves its cosine factor. -/
theorem ccmGuinandWeilEventCos_one_sub (omega : ℝ) (mode : ℤ) :
    Real.cos (2 * Real.pi * (1 - omega) * (mode : ℝ)) =
      Real.cos (2 * Real.pi * omega * (mode : ℝ)) := by
  rw [show 2 * Real.pi * (1 - omega) * (mode : ℝ) =
    (mode : ℝ) * (2 * Real.pi) - 2 * Real.pi * omega * (mode : ℝ) by ring]
  exact Real.cos_int_mul_two_pi_sub _ _

/-- Reflected event diagonals sum to twice the common cosine factor. -/
theorem ccmGuinandWeilEventDiagonal_add_one_sub (omega : ℝ) (mode : ℤ) :
    ccmGuinandWeilEventDiagonal omega mode +
        ccmGuinandWeilEventDiagonal (1 - omega) mode =
      2 * Real.cos (2 * Real.pi * omega * (mode : ℝ)) := by
  simp only [ccmGuinandWeilEventDiagonal, ccmGuinandWeilEventCos_one_sub]
  ring

/-- Finite Guinand--Weil event matrix on a chosen family of integral Fourier modes. -/
def ccmGuinandWeilEventMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mode : ι → ℤ) (omega : ℝ) : Matrix ι ι ℝ :=
  ccmDividedDifferenceMatrix
    (fun i => (mode i : ℝ))
    (fun i => ccmGuinandWeilEventSource omega (mode i))
    (fun i => ccmGuinandWeilEventDiagonal omega (mode i))

/-- **Exact source-reflection diagonalization.**  The reflection-even part of a single
Guinand--Weil event matrix is diagonal; all off-diagonal source incidence is reflection-odd. -/
theorem ccmGuinandWeilEventMatrix_add_reflected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mode : ι → ℤ) (omega : ℝ) :
    ccmGuinandWeilEventMatrix mode omega +
        ccmGuinandWeilEventMatrix mode (1 - omega) =
      Matrix.diagonal (fun i =>
        2 * Real.cos (2 * Real.pi * omega * (mode i : ℝ))) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ccmGuinandWeilEventMatrix, ccmDividedDifferenceMatrix,
      ccmGuinandWeilEventDiagonal_add_one_sub]
  · simp [ccmGuinandWeilEventMatrix, ccmDividedDifferenceMatrix, hij,
      ccmGuinandWeilEventSource_one_sub]
    ring_nf

/-- Symmetrizing one event across the source reflection keeps exactly its cosine diagonal. -/
theorem ccmGuinandWeilEventMatrix_reflection_even_part
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mode : ι → ℤ) (omega : ℝ) :
    (1 / 2 : ℝ) •
        (ccmGuinandWeilEventMatrix mode omega +
          ccmGuinandWeilEventMatrix mode (1 - omega)) =
      Matrix.diagonal (fun i =>
        Real.cos (2 * Real.pi * omega * (mode i : ℝ))) := by
  rw [ccmGuinandWeilEventMatrix_add_reflected]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Finite signed packet of source-reflected Guinand--Weil events. -/
def ccmGuinandWeilReflectedEventPacketMatrix
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (weight : κ → ℝ) (horizon : κ → ℝ) (mode : ι → ℤ) : Matrix ι ι ℝ :=
  ∑ r, weight r •
    (ccmGuinandWeilEventMatrix mode (horizon r) +
      ccmGuinandWeilEventMatrix mode (1 - horizon r))

/-- Every finite source-reflected event packet is exactly a cosine diagonal. -/
theorem ccmGuinandWeilReflectedEventPacketMatrix_eq_diagonal
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (weight : κ → ℝ) (horizon : κ → ℝ) (mode : ι → ℤ) :
    ccmGuinandWeilReflectedEventPacketMatrix weight horizon mode =
      Matrix.diagonal (fun i =>
        2 * ∑ r, weight r *
          Real.cos (2 * Real.pi * horizon r * (mode i : ℝ))) := by
  rw [ccmGuinandWeilReflectedEventPacketMatrix]
  simp_rw [ccmGuinandWeilEventMatrix_add_reflected]
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  · simp [Matrix.smul_apply, hij]

/-- The reflected packet's zero mode is twice total event weight, independent of horizons. -/
theorem ccmGuinandWeilReflectedEventPacketMatrix_zero_mode
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (weight : κ → ℝ) (horizon : κ → ℝ) (mode : ι → ℤ)
    (i : ι) (hi : mode i = 0) :
    ccmGuinandWeilReflectedEventPacketMatrix weight horizon mode i i =
      2 * ∑ r, weight r := by
  rw [ccmGuinandWeilReflectedEventPacketMatrix_eq_diagonal]
  simp [hi]

/-- Total event weight two produces the central four-unit value, but says nothing about the
nonzero cosine modes. -/
theorem ccmGuinandWeilReflectedEventPacketMatrix_central_four
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (weight : κ → ℝ) (horizon : κ → ℝ) (mode : ι → ℤ)
    (i : ι) (hi : mode i = 0) (hweight : ∑ r, weight r = 2) :
    ccmGuinandWeilReflectedEventPacketMatrix weight horizon mode i i = 4 := by
  rw [ccmGuinandWeilReflectedEventPacketMatrix_zero_mode weight horizon mode i hi,
    hweight]
  norm_num

/-- At half horizon, the reflected event pair has diagonal value `-2` at mode one. -/
theorem ccmGuinandWeilEventMatrix_half_diagonal_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mode : ι → ℤ) (i : ι) (hi : mode i = 1) :
    (ccmGuinandWeilEventMatrix mode (1 / 2 : ℝ) +
      ccmGuinandWeilEventMatrix mode (1 - (1 / 2 : ℝ))) i i = -2 := by
  rw [ccmGuinandWeilEventMatrix_add_reflected]
  simp only [Matrix.diagonal_apply_eq, hi, Int.cast_one]
  rw [show 2 * Real.pi * (1 / 2 : ℝ) * 1 = Real.pi by ring,
    Real.cos_pi]
  norm_num

/-- **Atomwise positivity no-go.**  A mode-one carrier makes the reflected half-horizon event
matrix non-positive-semidefinite, despite its positive central value. -/
theorem ccmGuinandWeilEventMatrix_half_not_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mode : ι → ℤ) (i : ι) (hi : mode i = 1) :
    ¬ (ccmGuinandWeilEventMatrix mode (1 / 2 : ℝ) +
      ccmGuinandWeilEventMatrix mode (1 - (1 / 2 : ℝ))).PosSemidef := by
  intro hpsd
  have hdiag := hpsd.diag_nonneg (i := i)
  rw [ccmGuinandWeilEventMatrix_half_diagonal_at_one mode i hi] at hdiag
  norm_num at hdiag

end RHTower
