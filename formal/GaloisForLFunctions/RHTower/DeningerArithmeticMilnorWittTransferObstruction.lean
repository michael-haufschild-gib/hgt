import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Bare Milnor--Witt transfer is not Hodge-positive

The real representative of the quadratic multiplicity

`n_ε = ⟨1⟩ + ⟨-1⟩ + ⟨1⟩ + ⋯`

is the diagonal weighted-sum-of-squares form with alternating signs.  As soon as `2 ≤ n`, its
second coordinate is a negative direction.  Consequently the canonical degree-`n`
Milnor--Witt transfer is not itself a positive Hodge form; an independent archimedean
polarization is necessary.

This statement concerns only the source quadratic transfer.  It uses no Xi divisor, zero
location, Weil positivity, or RH premise.
-/

namespace RHTower

open QuadraticMap

/-- Alternating real weights representing the Milnor--Witt quadratic multiplicity `n_ε`. -/
def deningerMilnorWittTransferWeight (n : ℕ) (i : Fin n) : ℝ :=
  if Even i.val then 1 else -1

/-- Real diagonal representative of the degree-`n` Milnor--Witt transfer class `n_ε`. -/
def deningerMilnorWittTransferForm (n : ℕ) : QuadraticForm ℝ (Fin n → ℝ) :=
  weightedSumSquares ℝ (deningerMilnorWittTransferWeight n)

/-- The coordinate of index one is available in every degree at least two. -/
def deningerMilnorWittNegativeIndex {n : ℕ} (hn : 2 ≤ n) : Fin n :=
  ⟨1, by omega⟩

@[simp]
theorem deningerMilnorWittTransferWeight_negativeIndex
    {n : ℕ} (hn : 2 ≤ n) :
    deningerMilnorWittTransferWeight n
        (deningerMilnorWittNegativeIndex hn) = -1 := by
  simp [deningerMilnorWittTransferWeight, deningerMilnorWittNegativeIndex]

/-- The canonical transfer form takes value `-1` on its explicit negative unit vector. -/
theorem deningerMilnorWittTransferForm_negativeVector
    {n : ℕ} (hn : 2 ≤ n) :
    deningerMilnorWittTransferForm n
        (Pi.single (deningerMilnorWittNegativeIndex hn) (1 : ℝ)) = -1 := by
  classical
  simp [deningerMilnorWittTransferForm, weightedSumSquares_apply,
    deningerMilnorWittTransferWeight, deningerMilnorWittNegativeIndex]

/-- The explicit negative unit vector is nonzero. -/
theorem deningerMilnorWittNegativeVector_ne_zero
    {n : ℕ} (hn : 2 ≤ n) :
    Pi.single (deningerMilnorWittNegativeIndex hn) (1 : ℝ) ≠ 0 := by
  classical
  intro h
  have hcoord := congrFun h (deningerMilnorWittNegativeIndex hn)
  simpa using hcoord

/-- Every nontrivial Milnor--Witt quadratic multiplicity has a nonzero negative inertia index. -/
theorem deningerMilnorWittTransferForm_sigNeg_pos
    {n : ℕ} (hn : 2 ≤ n) :
    0 < QuadraticForm.sigNeg (deningerMilnorWittTransferForm n) := by
  rw [deningerMilnorWittTransferForm, QuadraticForm.sigNeg_weightedSumSquares]
  exact Set.ncard_pos.mpr
    ⟨deningerMilnorWittNegativeIndex hn, by
      simp [deningerMilnorWittTransferWeight, deningerMilnorWittNegativeIndex]⟩

/-- Bare degree-`n` Milnor--Witt transfer is not positive definite for `n ≥ 2`. -/
theorem deningerMilnorWittTransferForm_not_posDef
    {n : ℕ} (hn : 2 ≤ n) :
    ¬QuadraticMap.PosDef (deningerMilnorWittTransferForm n) := by
  intro hpos
  have hnegative :=
    hpos
      (Pi.single (deningerMilnorWittNegativeIndex hn) (1 : ℝ))
      (deningerMilnorWittNegativeVector_ne_zero hn)
  rw [deningerMilnorWittTransferForm_negativeVector hn] at hnegative
  linarith

/-- In particular, the bare quadratic transfer of every prime degree is indefinite. -/
theorem deningerPrimeMilnorWittTransferForm_not_posDef
    {p : ℕ} (hp : Nat.Prime p) :
    ¬QuadraticMap.PosDef (deningerMilnorWittTransferForm p) :=
  deningerMilnorWittTransferForm_not_posDef (Nat.Prime.two_le hp)

end RHTower
