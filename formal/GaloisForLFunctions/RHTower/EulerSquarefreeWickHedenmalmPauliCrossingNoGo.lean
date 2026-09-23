import GaloisForLFunctions.RHTower.EulerSquarefreeWickHedenmalmReflectionCrossing
import GaloisForLFunctions.HTGeometry.StaticGaussianCrossingMemoryLaw

/-!
# Pauli realization and Wick-positivity no-go for the EWQ--Hedenmalm crossing

The reflected EWQ--Hedenmalm channel is negative off the critical line.  It is tempting to invoke
positivity of a classical Gaussian/Wick source to rule this out.  That inference is false:
individual fourth-order crossing contractions of Hermitian noncommuting coefficients may be
negative even though the complete Wick contraction is positive.

This module realizes the exact arithmetic reflected crossing with the anticommuting Pauli pair
`X,Z`.  For amplitude `z`, `Re Tr(X_z Z X_z Z) = -2 z²`; multiplication by `2 log p` is precisely
the EWQ--Hedenmalm reflected prime term.  At the same time the total two-Pauli crossing memory is
the nonnegative square `2(z²-1)²`.

Therefore generic Gaussianity, Hermiticity, or positivity of the full fourth moment cannot supply
the RH-bearing mixed-incidence positivity.  A surviving QFT producer must impose a stronger
reflection-positive subalgebra condition which controls this specific ordered contraction.
-/

open scoped BigOperators Matrix

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Single-qubit Pauli `X`. -/
def ewqPauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 1, 0]

/-- Single-qubit Pauli `Z`. -/
def ewqPauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, -1]

theorem ewqPauliX_isHermitian : ewqPauliXᴴ = ewqPauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ewqPauliX]

theorem ewqPauliZ_isHermitian : ewqPauliZᴴ = ewqPauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ewqPauliZ]

/-- Arithmetic amplitude inserted in the Pauli `X` leg. -/
def ewqPauliScaledX (z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (z : ℂ) • ewqPauliX

theorem ewqPauliScaledX_isHermitian (z : ℝ) :
    (ewqPauliScaledX z)ᴴ = ewqPauliScaledX z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ewqPauliScaledX, ewqPauliX]

/-- The ordered Pauli crossing is a negative square. -/
theorem ewqPauli_anticommuting_crossing_re (z : ℝ) :
    (Matrix.trace
      (ewqPauliScaledX z * ewqPauliZ * ewqPauliScaledX z * ewqPauliZ)).re =
      -2 * z ^ (2 : ℕ) := by
  simp [ewqPauliScaledX, ewqPauliX, ewqPauliZ, Matrix.trace,
    Fin.sum_univ_two]
  ring

theorem ewqPauli_anticommuting_crossing_re_neg {z : ℝ} (hz : z ≠ 0) :
    (Matrix.trace
      (ewqPauliScaledX z * ewqPauliZ * ewqPauliScaledX z * ewqPauliZ)).re < 0 := by
  rw [ewqPauli_anticommuting_crossing_re]
  nlinarith [sq_pos_of_ne_zero hz]

/-- Two-coefficient Hermitian Gaussian pencil built from the scaled Pauli pair. -/
def ewqPauliCrossingFamily (z : ℝ) :
    Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![ewqPauliScaledX z, ewqPauliZ]

theorem ewqPauliCrossingFamily_isHermitian (z : ℝ) (i : Fin 2) :
    (ewqPauliCrossingFamily z i)ᴴ = ewqPauliCrossingFamily z i := by
  fin_cases i
  · exact ewqPauliScaledX_isHermitian z
  · exact ewqPauliZ_isHermitian

/-- The total classical crossing memory remains a nonnegative square despite its negative mixed
ordered contractions. -/
theorem ewqPauliCrossingMemory_re (z : ℝ) :
    (GaloisForLFunctions.HTGeometry.matrixFamilyCrossingMemory
      (ewqPauliCrossingFamily z)).re = 2 * (z ^ (2 : ℕ) - 1) ^ (2 : ℕ) := by
  simp [GaloisForLFunctions.HTGeometry.matrixFamilyCrossingMemory,
    ewqPauliCrossingFamily, ewqPauliScaledX, ewqPauliX, ewqPauliZ,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem ewqPauliCrossingMemory_re_nonneg (z : ℝ) :
    0 ≤ (GaloisForLFunctions.HTGeometry.matrixFamilyCrossingMemory
      (ewqPauliCrossingFamily z)).re := by
  rw [ewqPauliCrossingMemory_re]
  positivity

/-- Hermiticity alone never implies nonnegativity of an ordered fourth crossing. -/
theorem not_every_hermitian_pair_crossing_nonnegative :
    ¬ ∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
      Aᴴ = A → Bᴴ = B → 0 ≤ (Matrix.trace (A * B * A * B)).re := by
  intro h
  have hbad := h (ewqPauliScaledX 1) ewqPauliZ
    (ewqPauliScaledX_isHermitian 1) ewqPauliZ_isHermitian
  rw [ewqPauli_anticommuting_crossing_re] at hbad
  norm_num at hbad

/-- **Exact Pauli realization.** The arithmetic reflected crossing is the ordered fourth crossing
of the Hermitian Pauli pair, with its literal prime logarithmic weight. -/
theorem ewqHedenmalm_reflectedCrossing_eq_pauliCrossing
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) (x y : Fin 2) :
    eulerPrimeQuadraticResidueOppositeBilinearCrossing p
        (ewqHedenmalmCovariantAmplitude p q)
        (ewqHedenmalmCovariantAmplitude p (_root_.RHTower.xiZeroCopyReflectEquiv q)) x y =
      2 * Real.log (p : ℝ) *
        (Matrix.trace
          (ewqPauliScaledX (ewqHedenmalmCovariantAmplitude p q) * ewqPauliZ *
            ewqPauliScaledX (ewqHedenmalmCovariantAmplitude p q) * ewqPauliZ)).re := by
  rw [ewqHedenmalm_reflectedCrossing_eq_neg_self,
    eulerPrimeQuadraticResidueOppositeCrossing_eq,
    ewqPauli_anticommuting_crossing_re]
  ring

end GaloisForLFunctions.RHTower
