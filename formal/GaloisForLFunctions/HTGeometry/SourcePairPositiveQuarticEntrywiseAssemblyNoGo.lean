import GaloisForLFunctions.HTGeometry.SourcePairPositiveQuarticGradedRealification

/-!
# Entrywise positive-quartic assembly is not a real-divisor reporter

The positive quartic source-pair charge detects whether one scalar coefficient is real. It cannot
be summed entrywise to detect whether a matrix has real spectrum. The Hermitian matrix

`[[0,i],[-i,0]]`

has characteristic divisor `(z-1)(z+1)`, but its two nonreal off-diagonal coefficient cells each
carry charge `2300`. Thus its entrywise charge is `4600` despite its entirely real divisor.

This rules out using the coefficient-cell assembly of the escaping odd-pole construction as GTA's
global orientation reporter. Any surviving aggregation must be conjugation invariant rather than
entrywise.
-/

open Complex Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Minimal Hermitian counterexample with nonreal coefficient cells and real spectrum. -/
def positiveQuarticEntrywiseHermitianCounterexample :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, I; -I, 0]

/-- Sum of local positive quartic charges over all entries of a two-by-two matrix. -/
def sourcePairPositiveQuarticEntrywiseCharge
    (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    sourcePairPositiveQuarticCharge (A i j).re (A i j).im

theorem positiveQuarticEntrywiseHermitianCounterexample_isHermitian :
    positiveQuarticEntrywiseHermitianCounterexample.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveQuarticEntrywiseHermitianCounterexample]

/-- Exact positive entrywise charge of the counterexample. -/
theorem sourcePairPositiveQuarticEntrywiseCharge_counterexample :
    sourcePairPositiveQuarticEntrywiseCharge
      positiveQuarticEntrywiseHermitianCounterexample = 4600 := by
  simp [sourcePairPositiveQuarticEntrywiseCharge,
    positiveQuarticEntrywiseHermitianCounterexample,
    sourcePairPositiveQuarticCharge]
  norm_num

/-- Its ordinary characteristic divisor has the two real roots `±1`. -/
theorem positiveQuarticEntrywiseHermitianCounterexample_charDivisor
    (z : ℂ) :
    (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      positiveQuarticEntrywiseHermitianCounterexample).det =
        (z - 1) * (z + 1) := by
  simp [positiveQuarticEntrywiseHermitianCounterexample, Matrix.det_fin_two]
  ring_nf

theorem positiveQuarticEntrywiseHermitianCounterexample_divisor_zero_im
    {z : ℂ}
    (hz : (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      positiveQuarticEntrywiseHermitianCounterexample).det = 0) :
    z.im = 0 := by
  rw [positiveQuarticEntrywiseHermitianCounterexample_charDivisor] at hz
  rcases mul_eq_zero.mp hz with hz | hz
  · have : z = 1 := sub_eq_zero.mp hz
    rw [this]
    simp
  · have : z = -1 := by linear_combination hz
    rw [this]
    simp

/-- Closed no-go: real divisor and Hermiticity coexist with strictly positive entrywise charge. -/
theorem positiveQuarticEntrywiseAssembly_not_realDivisorReporter :
    positiveQuarticEntrywiseHermitianCounterexample.IsHermitian ∧
      (∀ z : ℂ,
        (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
          positiveQuarticEntrywiseHermitianCounterexample).det = 0 → z.im = 0) ∧
      sourcePairPositiveQuarticEntrywiseCharge
        positiveQuarticEntrywiseHermitianCounterexample = 4600 ∧
      0 < sourcePairPositiveQuarticEntrywiseCharge
        positiveQuarticEntrywiseHermitianCounterexample := by
  refine ⟨positiveQuarticEntrywiseHermitianCounterexample_isHermitian,
    fun _ hz => positiveQuarticEntrywiseHermitianCounterexample_divisor_zero_im hz,
    sourcePairPositiveQuarticEntrywiseCharge_counterexample, ?_⟩
  rw [sourcePairPositiveQuarticEntrywiseCharge_counterexample]
  norm_num

end

end GaloisForLFunctions.HTGeometry
