import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHankelKernel
import GaloisForLFunctions.HTGeometry.QuantumGeometricTensorGram
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A concrete complex Hilbert realization of collision moments

The two positive spectral weights supply two real coordinates in a complex
Euclidean space. Their inner products reproduce every shifted collision
moment, so existing projective and quantum-geometric interfaces apply.
This is a constructed mathematical realization of the thermal-kernel history.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Two weighted geometric coordinates realize the entire collision moment sequence. -/
def egbFixedChargeAGibbsCollisionMomentVector (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (j : ℕ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![
    ((Real.sqrt ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) *
      (4 / 9 : ℝ) ^ j : ℝ) : ℂ),
    ((Real.sqrt ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) *
      (1 / 36 : ℝ) ^ j : ℝ) : ℂ)]

/-- The concrete Hilbert inner products equal the shifted temporal collision moments. -/
theorem egbFixedChargeAGibbsCollisionMomentVector_inner (n o i j : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    inner ℂ (egbFixedChargeAGibbsCollisionMomentVector n o β E i)
      (egbFixedChargeAGibbsCollisionMomentVector n o β E j) =
      (egbFixedChargeAGibbsCollisionExcess n (i + j + o + 1) β E : ℂ) := by
  have hg := congrArg
    (fun M : Matrix (Fin (i + j + 1)) (Fin (i + j + 1)) ℝ =>
      M ⟨i, by omega⟩ ⟨j, by omega⟩)
    (egbFixedChargeAGibbsCollisionHankelMatrix_gram n o (i + j + 1) β E)
  rw [Matrix.mul_apply, Fin.sum_univ_two] at hg
  change egbFixedChargeAGibbsCollisionExcess n (i + j + o + 1) β E =
    (Real.sqrt ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ i) *
      (Real.sqrt ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ j) +
    (Real.sqrt ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ i) *
      (Real.sqrt ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ j) at hg
  unfold egbFixedChargeAGibbsCollisionMomentVector
  rw [PiLp.inner_apply]
  change (∑ k : Fin 2, inner ℂ
    ((![((Real.sqrt ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ i : ℝ) : ℂ),
      ((Real.sqrt ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ i : ℝ) : ℂ)] : Fin 2 → ℂ) k)
    ((![((Real.sqrt ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ j : ℝ) : ℂ),
      ((Real.sqrt ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ j : ℝ) : ℂ)] : Fin 2 → ℂ) k)) = _
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, RCLike.inner_apply, Complex.conj_ofReal]
  rw [hg]
  push_cast
  ring

end
end GaloisForLFunctions.HTGeometry
