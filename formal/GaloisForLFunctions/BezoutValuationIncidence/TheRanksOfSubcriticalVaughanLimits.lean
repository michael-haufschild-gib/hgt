import GaloisForLFunctions.BezoutValuationIncidence.TheSubcriticalVaughanGramLimitSet
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Subcritical smooth Vaughan limits are outer products. Their ranks are zero at
zero amplitude and one at every positive arithmetic amplitude.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- Zero amplitude gives the zero smooth limit matrix. -/
theorem pmVaughanSmoothLimitMatrix_zero (ε : ℝ) : pmVaughanSmoothLimitMatrix ε 0 = 0 := by
  funext i j
  simp only [pmVaughanSmoothLimitMatrix, mul_zero, zero_mul, Pi.zero_apply]

/-- Every smooth limit matrix is a single outer product. -/
theorem rank_pmVaughanSmoothLimitMatrix_le_one (ε a : ℝ) :
    Matrix.rank (pmVaughanSmoothLimitMatrix ε a) ≤ 1 := by
  change (Matrix.vecMulVec
    (fun i => subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε) * a * pmPronicVaughanSmoothSigns i)
      pmPronicVaughanSmoothSigns).rank ≤ 1
  exact Matrix.rank_vecMulVec_le _ _

/-- Positive subcritical amplitudes give rank exactly one. -/
theorem rank_pmVaughanSmoothLimitMatrix_of_pos {ε a : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (ha : 0 < a) :
    Matrix.rank (pmVaughanSmoothLimitMatrix ε a) = 1 := by
  have hβ : 0 < 1 - 2 * ε := by linarith only [hε2]
  have hc := subHalfZetaCoeff_ne_zero hε (by linarith only [hε2] : ε < 1)
  have hdiag : 0 < pmVaughanSmoothLimitMatrix ε a 2 2 := by
    have h := mul_pos (div_pos (sq_pos_of_ne_zero hc) hβ) ha
    change 0 < subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε) * a * (-1) * (-1)
    simpa only [mul_neg_one, neg_neg] using h
  have hne : Matrix.rank (pmVaughanSmoothLimitMatrix ε a) ≠ 0 := by
    intro hz
    have hlin : Matrix.mulVecLin (pmVaughanSmoothLimitMatrix ε a) = 0 := by
      simpa only [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] using hz
    have hcell := congrArg
      (fun f : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) =>
        f (Pi.single (2 : Fin 5) 1) (2 : Fin 5)) hlin
    have hzcell : pmVaughanSmoothLimitMatrix ε a 2 2 = 0 := by
      simpa [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Pi.single_apply] using hcell
    exact hdiag.ne' hzcell
  have hle := rank_pmVaughanSmoothLimitMatrix_le_one ε a
  omega

/-- The rank of an arithmetic smooth limit is zero or one according to its amplitude. -/
theorem rank_pmVaughanSmoothLimitMatrix {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {a : ℝ}
    (ha : a ∈ pmVaughanSmoothAmplitudeSet) :
    Matrix.rank (pmVaughanSmoothLimitMatrix ε a) = if a = 0 then 0 else 1 := by
  by_cases hz : a = 0
  · subst a
    rw [if_pos rfl, pmVaughanSmoothLimitMatrix_zero]
    change Matrix.rank (0 : Matrix (Fin 5) (Fin 5) ℝ) = 0
    simp
  · rw [if_neg hz]
    exact rank_pmVaughanSmoothLimitMatrix_of_pos hε hε2
      (lt_of_le_of_ne (pmVaughanSmoothAmplitudeSet_nonneg ha) (Ne.symm hz))

#print axioms pmVaughanSmoothLimitMatrix_zero
#print axioms rank_pmVaughanSmoothLimitMatrix_le_one
#print axioms rank_pmVaughanSmoothLimitMatrix_of_pos
#print axioms rank_pmVaughanSmoothLimitMatrix
end GaloisForLFunctions.BezoutValuationIncidence
