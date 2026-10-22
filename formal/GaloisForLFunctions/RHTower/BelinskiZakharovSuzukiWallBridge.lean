import GaloisForLFunctions.RHTower.Suzuki.SuzukiWallFieldAntidiagonalGramLift
import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Belinski--Zakharov residues in the Suzuki wall field

The finite two-height Suzuki critical wall-field Gram section is a nonzero rank-one complex
residue.  This module identifies it with the complex extension of the real BZ residue used by the
Kerr--Newman two-Killing dressing interface.  Its Hermitian Gram origin is deliberate: it makes
this an amplitude/projector residue, rather than the nilpotent residue of a determinant-preserving
unipotent vacuum dressing.

No assertion is made here about an Einstein--Maxwell solution, a full BZ inverse-scattering
construction, or a Riemann-hypothesis consequence.
-/

open scoped ComplexConjugate Matrix

namespace RHTower

/-- Complex rank-one BZ residue for a two-dimensional spectral packet. -/
def belinskiZakharovComplexRankOneResidue
    (column row : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec column row

/-- Every complex two-dimensional BZ rank-one residue has zero determinant. -/
theorem belinskiZakharovComplexRankOneResidue_det
    (column row : Fin 2 → ℂ) :
    (belinskiZakharovComplexRankOneResidue column row).det = 0 := by
  rw [Matrix.det_fin_two]
  simp [belinskiZakharovComplexRankOneResidue, Matrix.vecMulVec]
  ring

/-- Complex BZ residues extend the real two-Killing residue used by Kerr--Newman dressings. -/
theorem belinskiZakharovComplexRankOneResidue_ofReal
    (column row : Fin 2 → ℝ) :
    belinskiZakharovComplexRankOneResidue
        (fun i => (column i : ℂ)) (fun j => (row j : ℂ)) =
      (GaloisForLFunctions.HTGeometry.belinskiZakharovRankOneResidue column row).map
        (fun x => (x : ℂ)) := by
  ext i j
  simp [belinskiZakharovComplexRankOneResidue,
    GaloisForLFunctions.HTGeometry.belinskiZakharovRankOneResidue,
    Matrix.vecMulVec]

/-- A two-height Suzuki critical wall-field Gram section is exactly a complex BZ residue. -/
theorem suzukiCriticalWallFieldGramMatrix_two_eq_belinskiZakharovComplexResidue
    (height : Fin 2 → ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallFieldGramMatrix height p e =
      belinskiZakharovComplexRankOneResidue
        (fun i => suzukiCriticalWallField (height i) p e)
        (fun j => star (suzukiCriticalWallField (height j) p e)) := by
  exact suzukiCriticalWallFieldGramMatrix_eq_vecMulVec height p e

/-- The two-height Suzuki wall residue has vanishing determinant. -/
theorem suzukiCriticalWallFieldGramMatrix_two_det_zero
    (height : Fin 2 → ℝ) (p : Nat.Primes) (e : ℕ) :
    (suzukiCriticalWallFieldGramMatrix height p e).det = 0 := by
  rw [suzukiCriticalWallFieldGramMatrix_two_eq_belinskiZakharovComplexResidue]
  exact belinskiZakharovComplexRankOneResidue_det _ _

/-- Unlike the zero residue, every two-height Suzuki wall residue has exact rank one. -/
theorem suzukiCriticalWallFieldGramMatrix_two_rank_eq_one
    (height : Fin 2 → ℝ) (p : Nat.Primes) (e : ℕ) :
    (suzukiCriticalWallFieldGramMatrix height p e).rank = 1 := by
  exact suzukiCriticalWallFieldGramMatrix_rank_eq_one (by norm_num) height p e

/-- The two-height Suzuki wall BZ residue is never the zero matrix. -/
theorem suzukiCriticalWallFieldGramMatrix_two_ne_zero
    (height : Fin 2 → ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallFieldGramMatrix height p e ≠ 0 := by
  rw [suzukiCriticalWallFieldGramMatrix_two_eq_belinskiZakharovComplexResidue]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp only [belinskiZakharovComplexRankOneResidue, Matrix.vecMulVec] at h00
  exact (mul_ne_zero (suzukiCriticalWallField_ne_zero _ p e)
    (star_ne_zero.mpr (suzukiCriticalWallField_ne_zero _ p e))) h00

end RHTower
