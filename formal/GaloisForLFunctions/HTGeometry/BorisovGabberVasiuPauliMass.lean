import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuDeterminant
import GaloisForLFunctions.HTGeometry.GomesPauliAdjointMass

/-!
# Axis-dependent mass shifts and observation repair

Borisov--Gabber--Vasiu's determinant lemma applies to the corpus's Pauli orbit
mass operator. It yields independent axis shifts and the exact overlap law for
repairing the carrier zero mode with a rank-one observation.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The determinant for independent axis shifts of the actual Pauli orbit mass. -/
theorem bgv_pauli_anisotropic_det (r a : Fin 3 → ℝ) :
    (diagonal a + gomesPauliAdjointMass r).det =
      (∏ i, (a i + (r ⬝ᵥ r))) -
        ∑ i, r i ^ (2 : ℕ) * ∏ j ∈ Finset.univ.erase i, (a j + (r ⬝ᵥ r)) := by
  have hmatrix : diagonal a + gomesPauliAdjointMass r =
      diagonal (fun i => a i + r ⬝ᵥ r) + vecMulVec (-r) r := by
    ext i j
    by_cases h : i = j
    · simp [gomesPauliAdjointMass, h]
      ring
    · simp [gomesPauliAdjointMass, h]
  rw [hmatrix, bgv_det_diagonal_add_vecMulVec]
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg,
    pow_two]

/-- The cofactor matrix retains exactly the carrier axis, including the zero carrier. -/
theorem bgv_pauli_adjugate (r : Fin 3 → ℝ) :
    (gomesPauliAdjointMass r).adjugate = (r ⬝ᵥ r) • vecMulVec r r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesPauliAdjointMass, Matrix.adjugate_fin_three, Matrix.vecMulVec,
      dotProduct, Fin.sum_univ_three] <;> ring

/-- A rank-one observation repairs the Pauli zero mode exactly through its carrier overlap. -/
theorem bgv_pauli_observation_det (r v : Fin 3 → ℝ) (t : ℝ) :
    (gomesPauliAdjointMass r + t • vecMulVec v v).det =
      t * (r ⬝ᵥ r) * (r ⬝ᵥ v) ^ (2 : ℕ) := by
  have hdet : (gomesPauliAdjointMass r).det = 0 := by
    have h := gomesPauliAdjointMass_characteristic r 0
    simpa [Matrix.det_neg] using h
  rw [show t • vecMulVec v v = vecMulVec (t • v) v by ext i j; simp [Matrix.vecMulVec, mul_assoc],
    bgv_det_add_vecMulVec, hdet, bgv_pauli_adjugate]
  simp [dotProduct, Fin.sum_univ_three, Matrix.mulVec, Matrix.vecMulVec]
  ring

end GaloisForLFunctions.HTGeometry
