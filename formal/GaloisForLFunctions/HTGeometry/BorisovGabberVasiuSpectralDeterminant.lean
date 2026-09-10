import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuDeterminant
import GaloisForLFunctions.HTGeometry.FiniteSpectrumPlainDeterminant

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- A coupled finite spectrum has a polynomial secular equation valid on the original spectrum. -/
theorem bgv_finiteSpectrum_rankOne_det {n : ℕ} (mu u v : Fin n → ℂ) (z t : ℂ) :
    (1 + z • (-diagonal mu) + t • vecMulVec u v).det =
      (∏ i, (1 - z * mu i)) +
        t * ∑ i, u i * v i * ∏ j ∈ Finset.univ.erase i, (1 - z * mu j) := by
  have hm : (1 + z • (-diagonal mu) : Matrix (Fin n) (Fin n) ℂ) =
      diagonal (fun i => 1 - z * mu i) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [sub_eq_add_neg]
    · simp [Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]
  rw [hm, ← smul_vecMulVec, bgv_det_diagonal_add_vecMulVec, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ac_rfl

end GaloisForLFunctions.HTGeometry

