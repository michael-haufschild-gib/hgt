import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuDeterminant
import Mathlib.Algebra.BigOperators.Option

open scoped BigOperators Matrix
open Matrix
namespace GaloisForLFunctions.HTGeometry
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A rank-one perturbation repairs one missing diagonal mode by its complementary product. -/
theorem bgv_det_one_missing_mode (a : ι → R) (u v : Option ι → R) :
    (diagonal (fun i : Option ι => i.elim 0 a) + vecMulVec u v).det =
      u none * v none * ∏ i, a i := by
  rw [bgv_det_diagonal_add_vecMulVec, Fintype.prod_option]
  simp only [Option.elim_none, zero_mul, zero_add]
  rw [Finset.sum_eq_single none]
  · congr 1
    have he : (Finset.univ : Finset (Option ι)).erase none =
        Finset.univ.map Function.Embedding.some := by
      ext i
      cases i <;> simp
    rw [he, Finset.prod_map]
    rfl
  · intro i _ hi
    have hz : (∏ j ∈ Finset.univ.erase i, j.elim 0 a) = 0 := by
      apply Finset.prod_eq_zero (i := none)
      · exact Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ none⟩
      · rfl
    rw [hz, mul_zero]
  · simp

/-- A single rank-one perturbation cannot repair two missing diagonal modes. -/
theorem bgv_det_two_missing_modes (a : ι → R) (u v : Option (Option ι) → R) :
    (diagonal (fun i : Option (Option ι) => i.elim 0 (fun j => j.elim 0 a)) +
      vecMulVec u v).det = 0 := by
  rw [bgv_det_one_missing_mode, Fintype.prod_option]
  simp

end GaloisForLFunctions.HTGeometry
