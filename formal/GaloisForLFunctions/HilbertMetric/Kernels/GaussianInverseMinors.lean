import GaloisForLFunctions.HilbertMetric.Kernels.GaussianCollocation
import GaloisForLFunctions.HTGeometry.JacobiComplementaryMinor

/-!
# Complementary minors of Gaussian interpolation

The Gaussian kernel of Salazar and the complementary-minor identity used
by Choi and Jang give every inverse minor explicitly. Changing alternate
row and column signs turns Gaussian inversion into another strictly
totally positive matrix.
-/

namespace GaloisForLFunctions.HilbertMetric
open Matrix Finset HTGeometry
noncomputable section

variable {n : ℕ}

/-- The magnitude and sign of each inverse minor are both determined by its complement. -/
theorem gaussianCollocation_inverse_complement (t : ℝ) (x y : Fin n ↪o ℝ)
    (S T : Finset (Fin n)) {m : ℕ} (hS : S.card = m) (hT : T.card = m) :
    (-1 : ℝ) ^ (idxSum S + idxSum T) *
      ((gaussianCollocation t x y)⁻¹.submatrix (S.orderEmbOfFin hS) (T.orderEmbOfFin hT)).det =
    ((gaussianCollocation t x y).submatrix (Tᶜ.orderEmbOfFin (card_compl_fin hT))
      (Sᶜ.orderEmbOfFin (card_compl_fin hS))).det / (gaussianCollocation t x y).det := by
  let M := gaussianCollocation t x y
  have hpos : 0 < M.det := gaussianCollocation_det_pos _ _ _
  have hJ := det_submatrix_mul_sign_mul_det M M⁻¹ (nonsing_inv_mul _ hpos.ne'.isUnit)
    S T hS hT
  rw [sign_blockEnum_symm_trans] at hJ
  push_cast at hJ
  apply (eq_div_iff hpos.ne').mpr
  convert hJ using 1
  ring

/-- Every signed inverse minor is strictly positive, including all nonprincipal minors. -/
theorem gaussianCollocation_inverse_minor_sign (t : ℝ) (x y : Fin n ↪o ℝ)
    (S T : Finset (Fin n)) {m : ℕ} (hS : S.card = m) (hT : T.card = m) :
    0 < (-1 : ℝ) ^ (idxSum S + idxSum T) *
      ((gaussianCollocation t x y)⁻¹.submatrix (S.orderEmbOfFin hS) (T.orderEmbOfFin hT)).det := by
  rw [gaussianCollocation_inverse_complement]
  exact div_pos (gaussianCollocation_det_pos t ((Tᶜ.orderEmbOfFin _).trans x)
    ((Sᶜ.orderEmbOfFin _).trans y)) (gaussianCollocation_det_pos t x y)

/-- Apply alternating signs to both coordinates of the inverse interpolator. -/
def gaussianAlternatingInverse (t : ℝ) (x y : Fin n ↪o ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => (-1:ℝ)^i.val * ((-1:ℝ)^j.val * (gaussianCollocation t x y)⁻¹ i j)

private theorem det_row_column_scales {m : ℕ} (a b : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    (of fun i j => a i*(b j*M i j)).det = (∏ i, a i)*((∏ j, b j)*M.det) :=
  (det_mul_column a (of fun i j => b j*M i j)).trans
    (congrArg (fun z : ℝ => (∏ i, a i)*z) (det_mul_row b M))

private theorem prod_alternating (S : Finset (Fin n)) {m : ℕ} (h : S.card = m) :
    (∏ i, (-1:ℝ)^((S.orderEmbOfFin h) i).val) = (-1:ℝ)^(idxSum S) := by
  rw [prod_pow_eq_pow_sum,sum_orderEmbOfFin]

/-- The alternating inverse is strictly totally positive in every order. -/
theorem gaussianAlternatingInverse_minor_pos (t : ℝ) (x y : Fin n ↪o ℝ)
    (S T : Finset (Fin n)) {m : ℕ} (hS : S.card = m) (hT : T.card = m) :
    0 < ((gaussianAlternatingInverse t x y).submatrix
      (S.orderEmbOfFin hS) (T.orderEmbOfFin hT)).det := by
  have h := det_row_column_scales (fun i => (-1:ℝ)^((S.orderEmbOfFin hS) i).val)
    (fun j => (-1:ℝ)^((T.orderEmbOfFin hT) j).val)
    ((gaussianCollocation t x y)⁻¹.submatrix (S.orderEmbOfFin hS) (T.orderEmbOfFin hT))
  rw [prod_alternating,prod_alternating,← mul_assoc,← pow_add] at h
  exact (gaussianCollocation_inverse_minor_sign t x y S T hS hT).trans_eq h.symm

#print axioms gaussianCollocation_inverse_complement
#print axioms gaussianAlternatingInverse_minor_pos

end
end GaloisForLFunctions.HilbertMetric
