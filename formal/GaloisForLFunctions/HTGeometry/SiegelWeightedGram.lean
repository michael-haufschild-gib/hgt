import GaloisForLFunctions.HTGeometry.SiegelSubsetProduct
import GaloisForLFunctions.HTGeometry.CauchyBinet

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- **Cauchy–Binet for a weighted Gram matrix.**  Each maximal minor of the frame contributes its
square, weighted by the product of the corresponding weights. -/
theorem factorial_mul_det_weightedGram {k N : ℕ} (d : Fin N → ℝ) (C : Matrix (Fin N) (Fin k) ℝ) :
    (Nat.factorial k : ℝ) * (Cᵀ * Matrix.diagonal d * C).det
      = ∑ f : Fin k → Fin N, (∏ b, d (f b)) * ((C.submatrix f id).det) ^ (2 : ℕ) := by
  classical
  rw [GaloisForLFunctions.factorial_mul_det_mul (Cᵀ * Matrix.diagonal d) C]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hsub : ((Cᵀ * Matrix.diagonal d).submatrix id f)
      = (C.submatrix f id)ᵀ * Matrix.diagonal (fun b : Fin k => d (f b)) := by
    ext a b
    have hL : (Cᵀ * Matrix.diagonal d) a (f b) = C (f b) a * d (f b) := by
      rw [Matrix.mul_apply,
        Finset.sum_eq_single (f b) (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
          (fun hcon => absurd (Finset.mem_univ (f b)) hcon),
        Matrix.transpose_apply, Matrix.diagonal_apply_eq]
    have hR : ((C.submatrix f id)ᵀ * Matrix.diagonal (fun b : Fin k => d (f b))) a b
        = C (f b) a * d (f b) := by
      rw [Matrix.mul_apply,
        Finset.sum_eq_single b (fun q _ hq => by rw [Matrix.diagonal_apply_ne _ hq, mul_zero])
          (fun hcon => absurd (Finset.mem_univ b) hcon),
        Matrix.transpose_apply, Matrix.diagonal_apply_eq]
      rfl
    show (Cᵀ * Matrix.diagonal d) a (f b) = _
    rw [hL, hR]
  rw [hsub, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- **A rank-`k` integral frame has weighted Gram determinant bounded below by the leading weight
product.**  Some maximal minor of the frame is a nonzero integer, so its square is at least one, and
the increasing weight bound compares its weight product with the leading one. -/
theorem prod_d_le_det_weightedGram {k n : ℕ} (hk : k ≤ n) {d : Fin n → ℝ} (hd : ∀ i, 0 < d i)
    {K : ℝ} (hK : 1 ≤ K) (hmono : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → d i ≤ K * d j)
    (Z : Matrix (Fin n) (Fin k) ℤ)
    (hpos : 0 < ((Z.map (fun z : ℤ => (z : ℝ)))ᵀ * Matrix.diagonal d
        * (Z.map (fun z : ℤ => (z : ℝ)))).det) :
    (∏ j : Fin k, d (Fin.castLE hk j))
      ≤ (Nat.factorial k : ℝ) * K ^ k
        * ((Z.map (fun z : ℤ => (z : ℝ)))ᵀ * Matrix.diagonal d
            * (Z.map (fun z : ℤ => (z : ℝ)))).det := by
  classical
  set C : Matrix (Fin n) (Fin k) ℝ := Z.map (fun z : ℤ => (z : ℝ)) with hC
  set T : ℝ := (Cᵀ * Matrix.diagonal d * C).det with hT
  have hCB := factorial_mul_det_weightedGram d C
  have hnn : ∀ f : Fin k → Fin n, 0 ≤ (∏ b, d (f b)) * ((C.submatrix f id).det) ^ (2 : ℕ) :=
    fun f => mul_nonneg (Finset.prod_nonneg fun b _ => (hd _).le) (sq_nonneg _)
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hsumpos : 0 < ∑ f : Fin k → Fin n, (∏ b, d (f b)) * ((C.submatrix f id).det) ^ (2 : ℕ) := by
    rw [← hCB]
    exact mul_pos hfac hpos
  obtain ⟨f₀, -, hf₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hsumpos)
  have hdet0 : (C.submatrix f₀ id).det ≠ 0 := by
    intro hcon
    exact hf₀ (by rw [hcon]; ring)
  have hinj : Function.Injective f₀ := by
    intro a b hab
    by_contra hne
    refine hdet0 (Matrix.det_zero_of_row_eq hne ?_)
    funext q
    show C (f₀ a) q = C (f₀ b) q
    rw [hab]
  have hcast : (C.submatrix f₀ id).det = (((Z.submatrix f₀ id).det : ℤ) : ℝ) := by
    have hmap : C.submatrix f₀ id = (Z.submatrix f₀ id).map (fun z : ℤ => (z : ℝ)) := rfl
    rw [hmap]
    exact (RingHom.map_det (Int.castRingHom ℝ) (Z.submatrix f₀ id)).symm
  have hge1 : (1 : ℝ) ≤ ((C.submatrix f₀ id).det) ^ (2 : ℕ) :=
    one_le_sq_of_int_ne_zero hcast hdet0
  have hprodpos : (0 : ℝ) < ∏ b, d (f₀ b) := Finset.prod_pos fun b _ => hd _
  have hterm : (∏ b, d (f₀ b)) ≤ (∏ b, d (f₀ b)) * ((C.submatrix f₀ id).det) ^ (2 : ℕ) := by
    nlinarith [hprodpos, hge1]
  have hsingle : (∏ b, d (f₀ b)) * ((C.submatrix f₀ id).det) ^ (2 : ℕ)
      ≤ ∑ f : Fin k → Fin n, (∏ b, d (f b)) * ((C.submatrix f id).det) ^ (2 : ℕ) :=
    Finset.single_le_sum (fun f _ => hnn f) (Finset.mem_univ f₀)
  have hfin : (∏ b, d (f₀ b)) ≤ (Nat.factorial k : ℝ) * T := by
    rw [hCB]
    exact le_trans hterm hsingle
  have hK0 : (0 : ℝ) ≤ K ^ k := pow_nonneg (le_trans zero_le_one hK) k
  calc (∏ j : Fin k, d (Fin.castLE hk j)) ≤ K ^ k * ∏ b, d (f₀ b) :=
        prod_castLE_le_prod_of_injective hk hd hmono hinj
    _ ≤ K ^ k * ((Nat.factorial k : ℝ) * T) := mul_le_mul_of_nonneg_left hfin hK0
    _ = (Nat.factorial k : ℝ) * K ^ k * T := by ring

end GaloisForLFunctions.HTGeometry
