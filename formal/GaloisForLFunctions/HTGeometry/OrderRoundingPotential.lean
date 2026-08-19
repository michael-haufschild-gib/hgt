import GaloisForLFunctions.HTGeometry.HumbertPositivity

/-!
# Rounding in an order, and the potential in Humbert coordinates

Two inputs to the reduction theory over an order.

The first replaces division with remainder: the embeddings of the order form a full lattice in
`ℝ^d`, so every real vector is within a fixed distance of the embedding vector of a ring element.
Rounding the coordinates in the basis is all it takes.

The second identifies the leading minors of a Humbert form at the multiples of `d` — the covolumes of
the sublattices spanned by the first few basis vectors *over the order* — as the products of the
norms of the Gram–Schmidt diagonals, up to a power of the discriminant.  So the potential that runs
the descent over the order is, up to a constant, the ambient potential of the integral theory.

* `exists_round` : **size reduction over an order.**
* `det_humbertBlock` : the determinant of a diagonal block.
* `det_leadingBlock_humbertAmbient` : **the leading minors at the multiples of `d`.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ} {R : Type*} [CommRing R]

/-- **Size reduction over an order**: every real vector is within a fixed distance of the embedding
vector of a ring element. -/
theorem exists_round (T : RealOrderData R d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → ℝ, ∃ α : R, ∀ v, |x v - T.emb v α| ≤ C := by
  classical
  have hu : IsUnit T.embMatrix.det := T.invertible
  refine ⟨∑ w : Fin d, ∑ k : Fin d, |T.embMatrix w k|, ?_, ?_⟩
  · exact Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  intro x
  set y : Fin d → ℝ := T.embMatrix⁻¹ *ᵥ x with hy
  set n : Fin d → ℤ := fun k => round (y k) with hn
  refine ⟨∑ k, n k • T.basis k, fun v => ?_⟩
  have hemb : T.emb v (∑ k, n k • T.basis k) = ∑ k, (n k : ℝ) * T.embMatrix v k := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_zsmul, zsmul_eq_mul]; rfl
  have hx : x v = ∑ k, T.embMatrix v k * y k := by
    have hmul : T.embMatrix *ᵥ y = x := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    have := congrFun hmul v
    exact this.symm
  have hdiff : x v - T.emb v (∑ k, n k • T.basis k)
      = ∑ k, T.embMatrix v k * (y k - (n k : ℝ)) := by
    rw [hx, hemb, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin d)),
      |T.embMatrix v k * (y k - (n k : ℝ))| ≤ |T.embMatrix v k| := by
    intro k _
    rw [abs_mul]
    have hround : |y k - (n k : ℝ)| ≤ 1 := by
      have := abs_sub_round (y k)
      linarith
    calc |T.embMatrix v k| * |y k - (n k : ℝ)| ≤ |T.embMatrix v k| * 1 :=
          mul_le_mul_of_nonneg_left hround (abs_nonneg _)
      _ = |T.embMatrix v k| := mul_one _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  exact Finset.single_le_sum
    (f := fun w : Fin d => ∑ k : Fin d, |T.embMatrix w k|)
    (fun w _ => Finset.sum_nonneg fun k _ => abs_nonneg _) (Finset.mem_univ v)

/-- The determinant of a diagonal block of a Humbert form. -/
theorem det_humbertBlock (T : RealOrderData R d) (Δ : Fin d → ℝ) :
    (humbertBlock T Δ).det = T.embMatrix.det ^ 2 * ∏ v, Δ v := by
  rw [humbertBlock, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- **The leading minors of a Humbert form at the multiples of `d`.**  They are the products of the
norms of the Gram–Schmidt diagonals, up to a power of the determinant of the embedding matrix. -/
theorem det_leadingBlock_humbertAmbient (T : RealOrderData R d) (Jv : Fin d → JacobiData nb)
    (Jm : Fin nb → JacobiData d) (hJm : ∀ m, (Jm m).form = humbertBlock T (fun v => (Jv v).d m))
    {i : ℕ} (hi : i ≤ nb) (hk : i * d ≤ nb * d) :
    (leadingBlock hk (humbertAmbient T Jv Jm).form).det
      = ∏ m : Fin i, (T.embMatrix.det ^ 2 * ∏ v, (Jv v).d (Fin.castLE hi m)) := by
  classical
  rw [det_leadingBlock_form hk,
    ← Equiv.prod_comp (finProdFinEquiv (m := i) (n := d))
      (fun p : Fin (i * d) => (humbertAmbient T Jv Jm).d (Fin.castLE hk p)),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun m' _ => ?_
  have hstep : ∀ k : Fin d,
      (humbertAmbient T Jv Jm).d (Fin.castLE hk (finProdFinEquiv (m', k)))
        = (Jm (Fin.castLE hi m')).d k := by
    intro k
    have hd0 : 0 < d := lt_of_le_of_lt (Nat.zero_le _) k.isLt
    have hval : ((Fin.castLE hk (finProdFinEquiv (m', k)) : Fin (nb * d)) : ℕ)
        = (k : ℕ) + d * (m' : ℕ) := by
      rw [Fin.val_castLE]
      exact val_finProdFinEquiv m' k
    have hdiv : (Fin.divNat (Fin.castLE hk (finProdFinEquiv (m', k))) : Fin nb)
        = Fin.castLE hi m' := by
      refine Fin.ext ?_
      show ((Fin.castLE hk (finProdFinEquiv (m', k)) : Fin (nb * d)) : ℕ) / d = (m' : ℕ)
      rw [hval, Nat.add_mul_div_left _ _ hd0, Nat.div_eq_of_lt k.isLt, Nat.zero_add]
    have hmod : (Fin.modNat (Fin.castLE hk (finProdFinEquiv (m', k))) : Fin d) = k := by
      refine Fin.ext ?_
      show ((Fin.castLE hk (finProdFinEquiv (m', k)) : Fin (nb * d)) : ℕ) % d = (k : ℕ)
      rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt]
    rw [humbertAmbient_d, hdiv, hmod]
  rw [Finset.prod_congr rfl (fun k (_ : k ∈ Finset.univ) => hstep k),
    ← (Jm (Fin.castLE hi m')).det_form, hJm, det_humbertBlock]

end GaloisForLFunctions.HTGeometry
