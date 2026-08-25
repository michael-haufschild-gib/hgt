import GaloisForLFunctions.RHTower.Sieve.MollifiedTwistedDiagonalProductEnergy
import GaloisForLFunctions.RHTower.Sieve.DirichletBilinear
import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralMeanValue

/-!
# Mollified diagonal as exact finite Dirichlet-convolution energy

This file converts the positive-natural product-fibre presentation of the exact zero-twist
diagonal to the zero-based finite `dirConv` representation used by the Levinson arithmetic layer.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Finset

private theorem sum_fin_succ_eq_sum_Icc_generic
    {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → R) :
    ∑ n : Fin N, f ((n : ℕ) + 1) = ∑ k ∈ Finset.Icc 1 N, f k := by
  classical
  rw [← image_succ_univ N, Finset.sum_image (succ_injOn N)]

/-- A positive-natural product-fibre coefficient is exactly the corresponding zero-based finite
Dirichlet convolution coefficient. -/
theorem mollifiedProductCoeff_Icc_eq_dirConv
    (a u : ℕ → ℂ) (L M : ℕ) (r : Fin (L * M)) :
    mollifiedProductCoeff a u (Finset.Icc 1 L) (Finset.Icc 1 M) ((r : ℕ) + 1) =
      dirConv L M (fun n => a ((n : ℕ) + 1)) (fun k => u ((k : ℕ) + 1)) r := by
  classical
  unfold mollifiedProductCoeff dirConv
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_product]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  symm
  calc
    (∑ n : Fin L, ∑ k : Fin M,
        if ((n : ℕ) + 1) * ((k : ℕ) + 1) = (r : ℕ) + 1 then
          a ((n : ℕ) + 1) * u ((k : ℕ) + 1) else 0) =
        ∑ n ∈ Finset.Icc 1 L, ∑ k : Fin M,
          if n * ((k : ℕ) + 1) = (r : ℕ) + 1 then
            a n * u ((k : ℕ) + 1) else 0 := by
      exact sum_fin_succ_eq_sum_Icc_generic L (fun n =>
        ∑ k : Fin M, if n * ((k : ℕ) + 1) = (r : ℕ) + 1 then
          a n * u ((k : ℕ) + 1) else 0)
    _ = ∑ n ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 M,
          if n * k = (r : ℕ) + 1 then a n * u k else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact sum_fin_succ_eq_sum_Icc_generic M (fun k =>
        if n * k = (r : ℕ) + 1 then a n * u k else 0)

/-- The complete self-paired zero-twist diagonal is the squared `ℓ²` energy of the exact finite
Dirichlet convolution, including the whole product range rather than only the short head. -/
theorem mollifiedTwistedDiagonalIcc_zero_self_eq_sum_normSq_dirConv
    (a u : ℕ → ℂ) (L M : ℕ) :
    mollifiedTwistedDiagonalIcc a a u u L M 0 =
      ∑ r : Fin (L * M),
        ((Complex.normSq
          (dirConv L M (fun n => a ((n : ℕ) + 1))
            (fun k => u ((k : ℕ) + 1)) r) : ℝ) : ℂ) := by
  rw [mollifiedTwistedDiagonalIcc_zero_self_eq_sum_normSq]
  let P : Finset (ℕ × ℕ) := Finset.Icc 1 L ×ˢ Finset.Icc 1 M
  let prod : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  let energy : ℕ → ℂ := fun r =>
    ((Complex.normSq
      (mollifiedProductCoeff a u (Finset.Icc 1 L) (Finset.Icc 1 M) r) : ℝ) : ℂ)
  have hsubset : P.image prod ⊆ Finset.Icc 1 (L * M) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    have hp' := Finset.mem_product.mp hp
    have hn := Finset.mem_Icc.mp hp'.1
    have hk := Finset.mem_Icc.mp hp'.2
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hn.1 hk.1, Nat.mul_le_mul hn.2 hk.2⟩
  have hzero : ∀ r ∈ Finset.Icc 1 (L * M), r ∉ P.image prod → energy r = 0 := by
    intro r hr hrnot
    have hcoeff :
        mollifiedProductCoeff a u (Finset.Icc 1 L) (Finset.Icc 1 M) r = 0 := by
      unfold mollifiedProductCoeff
      apply Finset.sum_eq_zero
      intro p hp
      exfalso
      apply hrnot
      exact Finset.mem_image.mpr
        ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    simp [energy, hcoeff]
  have hsupport : (∑ r ∈ P.image prod, energy r) =
      ∑ r ∈ Finset.Icc 1 (L * M), energy r :=
    Finset.sum_subset hsubset hzero
  change (∑ r ∈ P.image prod, energy r) = _
  rw [hsupport]
  rw [← sum_fin_succ_eq_sum_Icc_generic (L * M) energy]
  apply Finset.sum_congr rfl
  intro r hr
  unfold energy
  rw [mollifiedProductCoeff_Icc_eq_dirConv]

end RHTower.Sieve
