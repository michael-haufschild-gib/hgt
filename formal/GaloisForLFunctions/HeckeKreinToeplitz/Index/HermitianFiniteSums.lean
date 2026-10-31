import GaloisForLFunctions.HTGeometry.AppellHumbertGaussianBound

/-!
# Finite sums in Hermitian forms

Sesquilinearity expands finite combinations into Gram coefficients. Cauchy–Schwarz turns unit diagonal bounds into a uniform bound by the squared sum of coefficient norms.
-/

open Complex Finset
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]

/-- A Hermitian form is additive over finite sums in its linear argument. -/
theorem hermitianForm_sum_left {H : V → V → ℂ} (hH : IsHermitianForm H)
    (v : ι → V) (w : V) : H (∑ i, v i) w = ∑ i, H (v i) w := by
  let L : V →ₗ[ℂ] ℂ :=
    { toFun := fun x => H x w
      map_add' := fun x y => hH.add_left x y w
      map_smul' := fun a x => by
        simpa only [smul_eq_mul, RingHom.id_apply] using hH.smul_left a x w }
  exact map_sum L v univ

/-- Conjugate symmetry gives finite additivity in the other argument. -/
theorem hermitianForm_sum_right {H : V → V → ℂ} (hH : IsHermitianForm H)
    (v : V) (w : ι → V) : H v (∑ i, w i) = ∑ i, H v (w i) := by
  rw [hH.symm, hermitianForm_sum_left hH, star_sum]
  apply sum_congr rfl
  intro i _
  rw [hH.symm, star_star]

/-- Finite linear combinations expand into their Hermitian Gram coefficients. -/
theorem hermitianForm_fin_synthesis {κ : Type*} [Fintype κ]
    {H : V → V → ℂ} (hH : IsHermitianForm H) (v : ι → V) (w : κ → V)
    (c : ι → ℂ) (d : κ → ℂ) :
    H (∑ i, c i • v i) (∑ j, d j • w j) =
      ∑ i, ∑ j, c i * star (d j) * H (v i) (w j) := by
  rw [hermitianForm_sum_left hH]
  apply sum_congr rfl
  intro i _
  rw [hermitianForm_sum_right hH]
  apply sum_congr rfl
  intro j _
  rw [hH.smul_left, hH.smul_right, mul_assoc]

/-- Unit diagonal bounds on generators give an `ℓ¹` bound on every finite linear combination. -/
theorem positiveHermitianForm_fin_sum_re_le {H : V → V → ℂ} (hH : IsHermitianForm H)
    (hpos : ∀ v, 0 ≤ (H v v).re) (v : ι → V) (hd : ∀ i, (H (v i) (v i)).re ≤ 1)
    (c : ι → ℂ) :
    (H (∑ i, c i • v i) (∑ i, c i • v i)).re ≤ (∑ i, ‖c i‖) ^ 2 := by
  have hentry (i j : ι) : ‖H (v i) (v j)‖ ≤ 1 := by
    have hcs := hH.norm_sq_le hpos (v i) (v j)
    have hprod : (H (v i) (v i)).re * (H (v j) (v j)).re ≤ 1 := by
      calc
        _ ≤ 1 * (H (v j) (v j)).re := mul_le_mul_of_nonneg_right (hd i) (hpos (v j))
        _ ≤ 1 := by simpa only [one_mul] using hd j
    nlinarith only [hcs, hprod, norm_nonneg (H (v i) (v j))]
  rw [hermitianForm_fin_synthesis hH]
  calc
    _ ≤ ‖∑ i, ∑ j, c i * star (c j) * H (v i) (v j)‖ := Complex.re_le_norm _
    _ ≤ ∑ i, ‖∑ j, c i * star (c j) * H (v i) (v j)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖c i * star (c j) * H (v i) (v j)‖ :=
      sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖c i‖ * ‖c j‖ := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      simp only [norm_mul, norm_star]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hentry i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ i, ‖c i‖) ^ 2 := by rw [sq, sum_mul_sum]

#print axioms positiveHermitianForm_fin_sum_re_le
end GaloisForLFunctions.HeckeKreinToeplitz
