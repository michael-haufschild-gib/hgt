import GaloisForLFunctions.SelbergClass.Primon.KestenDirichletGreenKernel
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Determinants of the Dirichlet Green sections

The terminal rank-one perturbation gives an exact determinant factor.
Although every fixed Dirichlet entry converges to the infinite Green
entry, the ratio of the two finite determinants decreases to `1-q^2`.
This nonzero boundary effect survives at arbitrarily large depth.
-/

open _root_.RHTower Matrix Filter Topology
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem gap_pos (p : Nat.Primes) : 0 < 1 - primeReciprocal p ^ 2 :=
  sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide))

private theorem denominator_pos (p : Nat.Primes) (n : ℕ) :
    0 < 1 - primeReciprocal p ^ (2 * n + 3) :=
  sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by omega))

private theorem one_add_ne (p : Nat.Primes) : 1 + primeReciprocal p ≠ 0 := by
  have := primeReciprocal_pos p
  positivity

/-- The source determinant differs from the exact inverse determinant by its terminal response. -/
theorem det_kestenCompressedGreenPencil_mul_green (p : Nat.Primes) (n : ℕ) :
    (kestenCompressedGreenPencil p n).det * (kestenFiniteGreen p n).det =
      1 + primeReciprocal p * kestenGreenEntry p n n := by
  have hG : IsUnit (kestenFiniteGreen p n).det :=
    isUnit_iff_ne_zero.mpr (det_kestenFiniteGreen_pos p n).ne'
  have h : kestenCompressedGreenPencil p n * kestenFiniteGreen p n =
      1 + Matrix.replicateCol (Fin 1) (Pi.single (Fin.last n) (primeReciprocal p)) *
        Matrix.replicateRow (Fin 1) (fun j : Fin (n + 1) => kestenGreenEntry p n j) := by
    rw [kestenCompressedGreenPencil_eq_inverse_add_terminal, Matrix.add_mul,
      Matrix.nonsing_inv_mul _ hG]
    congr 1
    ext i j
    simp only [kestenTerminalSelfEnergy, Matrix.diagonal_mul, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, kestenFiniteGreen,
      Finset.univ_unique, Finset.sum_singleton]
    by_cases hi : i = Fin.last n
    · subst i
      simp
    · simp [Pi.single_apply, hi, eq_comm]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow] at hd
  simpa [dotProduct, Pi.single_apply, mul_comm] using hd

/-- The finite source determinant is a geometric gap divided by its bulk factor. -/
theorem det_kestenCompressedGreenPencil (p : Nat.Primes) (n : ℕ) :
    (kestenCompressedGreenPencil p n).det =
      (1 - primeReciprocal p ^ (2 * n + 3)) /
        (primeReciprocal p ^ (n + 1) * (1 - primeReciprocal p)) := by
  calc
    _ = (1 + primeReciprocal p * kestenGreenEntry p n n) / (kestenFiniteGreen p n).det :=
      (eq_div_iff (det_kestenFiniteGreen_pos p n).ne').mpr
        (det_kestenCompressedGreenPencil_mul_green p n)
    _ = _ := by
      rw [one_add_reciprocal_kestenGreenEntry_diagonal, det_kestenFiniteGreen]
      field_simp [(gap_pos p).ne', (primeReciprocal_pos p).ne', one_add_ne p,
        (sub_pos.mpr (primeReciprocal_lt_one p)).ne']
      ring

/-- The finite Dirichlet determinant is the reciprocal source determinant. -/
theorem det_kestenDirichletGreen (p : Nat.Primes) (n : ℕ) :
    (kestenDirichletGreen p n).det =
      primeReciprocal p ^ (n + 1) * (1 - primeReciprocal p) /
        (1 - primeReciprocal p ^ (2 * n + 3)) := by
  rw [kestenDirichletGreen, Matrix.det_nonsing_inv, Ring.inverse_eq_inv,
    det_kestenCompressedGreenPencil, inv_div]

/-- The relative determinant isolates the entire effect of the terminal boundary. -/
theorem kestenDirichletGreen_det_ratio (p : Nat.Primes) (n : ℕ) :
    (kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det =
      (1 - primeReciprocal p ^ 2) / (1 - primeReciprocal p ^ (2 * n + 3)) := by
  rw [det_kestenDirichletGreen, det_kestenFiniteGreen]
  field_simp [(primeReciprocal_pos p).ne', one_add_ne p, (denominator_pos p n).ne']
  ring

/-- Every finite relative determinant strictly exceeds its limiting boundary factor. -/
theorem kestenDirichletGreen_det_ratio_lower (p : Nat.Primes) (n : ℕ) :
    1 - primeReciprocal p ^ 2 < (kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det := by
  rw [kestenDirichletGreen_det_ratio]
  apply (lt_div_iff₀ (denominator_pos p n)).mpr
  have h := mul_pos (gap_pos p) (pow_pos (primeReciprocal_pos p) (2 * n + 3))
  nlinarith only [h]

/-- Dirichlet truncation strictly decreases the finite determinant. -/
theorem kestenDirichletGreen_det_ratio_lt_one (p : Nat.Primes) (n : ℕ) :
    (kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det < 1 := by
  rw [kestenDirichletGreen_det_ratio]
  apply (div_lt_iff₀ (denominator_pos p n)).mpr
  rw [show 2 * n + 3 = 2 + (2 * n + 1) by omega, pow_add]
  have h := mul_pos (pow_pos (primeReciprocal_pos p) 2)
    (sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p)
      (by omega : 2 * n + 1 ≠ 0)))
  nlinarith only [h]

/-- The relative determinant strictly decreases as the terminal boundary recedes. -/
theorem strictAnti_kestenDirichletGreen_det_ratio (p : Nat.Primes) :
    StrictAnti (fun n => (kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [kestenDirichletGreen_det_ratio, kestenDirichletGreen_det_ratio]
  apply (div_lt_div_iff₀ (denominator_pos p (n + 1)) (denominator_pos p n)).mpr
  rw [show 2 * (n + 1) + 3 = (2 * n + 3) + 2 by omega, pow_add]
  have h := mul_pos (gap_pos p)
    (mul_pos (pow_pos (primeReciprocal_pos p) (2 * n + 3)) (gap_pos p))
  nlinarith only [h]

/-- Local entrywise recovery coexists with the nontrivial limiting determinant factor `1-q^2`. -/
theorem tendsto_kestenDirichletGreen_det_ratio (p : Nat.Primes) :
    Tendsto (fun n => (kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det)
      atTop (𝓝 (1 - primeReciprocal p ^ 2)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (primeReciprocal p))
    (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide : (2 : ℕ) ≠ 0))
  have he (n : ℕ) : (kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det =
      (1 - primeReciprocal p ^ 2) / (1 - primeReciprocal p ^ 3 * (primeReciprocal p ^ 2) ^ n) := by
    rw [kestenDirichletGreen_det_ratio, show 2 * n + 3 = 3 + 2 * n by omega, pow_add, pow_mul]
  have h := (tendsto_const_nhds (x := 1 - primeReciprocal p ^ 2)).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (hp.const_mul (primeReciprocal p ^ 3))) (by norm_num)
  simpa only [mul_zero, sub_zero, div_one] using h.congr (fun n => (he n).symm)

end
end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.det_kestenCompressedGreenPencil_mul_green
#print axioms GaloisForLFunctions.SelbergClass.Primon.det_kestenCompressedGreenPencil
#print axioms GaloisForLFunctions.SelbergClass.Primon.det_kestenDirichletGreen
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenDirichletGreen_det_ratio
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenDirichletGreen_det_ratio_lower
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenDirichletGreen_det_ratio_lt_one
#print axioms GaloisForLFunctions.SelbergClass.Primon.strictAnti_kestenDirichletGreen_det_ratio
#print axioms GaloisForLFunctions.SelbergClass.Primon.tendsto_kestenDirichletGreen_det_ratio
