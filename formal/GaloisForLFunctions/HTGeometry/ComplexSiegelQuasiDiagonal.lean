import GaloisForLFunctions.HTGeometry.ComplexSiegelSet
import GaloisForLFunctions.HTGeometry.ComplexJacobiCoercivity

/-!
# Quasi-diagonality on a Hermitian Siegel set

The bounded inverse of the complex upper-unipotent factor and the ordered Jacobi diagonal give a
uniform comparison between a Hermitian Siegel form and its diagonal quadratic form.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- Exact real quadratic form of complex Jacobi data. -/
theorem ComplexJacobiData.quadForm_eq (J : ComplexJacobiData n) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (J.form.mulVec v)).re =
      ∑ i, J.d i * ‖J.U.mulVec v i‖ ^ (2 : ℕ) := by
  exact re_complex_jacobi_quadForm J.U J.d v

/-- A complex Hermitian Siegel set is uniformly quasi-diagonal. -/
theorem exists_complexSiegel_quasiDiagonal (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    ∃ c : ℝ, 0 < c ∧ ∀ J : ComplexJacobiData n, J.IsSiegel t u →
      ∀ v : Fin n → ℂ,
        c * (∑ i, J.d i * ‖v i‖ ^ (2 : ℕ)) ≤ (star v ⬝ᵥ (J.form.mulVec v)).re := by
  classical
  obtain ⟨C₀, hC₀⟩ := exists_complex_unipotent_inv_bound n u
  set C : ℝ := max C₀ 1 with hC
  have hCbound : ∀ U ∈ complexUnipotentBall n u,
      ∀ i j, ‖U⁻¹ i j‖ ≤ C :=
    fun U hU i j => le_trans (hC₀ U hU i j) (le_max_left _ _)
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have htn : (0 : ℝ) < t ^ n := pow_pos ht0 n
  set M : ℝ := (n : ℝ) ^ (2 : ℕ) * C ^ (2 : ℕ) * t ^ n + 1 with hM
  have hM0 : (0 : ℝ) < M := by positivity
  refine ⟨1 / M, by positivity, fun J hS v => ?_⟩
  set w : Fin n → ℂ := J.U.mulVec v with hw
  have hform : (star v ⬝ᵥ (J.form.mulVec v)).re =
      ∑ j, J.d j * ‖w j‖ ^ (2 : ℕ) := J.quadForm_eq v
  have hSum0 : (0 : ℝ) ≤ ∑ j, J.d j * ‖w j‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (J.pos j).le (sq_nonneg _)
  have hUmem : J.U ∈ complexUnipotentBall n u := ⟨J.upper, J.unit, hS.2⟩
  have hinvb : ∀ i j, ‖J.U⁻¹ i j‖ ≤ C := hCbound J.U hUmem
  have hvw : ∀ i, v i = ∑ j, J.U⁻¹ i j * w j := by
    intro i
    have hinv : J.U⁻¹.mulVec (J.U.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (by rw [J.det_eq_one]; exact isUnit_one),
        Matrix.one_mulVec]
    have hi := congrFun hinv i
    rw [hw]
    exact hi.symm
  have hterm : ∀ i j : Fin n,
      J.d i * ‖J.U⁻¹ i j * w j‖ ^ (2 : ℕ) ≤
        C ^ (2 : ℕ) * t ^ n * (J.d j * ‖w j‖ ^ (2 : ℕ)) := by
    intro i j
    rcases lt_or_ge (j : ℕ) (i : ℕ) with hji | hij
    · have hz : J.U⁻¹ i j = 0 := J.inv_upper i j hji
      rw [hz, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact mul_nonneg (mul_nonneg (sq_nonneg C) htn.le)
        (mul_nonneg (J.pos j).le (sq_nonneg ‖w j‖))
    · have hd : J.d i ≤ t ^ n * J.d j := J.d_le_pow_n ht hS hij
      have hsq : ‖J.U⁻¹ i j‖ ^ (2 : ℕ) ≤ C ^ (2 : ℕ) := by
        nlinarith [hinvb i j, norm_nonneg (J.U⁻¹ i j)]
      rw [norm_mul, mul_pow]
      have hwsq : 0 ≤ ‖w j‖ ^ (2 : ℕ) := sq_nonneg _
      calc
        J.d i * (‖J.U⁻¹ i j‖ ^ (2 : ℕ) * ‖w j‖ ^ (2 : ℕ)) =
            (J.d i * ‖J.U⁻¹ i j‖ ^ (2 : ℕ)) * ‖w j‖ ^ (2 : ℕ) := by ring
        _ ≤ ((t ^ n * J.d j) * C ^ (2 : ℕ)) * ‖w j‖ ^ (2 : ℕ) := by
          refine mul_le_mul_of_nonneg_right ?_ hwsq
          exact mul_le_mul hd hsq (sq_nonneg _)
            (mul_nonneg htn.le (J.pos j).le)
        _ = C ^ (2 : ℕ) * t ^ n * (J.d j * ‖w j‖ ^ (2 : ℕ)) := by ring
  have hrow : ∀ i : Fin n,
      J.d i * ‖v i‖ ^ (2 : ℕ) ≤
        (n : ℝ) * (C ^ (2 : ℕ) * t ^ n) * ∑ j, J.d j * ‖w j‖ ^ (2 : ℕ) := by
    intro i
    have hcs : ‖v i‖ ^ (2 : ℕ) ≤ (n : ℝ) * ∑ j, ‖J.U⁻¹ i j * w j‖ ^ (2 : ℕ) := by
      rw [hvw i]
      simpa using norm_sum_sq_le_card_mul (fun j : Fin n => J.U⁻¹ i j * w j)
    calc
      J.d i * ‖v i‖ ^ (2 : ℕ) ≤
          J.d i * ((n : ℝ) * ∑ j, ‖J.U⁻¹ i j * w j‖ ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hcs (J.pos i).le
      _ = (n : ℝ) * ∑ j, J.d i * ‖J.U⁻¹ i j * w j‖ ^ (2 : ℕ) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ (n : ℝ) * ∑ j, C ^ (2 : ℕ) * t ^ n * (J.d j * ‖w j‖ ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j _ => hterm i j) (Nat.cast_nonneg n)
      _ = (n : ℝ) * (C ^ (2 : ℕ) * t ^ n) * ∑ j, J.d j * ‖w j‖ ^ (2 : ℕ) := by
        rw [← Finset.mul_sum]
        ring
  have htotal : ∑ i, J.d i * ‖v i‖ ^ (2 : ℕ) ≤
      (n : ℝ) ^ (2 : ℕ) * C ^ (2 : ℕ) * t ^ n * ∑ j, J.d j * ‖w j‖ ^ (2 : ℕ) := by
    calc
      ∑ i, J.d i * ‖v i‖ ^ (2 : ℕ) ≤
          ∑ _i : Fin n,
            (n : ℝ) * (C ^ (2 : ℕ) * t ^ n) * ∑ j, J.d j * ‖w j‖ ^ (2 : ℕ) :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = (n : ℝ) *
          ((n : ℝ) * (C ^ (2 : ℕ) * t ^ n) * ∑ j, J.d j * ‖w j‖ ^ (2 : ℕ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (n : ℝ) ^ (2 : ℕ) * C ^ (2 : ℕ) * t ^ n * ∑ j, J.d j * ‖w j‖ ^ (2 : ℕ) := by ring
  rw [hform, div_mul_eq_mul_div, one_mul, div_le_iff₀ hM0]
  refine htotal.trans ?_
  rw [hM]
  nlinarith

end GaloisForLFunctions.HTGeometry
