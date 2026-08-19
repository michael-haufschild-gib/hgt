import GaloisForLFunctions.HTGeometry.SiegelSet
import Mathlib.Algebra.Order.Chebyshev

/-!
# Quasi-diagonality on a Siegel set

On a Siegel set the quadratic form is comparable to its diagonal part: there is a constant
depending only on the dimension and the two Siegel parameters with

`A[v] ≥ c · ∑ dᵢ vᵢ²`.

Passing from `v` to the Jacobi coordinates `w = Uv` is harmless because the unipotent part is
bounded, hence so is its inverse, and the diagonal ratios are bounded by a single power of `t`
because the entries of the inverse below the diagonal vanish.

This is the estimate that makes both halves of reduction theory work: it turns the Siegel bounds
into a bound on the values of the form at lattice points.

* `exists_quasiDiagonal` : **the comparison, with a uniform constant.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

theorem JacobiData.det_eq_one (J : JacobiData n) : J.U.det = 1 :=
  det_eq_one_of_unipotent J.upper J.unit

theorem JacobiData.inv_upper (J : JacobiData n) : ∀ i j : Fin n, j < i → J.U⁻¹ i j = 0 := by
  haveI : Invertible J.U := Matrix.invertibleOfIsUnitDet _ (by rw [J.det_eq_one]; exact isUnit_one)
  have hbt : J.U.BlockTriangular id := fun i j hij => J.upper i j hij
  exact fun i j hij => Matrix.blockTriangular_inv_of_blockTriangular hbt hij

theorem JacobiData.mulVec_inv (J : JacobiData n) (v : Fin n → ℝ) :
    J.U⁻¹ *ᵥ (J.U *ᵥ v) = v := by
  haveI : Invertible J.U := Matrix.invertibleOfIsUnitDet _ (by rw [J.det_eq_one]; exact isUnit_one)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_of_invertible J.U),
    Matrix.one_mulVec]

theorem JacobiData.quadForm_eq (J : JacobiData n) (v : Fin n → ℝ) :
    v ⬝ᵥ (J.form *ᵥ v) = ∑ i, J.d i * ((J.U *ᵥ v) i) ^ 2 :=
  quadForm_jacobi (A := J.form) (U := J.U) (d := J.d) rfl v

/-- **Quasi-diagonality on a Siegel set.** -/
theorem exists_quasiDiagonal (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    ∃ c : ℝ, 0 < c ∧ ∀ J : JacobiData n, J.IsSiegel t u →
      ∀ v : Fin n → ℝ, c * (∑ i, J.d i * (v i) ^ 2) ≤ v ⬝ᵥ (J.form *ᵥ v) := by
  classical
  obtain ⟨C₀, hC₀⟩ := exists_unipotent_inv_bound n u
  set C : ℝ := max C₀ 1 with hC
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hCbound : ∀ U ∈ unipotentBall n u, ∀ i j, |U⁻¹ i j| ≤ C :=
    fun U hU i j => le_trans (hC₀ U hU i j) (le_max_left _ _)
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have htn : (0 : ℝ) < t ^ n := pow_pos ht0 n
  set M : ℝ := (n : ℝ) ^ 2 * C ^ 2 * t ^ n + 1 with hM
  have hM0 : (0 : ℝ) < M := by positivity
  refine ⟨1 / M, by positivity, fun J hS v => ?_⟩
  set w : Fin n → ℝ := J.U *ᵥ v with hw
  have hform : v ⬝ᵥ (J.form *ᵥ v) = ∑ j, J.d j * (w j) ^ 2 := J.quadForm_eq v
  have hSum0 : (0 : ℝ) ≤ ∑ j, J.d j * (w j) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (J.pos j).le (sq_nonneg _)
  have hUmem : J.U ∈ unipotentBall n u := ⟨J.upper, J.unit, hS.2⟩
  have hinvb : ∀ i j, |J.U⁻¹ i j| ≤ C := hCbound J.U hUmem
  have hvw : ∀ i, v i = ∑ j, J.U⁻¹ i j * w j := by
    intro i
    have := J.mulVec_inv v
    have hi := congrFun this i
    rw [hw]
    exact hi.symm
  -- the pointwise estimate
  have hterm : ∀ i j : Fin n,
      J.d i * (J.U⁻¹ i j * w j) ^ 2 ≤ C ^ 2 * t ^ n * (J.d j * (w j) ^ 2) := by
    intro i j
    rcases lt_or_ge (j : ℕ) (i : ℕ) with hji | hij
    · have hz : J.U⁻¹ i j = 0 := J.inv_upper i j (by exact hji)
      rw [hz, zero_mul]
      have : (0 : ℝ) ≤ C ^ 2 * t ^ n * (J.d j * (w j) ^ 2) :=
        mul_nonneg (by positivity) (mul_nonneg (J.pos j).le (sq_nonneg _))
      simpa using this
    · have hd : J.d i ≤ t ^ n * J.d j := J.d_le_pow_n ht hS hij
      have hsq : (J.U⁻¹ i j) ^ 2 ≤ C ^ 2 := by
        have := hinvb i j
        nlinarith [abs_nonneg (J.U⁻¹ i j), sq_abs (J.U⁻¹ i j)]
      have hwsq : (0 : ℝ) ≤ (w j) ^ 2 := sq_nonneg _
      have hdi : (0 : ℝ) < J.d i := J.pos i
      calc J.d i * (J.U⁻¹ i j * w j) ^ 2 = J.d i * (J.U⁻¹ i j) ^ 2 * (w j) ^ 2 := by ring
        _ ≤ (t ^ n * J.d j) * C ^ 2 * (w j) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ hwsq
            exact mul_le_mul hd hsq (sq_nonneg _)
              (mul_nonneg (le_of_lt htn) (J.pos j).le)
        _ = C ^ 2 * t ^ n * (J.d j * (w j) ^ 2) := by ring
  -- sum over `j`
  have hrow : ∀ i : Fin n, J.d i * (v i) ^ 2
      ≤ (n : ℝ) * (C ^ 2 * t ^ n) * (∑ j, J.d j * (w j) ^ 2) := by
    intro i
    have hcs : (v i) ^ 2 ≤ (n : ℝ) * ∑ j, (J.U⁻¹ i j * w j) ^ 2 := by
      rw [hvw i]
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun j => J.U⁻¹ i j * w j)
      simpa using this
    have hdi : (0 : ℝ) < J.d i := J.pos i
    calc J.d i * (v i) ^ 2
        ≤ J.d i * ((n : ℝ) * ∑ j, (J.U⁻¹ i j * w j) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (le_of_lt hdi)
      _ = (n : ℝ) * ∑ j, J.d i * (J.U⁻¹ i j * w j) ^ 2 := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ (n : ℝ) * ∑ j, C ^ 2 * t ^ n * (J.d j * (w j) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hterm i j) ?_
          positivity
      _ = (n : ℝ) * (C ^ 2 * t ^ n) * (∑ j, J.d j * (w j) ^ 2) := by
          rw [← Finset.mul_sum]
          ring
  have htotal : (∑ i, J.d i * (v i) ^ 2)
      ≤ (n : ℝ) ^ 2 * C ^ 2 * t ^ n * (∑ j, J.d j * (w j) ^ 2) := by
    calc (∑ i, J.d i * (v i) ^ 2)
        ≤ ∑ _i : Fin n, (n : ℝ) * (C ^ 2 * t ^ n) * (∑ j, J.d j * (w j) ^ 2) :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = (n : ℝ) * ((n : ℝ) * (C ^ 2 * t ^ n) * (∑ j, J.d j * (w j) ^ 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (n : ℝ) ^ 2 * C ^ 2 * t ^ n * (∑ j, J.d j * (w j) ^ 2) := by ring
  rw [hform, div_mul_eq_mul_div, one_mul, div_le_iff₀ hM0]
  refine le_trans htotal ?_
  rw [hM]
  nlinarith [hSum0]

end GaloisForLFunctions.HTGeometry
