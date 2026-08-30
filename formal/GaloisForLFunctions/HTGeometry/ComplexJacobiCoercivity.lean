import GaloisForLFunctions.HTGeometry.ComplexUnipotentInverseBound
import GaloisForLFunctions.HTGeometry.DiagonalQuadraticForm
import GaloisForLFunctions.HTGeometry.MatrixStarAutomorphismInner
import GaloisForLFunctions.HTGeometry.PencilCauchySchwarz

/-!
# Uniform coercivity of bounded complex Jacobi factors

The inverse bound for a bounded complex upper-unipotent factor turns a positive floor on its
Jacobi diagonal into one uniform coercivity constant for the associated Hermitian form.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-- Real part of a complex Jacobi quadratic form in its upper-triangular coordinates. -/
theorem re_complex_jacobi_quadForm
    (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (v : Fin n → ℂ) :
    (star v ⬝ᵥ
      (U.conjTranspose * Matrix.diagonal (fun i => (d i : ℂ)) * U).mulVec v).re =
      ∑ i, d i * ‖U.mulVec v i‖ ^ 2 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [← star_mulVec_dotProduct]
  exact re_quadForm_diagonal d (U.mulVec v)

/-- Bounded complex Jacobi factors with diagonal floor `δ` have a common coercivity constant.
The returned `q` depends only on dimension and the upper-factor entry bound. -/
theorem exists_complexJacobi_coercivity (n : ℕ) (u : ℝ) :
    ∃ q : ℝ, 0 < q ∧
      ∀ (δ : ℝ) (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ),
        0 ≤ δ → U ∈ complexUnipotentBall n u → (∀ i, δ ≤ d i) →
        ∀ v : Fin n → ℂ,
          q * δ * ∑ i, ‖v i‖ ^ 2 ≤
            (star v ⬝ᵥ
              (U.conjTranspose * Matrix.diagonal (fun i => (d i : ℂ)) * U).mulVec v).re := by
  classical
  obtain ⟨C₀, hC₀⟩ := exists_complex_unipotent_inv_bound n u
  set C : ℝ := max C₀ 1 with hC
  have hCbound : ∀ U ∈ complexUnipotentBall n u,
      ∀ i j, ‖U⁻¹ i j‖ ≤ C :=
    fun U hU i j => le_trans (hC₀ U hU i j) (le_max_left _ _)
  set M : ℝ := (n : ℝ) ^ 2 * C ^ 2 + 1 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨1 / M, by positivity, ?_⟩
  intro δ U d hδ hU hd v
  set w : Fin n → ℂ := U.mulVec v with hw
  have hdet : U.det = 1 := complex_det_eq_one_of_unipotent hU.1 hU.2.1
  have hvw : ∀ i, v i = ∑ j, U⁻¹ i j * w j := by
    intro i
    have hinv : (U⁻¹).mulVec (U.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one), Matrix.one_mulVec]
    have hi := congrFun hinv i
    rw [hw]
    exact hi.symm
  have hinvb : ∀ i j, ‖U⁻¹ i j‖ ≤ C := hCbound U hU
  have hterm : ∀ i j : Fin n,
      ‖U⁻¹ i j * w j‖ ^ 2 ≤ C ^ 2 * ‖w j‖ ^ 2 := by
    intro i j
    rw [norm_mul, mul_pow]
    have hs : ‖U⁻¹ i j‖ ^ 2 ≤ C ^ 2 := by
      nlinarith [hinvb i j, norm_nonneg (U⁻¹ i j)]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg ‖w j‖)
  have hrow : ∀ i : Fin n,
      ‖v i‖ ^ 2 ≤ (n : ℝ) * C ^ 2 * ∑ j, ‖w j‖ ^ 2 := by
    intro i
    calc
      ‖v i‖ ^ 2 = ‖∑ j, U⁻¹ i j * w j‖ ^ 2 := by rw [hvw i]
      _ ≤ (n : ℝ) * ∑ j, ‖U⁻¹ i j * w j‖ ^ 2 := by
        simpa using norm_sum_sq_le_card_mul (fun j : Fin n => U⁻¹ i j * w j)
      _ ≤ (n : ℝ) * ∑ j, C ^ 2 * ‖w j‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hterm i j)
          (Nat.cast_nonneg n)
      _ = (n : ℝ) * C ^ 2 * ∑ j, ‖w j‖ ^ 2 := by
        rw [← Finset.mul_sum]
        ring
  have htotal : ∑ i, ‖v i‖ ^ 2 ≤
      (n : ℝ) ^ 2 * C ^ 2 * ∑ j, ‖w j‖ ^ 2 := by
    calc
      ∑ i, ‖v i‖ ^ 2 ≤
          ∑ _i : Fin n, (n : ℝ) * C ^ 2 * ∑ j, ‖w j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = (n : ℝ) * ((n : ℝ) * C ^ 2 * ∑ j, ‖w j‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (n : ℝ) ^ 2 * C ^ 2 * ∑ j, ‖w j‖ ^ 2 := by ring
  have hW0 : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hbase : (1 / M) * ∑ i, ‖v i‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hM0]
    rw [hM]
    nlinarith
  have hweighted : δ * ∑ j, ‖w j‖ ^ 2 ≤ ∑ j, d j * ‖w j‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hd j) (sq_nonneg ‖w j‖)
  rw [re_complex_jacobi_quadForm, ← hw]
  calc
    1 / M * δ * ∑ i, ‖v i‖ ^ 2 =
        δ * ((1 / M) * ∑ i, ‖v i‖ ^ 2) := by ring
    _ ≤ δ * ∑ j, ‖w j‖ ^ 2 := mul_le_mul_of_nonneg_left hbase hδ
    _ ≤ ∑ j, d j * ‖w j‖ ^ 2 := hweighted

end GaloisForLFunctions.HTGeometry
