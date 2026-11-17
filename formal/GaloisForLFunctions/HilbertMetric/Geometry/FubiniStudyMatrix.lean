import GaloisForLFunctions.HilbertMetric.Geometry.FubiniStudyTraceCondition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Matrix of the differentiated Fubini–Study metric

The affine Levi metric is a positive scalar identity minus a radial
rank-one term. The determinant lemma gives its exact density, while
quadratic evaluation identifies this matrix with the actual Levi form.
-/

noncomputable section
open Matrix
open scoped ComplexConjugate BigOperators ComplexOrder
namespace GaloisForLFunctions.HilbertMetric.FubiniStudy

/-- Rank-one matrix expression for the affine Fubini–Study metric. -/
def metricMatrix {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  (denominator z : ℂ)⁻¹ •
    (1 + replicateCol (Fin 1) (fun i => -(denominator z : ℂ)⁻¹ * z i) *
      replicateRow (Fin 1) (fun i => conj (z i)))

private theorem sum_conj_mul (n : ℕ) (z : EuclideanSpace ℂ (Fin n)) :
    ∑ i, conj (z i) * z i = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- The metric determinant is the exact radial Monge–Ampère density. -/
theorem det_metricMatrix {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    (metricMatrix z).det = ((1 / denominator z ^ (n + 1) : ℝ) : ℂ) := by
  have hdet : (1 + replicateCol (Fin 1) (fun i => -(denominator z : ℂ)⁻¹ * z i) *
      replicateRow (Fin 1) (fun i => conj (z i))).det =
      1 + (fun i => conj (z i)) ⬝ᵥ (fun i => -(denominator z : ℂ)⁻¹ * z i) :=
    Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
      (fun i => -(denominator z : ℂ)⁻¹ * z i) (fun i => conj (z i))
  rw [metricMatrix, Matrix.det_smul, hdet]
  simp only [Fintype.card_fin]
  have hs : (fun i => conj (z i)) ⬝ᵥ (fun i => -(denominator z : ℂ)⁻¹ * z i) =
      -(denominator z : ℂ)⁻¹ * ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    unfold dotProduct
    rw [← sum_conj_mul n z, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  have hd : (denominator z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (denominator_pos z).ne'
  have hu : 1 + -(denominator z : ℂ)⁻¹ * ((‖z‖ ^ 2 : ℝ) : ℂ) =
      (denominator z : ℂ)⁻¹ := by
    field_simp [hd]
    simp only [denominator, Complex.ofReal_add, Complex.ofReal_one]
    ring
  rw [hu, ← pow_succ]
  push_cast
  simp only [one_div, inv_pow]

/-- The matrix entries are the differentiated projective metric coefficients. -/
theorem metricMatrix_apply {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) (i j : Fin n) :
    metricMatrix z i j = (if i = j then 1 else 0) / (denominator z : ℂ) -
      z i * conj (z j) / (denominator z : ℂ) ^ 2 := by
  simp only [metricMatrix, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, Matrix.of_apply,
    Fin.sum_univ_one, Matrix.one_apply]
  ring

private theorem inner_eq_sum {n : ℕ} (v w : EuclideanSpace ℂ (Fin n)) :
    inner ℂ v w = ∑ i, conj (v i) * w i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change ∑ i, w i * conj (v i) = ∑ i, conj (v i) * w i
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Matrix action is a scalar identity minus the radial rank-one correction. -/
theorem metricMatrix_mulVec {n : ℕ} (z w : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (metricMatrix z *ᵥ (fun j => w j)) i =
      w i / (denominator z : ℂ) -
        z i * inner ℂ z w / (denominator z : ℂ) ^ 2 := by
  change (∑ j, metricMatrix z i j * w j) = _
  simp_rw [metricMatrix_apply, sub_mul, Finset.sum_sub_distrib]
  have hd : (∑ j, (if i = j then 1 else 0) / (denominator z : ℂ) * w j) =
      w i / (denominator z : ℂ) := by
    simp only [ite_div, zero_div, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring
  have hr : (∑ j, z i * conj (z j) / (denominator z : ℂ) ^ 2 * w j) =
      z i * inner ℂ z w / (denominator z : ℂ) ^ 2 := by
    rw [inner_eq_sum, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hd, hr]

/-- The matrix represents the Hermitian polarization of the actual Levi form. -/
theorem metricMatrix_pairing {n : ℕ} (z v w : EuclideanSpace ℂ (Fin n)) :
    (fun i => conj (v i)) ⬝ᵥ (metricMatrix z *ᵥ (fun i => w i)) = hermitian z v w := by
  unfold dotProduct
  simp_rw [metricMatrix_mulVec, mul_sub, Finset.sum_sub_distrib]
  rw [hermitian, inner_eq_sum v w, inner_eq_sum v z, Finset.sum_div,
    Finset.sum_mul, Finset.sum_div]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- The diagonal matrix pairing is exactly the second derivative Levi energy. -/
theorem metricMatrix_quadratic {n : ℕ} (z v : EuclideanSpace ℂ (Fin n)) :
    (fun i => conj (v i)) ⬝ᵥ (metricMatrix z *ᵥ (fun i => v i)) = (levi z v : ℂ) := by
  rw [metricMatrix_pairing, hermitian_self]

/-- Conjugate symmetry of the differentiated metric matrix. -/
theorem metricMatrix_isHermitian {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    (metricMatrix z).IsHermitian := by
  ext i j
  change conj (metricMatrix z j i) = metricMatrix z i j
  rw [metricMatrix_apply, metricMatrix_apply]
  by_cases h : i = j
  · subst j
    simp only [if_true, map_sub, map_div₀, map_pow, map_one, map_mul,
      Complex.conj_ofReal, Complex.conj_conj]
    ring
  · simp only [if_neg h, if_neg (Ne.symm h), map_sub, map_div₀, map_pow, map_zero,
      map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring

/-- Strict positivity of the actual Levi form makes its matrix positive definite. -/
theorem metricMatrix_posDef {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    (metricMatrix z).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨metricMatrix_isHermitian z, fun v hv => ?_⟩
  let w : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  have hw : w ≠ 0 := by
    intro h
    exact hv (congrArg WithLp.ofLp h)
  have he := metricMatrix_quadratic z w
  change star v ⬝ᵥ (metricMatrix z *ᵥ v) = (levi z w : ℂ) at he
  rw [he]
  exact_mod_cast (levi_pos_iff z w).mpr hw

#print axioms det_metricMatrix
#print axioms metricMatrix_pairing
#print axioms metricMatrix_quadratic
#print axioms metricMatrix_posDef
end GaloisForLFunctions.HilbertMetric.FubiniStudy
