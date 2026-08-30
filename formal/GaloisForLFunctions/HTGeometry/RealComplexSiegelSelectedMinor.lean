import GaloisForLFunctions.HTGeometry.ComplexSiegelGramDomination
import GaloisForLFunctions.HTGeometry.ComplexSiegelWeightedGram
import GaloisForLFunctions.HTGeometry.SiegelMinorLowerBound
import GaloisForLFunctions.HTGeometry.SiegelOrbitMoves

/-!
# Selected-minor bounds for real and Hermitian Siegel forms

One prescribed maximal minor is retained through Cauchy--Binet.  Ordered Jacobi-weight comparison
and real/Hermitian determinant domination then give matching local bounds.  Keeping the selection
fixed is essential over number fields: the same nonzero algebraic-integer minor must be used at all
archimedean places before applying the product formula.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

variable {n k : ℕ}

/-- One prescribed minor term is bounded by a real weighted Gram determinant. -/
theorem realWeightedMinor_le_factorial_mul_det
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (C : Matrix (Fin n) (Fin k) ℝ) (f : Fin k → Fin n) :
    (∏ b, d (f b)) * ((C.submatrix f id).det) ^ 2 ≤
      (Nat.factorial k : ℝ) *
        (Matrix.transpose C * Matrix.diagonal d * C).det := by
  classical
  have hCB := factorial_mul_det_weightedGram d C
  have hnonneg : ∀ g : Fin k → Fin n,
      0 ≤ (∏ b, d (g b)) * ((C.submatrix g id).det) ^ 2 := by
    intro g
    exact mul_nonneg (Finset.prod_nonneg fun b _ => hd _) (sq_nonneg _)
  rw [hCB]
  exact Finset.single_le_sum (fun g _ => hnonneg g) (Finset.mem_univ f)

/-- A complex Jacobi form is positive definite. -/
theorem ComplexJacobiData.form_posDef (J : ComplexJacobiData n) : J.form.PosDef := by
  have hD : (Matrix.diagonal (fun i => (J.d i : ℂ))).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    exact Complex.lt_def.2 ⟨J.pos i, by simp⟩
  have hU : IsUnit J.U := by
    rw [Matrix.isUnit_iff_isUnit_det, J.det_eq_one]
    exact isUnit_one
  exact hD.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hU)

/-- Diagonal complex quadratic form with real weights. -/
theorem re_star_dotProduct_diagonal_mulVec (d : Fin n → ℝ) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (Matrix.diagonal (fun i => (d i : ℂ))).mulVec v).re =
      ∑ i, d i * ‖v i‖ ^ 2 := by
  exact re_quadForm_diagonal d v

/-- Selected-minor lower bound for one Hermitian Siegel form and one injective frame. -/
theorem complex_siegel_selectedMinor_bound
    {t u c : ℝ} (ht : 1 ≤ t) (hc : 0 < c)
    (J : ComplexJacobiData n) (hS : J.IsSiegel t u)
    (hquasi : ∀ v : Fin n → ℂ,
      c * (∑ i, J.d i * ‖v i‖ ^ 2) ≤ (star v ⬝ᵥ J.form.mulVec v).re)
    (hk : k ≤ n) (C : Matrix (Fin n) (Fin k) ℂ)
    (hC : Function.Injective C.mulVec)
    (f : Fin k → Fin n) (hf : Function.Injective f) :
    c ^ k * (∏ j : Fin k, J.d (Fin.castLE hk j)) *
        ‖(C.submatrix f id).det‖ ^ 2 ≤
      (Nat.factorial k : ℝ) * (t ^ n) ^ k *
        (Matrix.conjTranspose C * J.form * C).det.re := by
  classical
  set D₀ : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => (J.d i : ℂ)) with hD₀
  have hDpos : D₀.PosDef := by
    rw [hD₀, Matrix.posDef_diagonal_iff]
    intro i
    exact Complex.lt_def.2 ⟨J.pos i, by simp⟩
  have hGDpos := complex_posDef_congr hDpos hC
  obtain ⟨JG₀, hJG₀⟩ := exists_complexJacobiData hGDpos
  have hGApos := complex_posDef_congr J.form_posDef hC
  obtain ⟨JG, hJG⟩ := exists_complexJacobiData hGApos
  have hcmp : ∀ v : Fin n → ℂ,
      c * (star v ⬝ᵥ D₀.mulVec v).re ≤ (star v ⬝ᵥ J.form.mulVec v).re := by
    intro v
    rw [hD₀, re_star_dotProduct_diagonal_mulVec]
    exact hquasi v
  have hXY : c ^ k * (Matrix.conjTranspose C * D₀ * C).det.re ≤
      (Matrix.conjTranspose C * J.form * C).det.re :=
    complex_det_congr_ge hc hcmp hJG hJG₀
  have hK : 1 ≤ t ^ n := one_le_pow₀ ht
  have hmono : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) →
      J.d i ≤ t ^ n * J.d j :=
    fun i j hij => J.d_le_pow_n ht hS hij
  have hPW : (∏ j : Fin k, J.d (Fin.castLE hk j)) ≤
      (t ^ n) ^ k * ∏ b, J.d (f b) :=
    prod_castLE_le_prod_of_injective hk J.pos hmono hf
  have hWM : (∏ b, J.d (f b)) * ‖(C.submatrix f id).det‖ ^ 2 ≤
      (Nat.factorial k : ℝ) * (Matrix.conjTranspose C * D₀ * C).det.re := by
    rw [hD₀]
    exact complexWeightedMinor_le_factorial_mul_det_re J.d (fun i => (J.pos i).le) C f
  have hc0 : 0 ≤ c ^ k := pow_nonneg hc.le k
  have hK0 : 0 ≤ (t ^ n) ^ k :=
    pow_nonneg (le_trans zero_le_one hK) k
  have hm0 : 0 ≤ ‖(C.submatrix f id).det‖ ^ 2 := sq_nonneg _
  have hfac0 : 0 ≤ (Nat.factorial k : ℝ) := by positivity
  calc
    c ^ k * (∏ j : Fin k, J.d (Fin.castLE hk j)) *
        ‖(C.submatrix f id).det‖ ^ 2 ≤
      c ^ k * ((t ^ n) ^ k * ∏ b, J.d (f b)) *
        ‖(C.submatrix f id).det‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hPW hc0) hm0
    _ = c ^ k * (t ^ n) ^ k *
        ((∏ b, J.d (f b)) * ‖(C.submatrix f id).det‖ ^ 2) := by ring
    _ ≤ c ^ k * (t ^ n) ^ k *
        ((Nat.factorial k : ℝ) * (Matrix.conjTranspose C * D₀ * C).det.re) := by
          exact mul_le_mul_of_nonneg_left hWM (mul_nonneg hc0 hK0)
    _ = (Nat.factorial k : ℝ) * (t ^ n) ^ k *
        (c ^ k * (Matrix.conjTranspose C * D₀ * C).det.re) := by ring
    _ ≤ (Nat.factorial k : ℝ) * (t ^ n) ^ k *
        (Matrix.conjTranspose C * J.form * C).det.re := by
          exact mul_le_mul_of_nonneg_left hXY (mul_nonneg hfac0 hK0)

/-- Selected-minor lower bound for one real Siegel form and one injective frame. -/
theorem real_siegel_selectedMinor_bound
    {t u c : ℝ} (ht : 1 ≤ t) (hc : 0 < c)
    (J : JacobiData n) (hS : J.IsSiegel t u)
    (hquasi : ∀ v : Fin n → ℝ,
      c * (∑ i, J.d i * (v i) ^ 2) ≤ v ⬝ᵥ J.form.mulVec v)
    (hk : k ≤ n) (C : Matrix (Fin n) (Fin k) ℝ)
    (hC : Function.Injective C.mulVec)
    (f : Fin k → Fin n) (hf : Function.Injective f) :
    c ^ k * (∏ j : Fin k, J.d (Fin.castLE hk j)) *
        ((C.submatrix f id).det) ^ 2 ≤
      (Nat.factorial k : ℝ) * (t ^ n) ^ k *
        (Matrix.transpose C * J.form * C).det := by
  classical
  set D₀ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal J.d with hD₀
  have hDpos : D₀.PosDef := by
    rw [hD₀, Matrix.posDef_diagonal_iff]
    exact J.pos
  have hker : ∀ x : Fin k → ℝ, C.mulVec x = 0 → x = 0 := by
    intro x hx
    exact hC (by simpa using hx)
  have hGDpos := posDef_congr hDpos hker
  obtain ⟨JG₀, hJG₀⟩ := exists_jacobiData hGDpos
  have hGApos := posDef_congr J.posDef hker
  obtain ⟨JG, hJG⟩ := exists_jacobiData hGApos
  have hcmp : ∀ v : Fin n → ℝ,
      c * (v ⬝ᵥ D₀.mulVec v) ≤ v ⬝ᵥ J.form.mulVec v := by
    intro v
    rw [hD₀, dotProduct_diagonal_mulVec]
    exact hquasi v
  have hXY : c ^ k * (Matrix.transpose C * D₀ * C).det ≤
      (Matrix.transpose C * J.form * C).det :=
    det_congr_ge hc hcmp hJG hJG₀
  have hK : 1 ≤ t ^ n := one_le_pow₀ ht
  have hmono : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) →
      J.d i ≤ t ^ n * J.d j :=
    fun i j hij => J.d_le_pow_n ht hS hij
  have hPW : (∏ j : Fin k, J.d (Fin.castLE hk j)) ≤
      (t ^ n) ^ k * ∏ b, J.d (f b) :=
    prod_castLE_le_prod_of_injective hk J.pos hmono hf
  have hWM : (∏ b, J.d (f b)) * ((C.submatrix f id).det) ^ 2 ≤
      (Nat.factorial k : ℝ) * (Matrix.transpose C * D₀ * C).det := by
    rw [hD₀]
    exact realWeightedMinor_le_factorial_mul_det J.d (fun i => (J.pos i).le) C f
  have hc0 : 0 ≤ c ^ k := pow_nonneg hc.le k
  have hK0 : 0 ≤ (t ^ n) ^ k :=
    pow_nonneg (le_trans zero_le_one hK) k
  have hm0 : 0 ≤ ((C.submatrix f id).det) ^ 2 := sq_nonneg _
  have hfac0 : 0 ≤ (Nat.factorial k : ℝ) := by positivity
  calc
    c ^ k * (∏ j : Fin k, J.d (Fin.castLE hk j)) *
        ((C.submatrix f id).det) ^ 2 ≤
      c ^ k * ((t ^ n) ^ k * ∏ b, J.d (f b)) *
        ((C.submatrix f id).det) ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hPW hc0) hm0
    _ = c ^ k * (t ^ n) ^ k *
        ((∏ b, J.d (f b)) * ((C.submatrix f id).det) ^ 2) := by ring
    _ ≤ c ^ k * (t ^ n) ^ k *
        ((Nat.factorial k : ℝ) * (Matrix.transpose C * D₀ * C).det) := by
          exact mul_le_mul_of_nonneg_left hWM (mul_nonneg hc0 hK0)
    _ = (Nat.factorial k : ℝ) * (t ^ n) ^ k *
        (c ^ k * (Matrix.transpose C * D₀ * C).det) := by ring
    _ ≤ (Nat.factorial k : ℝ) * (t ^ n) ^ k *
        (Matrix.transpose C * J.form * C).det := by
          exact mul_le_mul_of_nonneg_left hXY (mul_nonneg hfac0 hK0)

end GaloisForLFunctions.HTGeometry
