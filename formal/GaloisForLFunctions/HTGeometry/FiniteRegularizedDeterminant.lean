/-
# The regularized determinant of a finite complex matrix and its Carleman bound

For a square complex matrix `M` the **regularized determinant**

  `det₂(1 + zM) = det(1 + zM) · exp(−z · tr M)`

is an entire function of `z`.  Its whole point is the growth bound

  `‖det₂(1 + zM)‖ ≤ exp(‖z‖²‖M‖²_HS / 2)`,

which involves only the Hilbert–Schmidt norm of `M` and not its trace norm, so it survives the
passage to an infinite Hilbert–Schmidt operator.

The proof is Schur triangulation followed by two elementary facts: the scalar inequality
`‖(1 + w)e^{−w}‖ ≤ exp(‖w‖²/2)`, which is `log u ≤ u − 1` for `u = ‖1 + w‖²`, and Schur's
inequality `∑ᵢ|λᵢ|² ≤ ‖M‖²_HS`, which is the diagonal part of the unitarily invariant
Hilbert–Schmidt norm of the triangular form.

Main results:
* `matHSNormSq` — the Hilbert–Schmidt norm squared of a matrix, and its unitary invariance.
* `norm_one_add_mul_exp_neg_le` — `‖(1 + w)e^{−w}‖ ≤ exp(‖w‖²/2)`.
* `finiteDet2` — `det(1 + zM)·exp(−z·tr M)`, entire in `z`.
* `norm_finiteDet2_le` — the Carleman bound.
* `trace_pow_eq_sum_diag`, `det_one_add_smul_eq_prod` — the eigenvalue formulas behind it.
-/
import GaloisForLFunctions.HTGeometry.SchurTriangulation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace GaloisForLFunctions.HTGeometry

open Matrix Finset

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## The Hilbert–Schmidt norm of a matrix -/

/-- The squared Hilbert–Schmidt norm `∑ᵢⱼ ‖Mᵢⱼ‖²` of a square matrix. -/
noncomputable def matHSNormSq (M : Matrix m m ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℕ)

omit [DecidableEq m] in
theorem matHSNormSq_nonneg (M : Matrix m m ℂ) : 0 ≤ matHSNormSq M := by
  unfold matHSNormSq; positivity

omit [DecidableEq m] in
/-- The Hilbert–Schmidt norm squared is the trace of `Mᴴ M`. -/
theorem matHSNormSq_eq_trace (M : Matrix m m ℂ) :
    ((matHSNormSq M : ℝ) : ℂ) = (Mᴴ * M).trace := by
  simp only [matHSNormSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, Complex.ofReal_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- **Unitary invariance of the Hilbert–Schmidt norm.** -/
theorem matHSNormSq_conj {M U : Matrix m m ℂ} (hU2 : U * Uᴴ = 1) :
    matHSNormSq (Uᴴ * M * U) = matHSNormSq M := by
  have hC : ((matHSNormSq (Uᴴ * M * U) : ℝ) : ℂ) = ((matHSNormSq M : ℝ) : ℂ) := by
    rw [matHSNormSq_eq_trace, matHSNormSq_eq_trace]
    have hadj : (Uᴴ * M * U)ᴴ * (Uᴴ * M * U) = Uᴴ * (Mᴴ * M) * U := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc Uᴴ * (Mᴴ * U) * (Uᴴ * M * U) = Uᴴ * Mᴴ * (U * Uᴴ) * M * U := by noncomm_ring
        _ = Uᴴ * (Mᴴ * M) * U := by rw [hU2]; noncomm_ring
    rw [hadj]
    calc (Uᴴ * (Mᴴ * M) * U).trace = (U * (Uᴴ * (Mᴴ * M))).trace :=
          Matrix.trace_mul_comm (Uᴴ * (Mᴴ * M)) U
      _ = (Mᴴ * M).trace := by rw [← Matrix.mul_assoc, hU2, Matrix.one_mul]
  exact_mod_cast hC

omit [DecidableEq m] in
/-- The diagonal energy is at most the total Hilbert–Schmidt energy. -/
theorem sum_diag_normSq_le (M : Matrix m m ℂ) :
    ∑ i, ‖M i i‖ ^ (2 : ℕ) ≤ matHSNormSq M := by
  refine Finset.sum_le_sum fun i _ => ?_
  refine Finset.single_le_sum (f := fun j => ‖M i j‖ ^ (2 : ℕ)) (fun j _ => by positivity)
    (Finset.mem_univ i)

/-! ## Diagonal of a power of a triangular matrix -/

omit [DecidableEq m] in
theorem diag_mul_of_blockTriangular [LinearOrder m] {A B : Matrix m m ℂ}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : m) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA (show id k < id i from h), zero_mul]
    · rw [hB (show id i < id k from h), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem diag_pow_of_blockTriangular [LinearOrder m] {T : Matrix m m ℂ}
    (hT : T.BlockTriangular id) (k : ℕ) (i : m) : (T ^ k) i i = (T i i) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, diag_mul_of_blockTriangular (hT.pow k) hT i, ih, pow_succ]

/-! ## Schur consequences -/

variable {M U T : Matrix m m ℂ}

theorem eq_conj_of_schur (hU2 : U * Uᴴ = 1) (hMT : Uᴴ * M * U = T) :
    M = U * T * Uᴴ := by
  rw [← hMT]
  calc M = (U * Uᴴ) * M * (U * Uᴴ) := by rw [hU2]; noncomm_ring
    _ = U * (Uᴴ * M * U) * Uᴴ := by noncomm_ring

theorem det_unitary_mul_det_conjTranspose (hU2 : U * Uᴴ = 1) : U.det * Uᴴ.det = 1 := by
  rw [← Matrix.det_mul, hU2, Matrix.det_one]

/-- `det(1 + zM) = ∏ᵢ (1 + z·Tᵢᵢ)` for a Schur triangulation `T` of `M`. -/
theorem det_one_add_smul_eq_prod [LinearOrder m] (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T) (z : ℂ) :
    (1 + z • M).det = ∏ i, (1 + z * T i i) := by
  have hM := eq_conj_of_schur hU2 hMT
  have hconj : (1 : Matrix m m ℂ) + z • M = U * (1 + z • T) * Uᴴ := by
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU2, Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj, Matrix.det_mul, Matrix.det_mul]
  have htri : ((1 : Matrix m m ℂ) + z • T).BlockTriangular id :=
    blockTriangular_one.add (fun i j hij => by simp [hT hij])
  rw [Matrix.det_of_upperTriangular htri]
  have : ∀ i, ((1 : Matrix m m ℂ) + z • T) i i = 1 + z * T i i := by
    intro i; simp
  simp only [this]
  rw [mul_comm (U.det), mul_assoc, det_unitary_mul_det_conjTranspose hU2, mul_one]

/-- `tr M = ∑ᵢ Tᵢᵢ` for a Schur triangulation `T` of `M`. -/
theorem trace_eq_sum_diag (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hMT : Uᴴ * M * U = T) :
    M.trace = ∑ i, T i i := by
  have hM := eq_conj_of_schur hU2 hMT
  rw [hM]
  calc (U * T * Uᴴ).trace = (Uᴴ * (U * T)).trace := Matrix.trace_mul_comm (U * T) Uᴴ
    _ = T.trace := by rw [← Matrix.mul_assoc, hU1, Matrix.one_mul]
    _ = ∑ i, T i i := rfl

/-- `tr(Mᵐ) = ∑ᵢ Tᵢᵢᵐ` for a Schur triangulation `T` of `M`. -/
theorem trace_pow_eq_sum_diag [LinearOrder m] (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T) (k : ℕ) :
    (M ^ k).trace = ∑ i, (T i i) ^ k := by
  have hM := eq_conj_of_schur hU2 hMT
  have hpow : M ^ k = U * T ^ k * Uᴴ := by
    induction k with
    | zero => simp [hU2]
    | succ k ih =>
      rw [pow_succ, ih, hM, pow_succ]
      calc U * T ^ k * Uᴴ * (U * T * Uᴴ) = U * T ^ k * (Uᴴ * U) * T * Uᴴ := by noncomm_ring
        _ = U * (T ^ k * T) * Uᴴ := by rw [hU1]; noncomm_ring
  rw [hpow]
  calc (U * T ^ k * Uᴴ).trace = (Uᴴ * (U * T ^ k)).trace := Matrix.trace_mul_comm (U * T ^ k) Uᴴ
    _ = (T ^ k).trace := by rw [← Matrix.mul_assoc, hU1, Matrix.one_mul]
    _ = ∑ i, (T i i) ^ k := by
        simp only [Matrix.trace, Matrix.diag_apply]
        exact Finset.sum_congr rfl fun i _ => diag_pow_of_blockTriangular hT k i

/-- **Schur's inequality.**  The eigenvalue energy of a matrix is at most its Hilbert–Schmidt
energy. -/
theorem sum_diag_normSq_le_matHSNormSq (hU2 : U * Uᴴ = 1)
    (hMT : Uᴴ * M * U = T) : ∑ i, ‖T i i‖ ^ (2 : ℕ) ≤ matHSNormSq M := by
  calc ∑ i, ‖T i i‖ ^ (2 : ℕ) ≤ matHSNormSq T := sum_diag_normSq_le T
    _ = matHSNormSq M := by rw [← hMT]; exact matHSNormSq_conj hU2

/-! ## The scalar Carleman inequality -/

/-- `‖(1 + w)e^{−w}‖ ≤ exp(‖w‖²/2)`, the scalar factor of the regularized determinant.
It is `log u ≤ u − 1` applied to `u = ‖1 + w‖² = 1 + 2 Re w + ‖w‖²`. -/
theorem norm_one_add_mul_exp_neg_le (w : ℂ) :
    ‖(1 + w) * Complex.exp (-w)‖ ≤ Real.exp (‖w‖ ^ (2 : ℕ) / 2) := by
  have hnorm : ‖(1 : ℂ) + w‖ ^ (2 : ℕ) = 1 + 2 * w.re + ‖w‖ ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  rcases eq_or_lt_of_le (norm_nonneg ((1 : ℂ) + w)) with h | h
  · rw [norm_mul, ← h]
    simpa using Real.exp_nonneg _
  · rw [norm_mul, Complex.norm_exp]
    have hlog : Real.log (‖(1 : ℂ) + w‖) ≤ w.re + ‖w‖ ^ (2 : ℕ) / 2 := by
      have h2 : Real.log (‖(1 : ℂ) + w‖ ^ (2 : ℕ)) ≤ ‖(1 : ℂ) + w‖ ^ (2 : ℕ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_pow] at h2
      rw [hnorm] at h2
      push_cast at h2
      linarith
    have hle : ‖(1 : ℂ) + w‖ ≤ Real.exp (w.re + ‖w‖ ^ (2 : ℕ) / 2) := by
      rw [← Real.exp_log h]
      exact Real.exp_le_exp.mpr hlog
    calc ‖(1 : ℂ) + w‖ * Real.exp (-w).re
        ≤ Real.exp (w.re + ‖w‖ ^ (2 : ℕ) / 2) * Real.exp (-w).re :=
          mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
      _ = Real.exp (‖w‖ ^ (2 : ℕ) / 2) := by
          rw [← Real.exp_add]; simp

/-! ## The finite regularized determinant -/

/-- The **regularized determinant** `det₂(1 + zM) = det(1 + zM)·exp(−z·tr M)` of a finite
matrix. -/
noncomputable def finiteDet2 (M : Matrix m m ℂ) (z : ℂ) : ℂ :=
  (1 + z • M).det * Complex.exp (-(z * M.trace))

/-- The regularized determinant is entire in `z`: the determinant is a polynomial. -/
theorem differentiable_finiteDet2 (M : Matrix m m ℂ) :
    Differentiable ℂ (finiteDet2 M) := by
  have hentry : ∀ (z : ℂ) (a b : m), ((1 : Matrix m m ℂ) + z • M) a b
      = (if a = b then (1 : ℂ) else 0) + z * M a b := by
    intro z a b; simp [Matrix.one_apply]
  have hdet : Differentiable ℂ (fun z : ℂ => ((1 : Matrix m m ℂ) + z • M).det) := by
    have hrw : (fun z : ℂ => ((1 : Matrix m m ℂ) + z • M).det)
        = fun z : ℂ => ∑ σ : Equiv.Perm m, (Equiv.Perm.sign σ : ℂ) *
            ∏ i, ((if σ i = i then (1 : ℂ) else 0) + z * M (σ i) i) := by
      funext z
      rw [Matrix.det_apply']
      exact Finset.sum_congr rfl fun σ _ => by
        refine congrArg _ (Finset.prod_congr rfl fun i _ => hentry z (σ i) i)
    rw [hrw]
    fun_prop
  exact hdet.mul ((Complex.differentiable_exp).comp (by fun_prop))

/-- The regularized determinant in Schur coordinates: a product of scalar factors. -/
theorem finiteDet2_eq_prod [LinearOrder m] (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T) (z : ℂ) :
    finiteDet2 M z = ∏ i, ((1 + z * T i i) * Complex.exp (-(z * T i i))) := by
  unfold finiteDet2
  rw [det_one_add_smul_eq_prod hU2 hT hMT z, trace_eq_sum_diag hU1 hU2 hMT,
    Finset.prod_mul_distrib]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum, neg_eq_neg_one_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The Carleman bound for a matrix indexed by `Fin n`, where the Schur decomposition is available
directly. -/
theorem norm_finiteDet2_fin_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    ‖finiteDet2 M z‖ ≤ Real.exp (‖z‖ ^ (2 : ℕ) * matHSNormSq M / 2) := by
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ := exists_schur_triangulation n M
  rw [finiteDet2_eq_prod hU1 hU2 hT hMT z, norm_prod]
  calc ∏ i, ‖(1 + z * T i i) * Complex.exp (-(z * T i i))‖
      ≤ ∏ i, Real.exp (‖z * T i i‖ ^ (2 : ℕ) / 2) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _)
          (fun i _ => norm_one_add_mul_exp_neg_le (z * T i i))
    _ = Real.exp (∑ i, ‖z * T i i‖ ^ (2 : ℕ) / 2) := by rw [Real.exp_sum]
    _ = Real.exp (‖z‖ ^ (2 : ℕ) * (∑ i, ‖T i i‖ ^ (2 : ℕ)) / 2) := by
        congr 1
        rw [Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by rw [norm_mul, mul_pow]
    _ ≤ Real.exp (‖z‖ ^ (2 : ℕ) * matHSNormSq M / 2) := by
        refine Real.exp_le_exp.mpr ?_
        have := sum_diag_normSq_le_matHSNormSq hU2 hMT
        have hz : (0 : ℝ) ≤ ‖z‖ ^ (2 : ℕ) := by positivity
        nlinarith


/-! ## Reindexing -/

omit [DecidableEq m] in
theorem matHSNormSq_submatrix {p : Type*} [Fintype p] [DecidableEq p] (e : p ≃ m)
    (M : Matrix m m ℂ) : matHSNormSq (M.submatrix e e) = matHSNormSq M := by
  unfold matHSNormSq
  simp only [Matrix.submatrix_apply]
  calc ∑ i : p, ∑ j : p, ‖M (e i) (e j)‖ ^ (2 : ℕ)
      = ∑ i : p, ∑ j : m, ‖M (e i) j‖ ^ (2 : ℕ) :=
        Finset.sum_congr rfl fun i _ => Equiv.sum_comp e (fun j => ‖M (e i) j‖ ^ (2 : ℕ))
    _ = ∑ i : m, ∑ j : m, ‖M i j‖ ^ (2 : ℕ) := Equiv.sum_comp e (fun i => ∑ j, ‖M i j‖ ^ (2 : ℕ))

omit [DecidableEq m] in
theorem trace_submatrix_equiv {p : Type*} [Fintype p] [DecidableEq p] (e : p ≃ m)
    (M : Matrix m m ℂ) : (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e fun i => M i i

theorem finiteDet2_submatrix {p : Type*} [Fintype p] [DecidableEq p] (e : p ≃ m)
    (M : Matrix m m ℂ) (z : ℂ) : finiteDet2 (M.submatrix e e) z = finiteDet2 M z := by
  have hone : ((1 : Matrix m m ℂ) + z • M).submatrix e e = 1 + z • M.submatrix e e := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff]
  unfold finiteDet2
  rw [← hone, Matrix.det_submatrix_equiv_self e, trace_submatrix_equiv e]

/-- **The Carleman bound.**  `‖det₂(1 + zM)‖ ≤ exp(‖z‖²‖M‖²_HS/2)` — the growth is controlled by
the Hilbert–Schmidt norm alone, for a matrix indexed by any finite type. -/
theorem norm_finiteDet2_le (M : Matrix m m ℂ) (z : ℂ) :
    ‖finiteDet2 M z‖ ≤ Real.exp (‖z‖ ^ (2 : ℕ) * matHSNormSq M / 2) := by
  set e : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm with he
  rw [← finiteDet2_submatrix e M z, ← matHSNormSq_submatrix e M]
  exact norm_finiteDet2_fin_le (M.submatrix e e) z

end GaloisForLFunctions.HTGeometry
