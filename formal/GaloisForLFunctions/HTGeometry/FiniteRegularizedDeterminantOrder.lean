/-
# The regularized determinant at every order

The order-`g+1` regularized determinant of a finite matrix subtracts the first `g` power traces
from the logarithm of the determinant:

  `det_{g+1}(1 + zM) = det(1 + zM)·exp(∑_{k=1}^{g} (−z)^k tr(M^k)/k)`,

and its logarithm is exactly the tail of the trace series,

  `exp(−∑_{k ≥ g+1} z^k tr(M^k)/k) = det_{g+1}(1 − zM)`   on the disc of convergence.

The proof is Schur triangulation followed by the scalar identity
`∑_{k ≥ g+1} w^k/k = −log(1−w) − ∑_{k=1}^{g} w^k/k`, exactly as at order two.  The order-two case
already in the corpus is the `g = 1` instance.

This is the card's displayed formula `log det(I−zA) = −∑_{j≥1} Tr(A^j)z^j/j` with the first `g`
terms removed: the coordinates a regularized determinant of order `g+1` forgets are precisely
`Tr(A), …, Tr(A^g)`.

Main results:
* `tsum_pow_div_add_succ`, `exp_neg_tsum_pow_div_add_succ` — the scalar tail identity.
* `finiteDetOrder`, `finiteDetOrder_eq_prod` — the determinant and its Schur product form.
* `exp_neg_traceSeries_eq_finiteDetOrder_neg` — **the trace-series identity at every order**.
-/
import GaloisForLFunctions.HTGeometry.FiniteDeterminantLogSeries

open Matrix Finset

namespace GaloisForLFunctions.HTGeometry

/-- The tail of the logarithm series past order `g`. -/
theorem tsum_pow_div_add_succ {w : ℂ} (hw : ‖w‖ < 1) (g : ℕ) :
    ∑' k : ℕ, w ^ (k + (g + 1)) / ((k + (g + 1) : ℕ) : ℂ)
      = -Complex.log (1 - w) - ∑ j ∈ Finset.range g, w ^ (j + 1) / ((j + 1 : ℕ) : ℂ) := by
  have hsum := Complex.hasSum_taylorSeries_neg_log hw
  have hsummable : Summable fun n : ℕ => w ^ n / (n : ℂ) := hsum.summable
  have hsplit := hsummable.sum_add_tsum_nat_add (g + 1)
  rw [hsum.tsum_eq] at hsplit
  have hrange : ∑ i ∈ Finset.range (g + 1), w ^ i / (i : ℂ)
      = ∑ j ∈ Finset.range g, w ^ (j + 1) / ((j + 1 : ℕ) : ℂ) := by
    rw [Finset.sum_range_succ']
    simp
  rw [hrange] at hsplit
  have hcast : (fun k : ℕ => w ^ (k + (g + 1)) / ((k + (g + 1) : ℕ) : ℂ))
      = fun k : ℕ => w ^ (k + (g + 1)) / (((k + (g + 1) : ℕ) : ℕ) : ℂ) := rfl
  rw [hcast]
  linear_combination hsplit

/-- The scalar factor at order `g+1`. -/
theorem exp_neg_tsum_pow_div_add_succ {w : ℂ} (hw : ‖w‖ < 1) (g : ℕ) :
    Complex.exp (-∑' k : ℕ, w ^ (k + (g + 1)) / ((k + (g + 1) : ℕ) : ℂ))
      = (1 - w) * Complex.exp (∑ j ∈ Finset.range g, w ^ (j + 1) / ((j + 1 : ℕ) : ℂ)) := by
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h] at hw
    simp at hw
  rw [tsum_pow_div_add_succ hw g]
  have hrw : -(-Complex.log (1 - w) - ∑ j ∈ Finset.range g, w ^ (j + 1) / ((j + 1 : ℕ) : ℂ))
      = Complex.log (1 - w) + ∑ j ∈ Finset.range g, w ^ (j + 1) / ((j + 1 : ℕ) : ℂ) := by ring
  rw [hrw, Complex.exp_add, Complex.exp_log hne]

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The **order-`g+1` regularized determinant** `det_{g+1}(1 + zM)` of a finite matrix. -/
noncomputable def finiteDetOrder (g : ℕ) (M : Matrix m m ℂ) (z : ℂ) : ℂ :=
  (1 + z • M).det *
    Complex.exp (∑ j ∈ Finset.range g,
      (-z) ^ (j + 1) * (M ^ (j + 1)).trace / ((j + 1 : ℕ) : ℂ))

/-- At order two the definition is the corpus regularized determinant. -/
theorem finiteDetOrder_one (M : Matrix m m ℂ) (z : ℂ) :
    finiteDetOrder 1 M z = finiteDet2 M z := by
  rw [finiteDetOrder, finiteDet2]
  congr 1
  rw [Finset.sum_range_one]
  simp

/-- The order-`g+1` determinant in Schur coordinates: a product of scalar primary factors. -/
theorem finiteDetOrder_eq_prod [LinearOrder m] {U T M : Matrix m m ℂ} (g : ℕ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T)
    (z : ℂ) :
    finiteDetOrder g M z
      = ∏ i, ((1 + z * T i i) *
          Complex.exp (∑ j ∈ Finset.range g,
            (-(z * T i i)) ^ (j + 1) / ((j + 1 : ℕ) : ℂ))) := by
  rw [finiteDetOrder, det_one_add_smul_eq_prod hU2 hT hMT z, Finset.prod_mul_distrib]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [trace_pow_eq_sum_diag hU1 hU2 hT hMT (j + 1), Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← mul_pow, neg_mul]

/-- **The trace-series identity at every order**, for a matrix indexed by `Fin n`. -/
theorem exp_neg_traceSeries_eq_finiteDetOrder_neg_fin {n : ℕ} (g : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ) {z : ℂ}
    (hz : ‖z‖ * Real.sqrt (matHSNormSq M) < 1) :
    Complex.exp (-∑' k : ℕ, z ^ (k + (g + 1)) / ((k + (g + 1) : ℕ) : ℂ) *
        (M ^ (k + (g + 1))).trace)
      = finiteDetOrder g (-M) z := by
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ := exists_schur_triangulation n M
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hsmall : ∀ i, ‖z * T i i‖ < 1 := by
    intro i
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_diag_le_of_schur hU2 hMT i) hzn) hz
  have hsummable : ∀ i : Fin n,
      Summable fun k : ℕ => (z * T i i) ^ (k + (g + 1)) / ((k + (g + 1) : ℕ) : ℂ) := by
    intro i
    have h := (Complex.hasSum_taylorSeries_neg_log (hsmall i)).summable
    exact (h.comp_injective (add_left_injective (g + 1))).congr fun k => rfl
  have htrace : ∀ k : ℕ, (M ^ (k + (g + 1))).trace = ∑ i, (T i i) ^ (k + (g + 1)) :=
    fun k => trace_pow_eq_sum_diag hU1 hU2 hT hMT (k + (g + 1))
  have hswap : (∑' k : ℕ, z ^ (k + (g + 1)) / ((k + (g + 1) : ℕ) : ℂ) *
        (M ^ (k + (g + 1))).trace)
      = ∑ i, ∑' k : ℕ, (z * T i i) ^ (k + (g + 1)) / ((k + (g + 1) : ℕ) : ℂ) := by
    rw [← Summable.tsum_finsetSum fun i _ => hsummable i]
    refine tsum_congr fun k => ?_
    rw [htrace k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]; ring
  rw [hswap, ← Finset.sum_neg_distrib, Complex.exp_sum]
  rw [finiteDetOrder_eq_prod g hU1 hU2 (hT.neg) (by rw [← hMT]; noncomm_ring) z]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [exp_neg_tsum_pow_div_add_succ (hsmall i) g]
  simp only [Matrix.neg_apply, mul_neg, neg_neg, ← sub_eq_add_neg]

theorem finiteDetOrder_submatrix {p : Type*} [Fintype p] [DecidableEq p] (e : p ≃ m)
    (g : ℕ) (M : Matrix m m ℂ) (z : ℂ) :
    finiteDetOrder g (M.submatrix e e) z = finiteDetOrder g M z := by
  rw [finiteDetOrder, finiteDetOrder]
  have hone : (1 : Matrix p p ℂ) + z • M.submatrix e e
      = ((1 : Matrix m m ℂ) + z • M).submatrix e e := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.submatrix_apply, Matrix.one_apply_eq]
    · simp [Matrix.submatrix_apply, Matrix.one_apply_ne hij,
        Matrix.one_apply_ne (fun h => hij (e.injective h))]
  rw [hone, Matrix.det_submatrix_equiv_self]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [trace_pow_submatrix e M (j + 1)]

/-- **The trace-series identity at every order**, for a matrix indexed by any finite type. -/
theorem exp_neg_traceSeries_eq_finiteDetOrder_neg (g : ℕ) (M : Matrix m m ℂ) {z : ℂ}
    (hz : ‖z‖ * Real.sqrt (matHSNormSq M) < 1) :
    Complex.exp (-∑' k : ℕ, z ^ (k + (g + 1)) / ((k + (g + 1) : ℕ) : ℂ) *
        (M ^ (k + (g + 1))).trace)
      = finiteDetOrder g (-M) z := by
  set e : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm with he
  have hHS : matHSNormSq (M.submatrix e e) = matHSNormSq M := matHSNormSq_submatrix e M
  have hneg : (-M).submatrix e e = -(M.submatrix e e) := by ext i j; simp
  have hdet : finiteDetOrder g (-M) z = finiteDetOrder g (-(M.submatrix e e)) z := by
    rw [← hneg, finiteDetOrder_submatrix]
  rw [hdet]
  have := exp_neg_traceSeries_eq_finiteDetOrder_neg_fin g (M.submatrix e e)
    (by rw [hHS]; exact hz)
  rw [← this]
  congr 2
  exact tsum_congr fun k => by rw [trace_pow_submatrix e M (k + (g + 1))]

end GaloisForLFunctions.HTGeometry
