/-
# The determinant exponent of a finite matrix

For a finite complex matrix `M` whose eigenvalues are smaller than `1/|z|`,

  `exp(−∑_{k≥2} zᵏ/k · tr(Mᵏ)) = det(1 − zM)·exp(z·tr M)`,

which is the finite-dimensional case of the defining series of the regularized determinant.  The
proof is Schur triangulation followed by the scalar identity `∑_{k≥2} wᵏ/k = −log(1 − w) − w`.

Applied to the block matrix of a truncated Hilbert–Schmidt kernel this identifies the corpus object
`HilbertSchmidt.fredholmDet` of the truncation with the finite regularized determinant of the
block, on the disc where the exponent series converges.

Main results:
* `tsum_pow_div_add_two` — `∑_{k} w^{k+2}/(k+2) = −log(1 − w) − w` for `‖w‖ < 1`.
* `exp_neg_traceSeries_eq_finiteDet2_neg` — the determinant exponent of a matrix.
* `fredholmDet_truncKernel_eq` — the corpus determinant of a truncation is the finite one.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockMatrix
import GaloisForLFunctions.HTGeometry.FredholmDeterminant
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace GaloisForLFunctions.HTGeometry

open Matrix Finset

/-- The tail of the logarithm series: `∑_{k} w^{k+2}/(k+2) = −log(1 − w) − w`. -/
theorem tsum_pow_div_add_two {w : ℂ} (hw : ‖w‖ < 1) :
    ∑' k : ℕ, w ^ (k + 2) / ((k + 2 : ℕ) : ℂ) = -Complex.log (1 - w) - w := by
  have hsum := Complex.hasSum_taylorSeries_neg_log hw
  have hsummable : Summable fun n : ℕ => w ^ n / (n : ℂ) := hsum.summable
  have hsplit := hsummable.sum_add_tsum_nat_add 2
  rw [hsum.tsum_eq] at hsplit
  have hrange : ∑ i ∈ Finset.range 2, w ^ i / (i : ℂ) = w := by
    simp [Finset.sum_range_succ]
  rw [hrange] at hsplit
  have hcast : (fun k : ℕ => w ^ (k + 2) / ((k + 2 : ℕ) : ℂ))
      = fun k : ℕ => w ^ (k + 2) / (((k + 2 : ℕ) : ℕ) : ℂ) := rfl
  rw [hcast]
  linear_combination hsplit

/-- The scalar factor: `exp(−(−log(1 − w) − w)) = (1 − w)·exp(w)`. -/
theorem exp_neg_tsum_pow_div_add_two {w : ℂ} (hw : ‖w‖ < 1) :
    Complex.exp (-∑' k : ℕ, w ^ (k + 2) / ((k + 2 : ℕ) : ℂ)) = (1 - w) * Complex.exp w := by
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h] at hw
    simp at hw
  rw [tsum_pow_div_add_two hw]
  have : -(-Complex.log (1 - w) - w) = Complex.log (1 - w) + w := by ring
  rw [this, Complex.exp_add, Complex.exp_log hne]

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Each eigenvalue of a matrix is bounded by its Hilbert–Schmidt norm. -/
theorem norm_diag_le_of_schur {M U T : Matrix m m ℂ} (hU2 : U * Uᴴ = 1)
    (hMT : Uᴴ * M * U = T) (i : m) : ‖T i i‖ ≤ Real.sqrt (matHSNormSq M) := by
  have h1 : ‖T i i‖ ^ 2 ≤ matHSNormSq M := by
    refine le_trans ?_ (sum_diag_normSq_le_matHSNormSq hU2 hMT)
    exact Finset.single_le_sum (f := fun j => ‖T j j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  calc ‖T i i‖ = Real.sqrt (‖T i i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (matHSNormSq M) := Real.sqrt_le_sqrt h1

/-- The trace-power series of a matrix, on the disc where it converges. -/
theorem exp_neg_traceSeries_eq_finiteDet2_neg_fin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {z : ℂ}
    (hz : ‖z‖ * Real.sqrt (matHSNormSq M) < 1) :
    Complex.exp (-∑' k : ℕ, z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (M ^ (k + 2)).trace)
      = finiteDet2 (-M) z := by
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ := exists_schur_triangulation n M
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hsmall : ∀ i, ‖z * T i i‖ < 1 := by
    intro i
    rw [norm_mul]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (norm_diag_le_of_schur hU2 hMT i) hzn) hz
  have hsummable : ∀ i : Fin n, Summable fun k : ℕ => (z * T i i) ^ (k + 2) / ((k + 2 : ℕ) : ℂ) := by
    intro i
    have h := (Complex.hasSum_taylorSeries_neg_log (hsmall i)).summable
    exact (h.comp_injective (add_left_injective 2)).congr fun k => rfl
  -- the trace series is the finite sum of the scalar series
  have htrace : ∀ k : ℕ, (M ^ (k + 2)).trace = ∑ i, (T i i) ^ (k + 2) :=
    fun k => trace_pow_eq_sum_diag hU1 hU2 hT hMT (k + 2)
  have hswap : (∑' k : ℕ, z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (M ^ (k + 2)).trace)
      = ∑ i, ∑' k : ℕ, (z * T i i) ^ (k + 2) / ((k + 2 : ℕ) : ℂ) := by
    rw [← Summable.tsum_finsetSum fun i _ => hsummable i]
    refine tsum_congr fun k => ?_
    rw [htrace k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]; ring
  rw [hswap, ← Finset.sum_neg_distrib, Complex.exp_sum]
  rw [finiteDet2_eq_prod hU1 hU2 (hT.neg) (by rw [← hMT]; noncomm_ring) z]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [exp_neg_tsum_pow_div_add_two (hsmall i)]
  simp only [Matrix.neg_apply, mul_neg, neg_neg, ← sub_eq_add_neg]

/-! ## Reindexing the trace series -/

theorem trace_pow_submatrix {p : Type*} [Fintype p] [DecidableEq p] (e : p ≃ m)
    (M : Matrix m m ℂ) (k : ℕ) : ((M.submatrix e e) ^ k).trace = (M ^ k).trace := by
  have hpow : ∀ k : ℕ, (M.submatrix e e) ^ k = (M ^ k).submatrix e e := by
    intro k
    induction k with
    | zero => ext i j; simp [Matrix.one_apply, e.injective.eq_iff]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ, Matrix.submatrix_mul_equiv]
  rw [hpow, trace_submatrix_equiv]

/-- The trace-power series identity for a matrix indexed by any finite type. -/
theorem exp_neg_traceSeries_eq_finiteDet2_neg (M : Matrix m m ℂ) {z : ℂ}
    (hz : ‖z‖ * Real.sqrt (matHSNormSq M) < 1) :
    Complex.exp (-∑' k : ℕ, z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (M ^ (k + 2)).trace)
      = finiteDet2 (-M) z := by
  set e : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm with he
  have hHS : matHSNormSq (M.submatrix e e) = matHSNormSq M := matHSNormSq_submatrix e M
  have hneg : (-M).submatrix e e = -(M.submatrix e e) := by ext i j; simp
  have hdet : finiteDet2 (-M) z = finiteDet2 (-(M.submatrix e e)) z := by
    rw [← hneg, finiteDet2_submatrix e (-M) z]
  rw [hdet]
  have := exp_neg_traceSeries_eq_finiteDet2_neg_fin (M.submatrix e e) (z := z) (by rw [hHS]; exact hz)
  rw [← this]
  congr 2
  exact tsum_congr fun k => by rw [trace_pow_submatrix e M (k + 2)]

/-! ## The corpus determinant of a truncated kernel -/

open HilbertSchmidt in
/-- **The regularized determinant of a finite truncation is the finite regularized determinant of
its block.**  Both are defined on the disc where the exponent series converges. -/
theorem fredholmDet_truncKernel_eq {ι : Type*} [DecidableEq ι] (K : ι × ι → ℂ) (s : Finset ι)
    {z : ℂ} (hz : ‖z‖ * hsNorm (truncKernel K s) < 1) :
    fredholmDet (truncKernel K s) z = finiteDet2 (-(blockMatrix K s)) z := by
  have hnorm : hsNorm (truncKernel K s) = Real.sqrt (matHSNormSq (blockMatrix K s)) := by
    rw [hsNorm, matHSNormSq_blockMatrix, hsNormSq_truncKernel_eq_sum]
  rw [fredholmDet, fredholmExp]
  rw [← exp_neg_traceSeries_eq_finiteDet2_neg (blockMatrix K s) (by rw [← hnorm]; exact hz)]
  congr 2
  exact tsum_congr fun k => by rw [hsTrace_hsPow_truncKernel K s (k + 1)]

end GaloisForLFunctions.HTGeometry
