import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic

/-!
# Unitary producers carry Euler factors only with modulus one

A unitary scattering matrix `S` (a quantum graph's vertex scattering matrix, a CMV/Lee–Yang
transfer, a canonical-system monodromy) produces the secular function `det(1 − S·D)`, with `D` a
diagonal matrix of phases `e^{ik log p}`.  Its trace formula is an Euler product over the diagonal
entries exactly when every principal minor of `S` is the product of its diagonal entries; already
the full minor gives `det S = ∏ S_ii`.

* `abs_diag_eq_one_of_det_eq_prod_diag`: for unitary `S`, `det S = ∏ S_ii` forces `|S_ii| = 1`,
  since `|det S| = 1` and every diagonal entry of a unitary matrix has modulus at most one.
* `offDiag_eq_zero_of_det_eq_prod_diag`: unit rows then force `S` diagonal.

So a unitary producer reproduces an Euler product only with unimodular local factors and
decoupled cycles.  The central local factors `p^{-1/2}` of `ζ` cannot be realised this way.
-/

open Matrix Finset

namespace RHTower

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rows of a unitary matrix are unit vectors: `Σ_j |S_ij|² = 1`. -/
theorem sum_normSq_row_of_mem_unitary {S : Matrix n n ℂ} (hS : S ∈ unitaryGroup n ℂ) (i : n) :
    ∑ j, Complex.normSq (S i j) = 1 := by
  have h := congrFun (congrFun (mem_unitaryGroup_iff.mp hS) i) i
  rw [mul_apply, one_apply_eq] at h
  have h' : ∑ j, (Complex.normSq (S i j) : ℂ) = 1 := by
    rw [← h]
    refine sum_congr rfl fun j _ => ?_
    rw [star_apply, Complex.star_def, Complex.mul_conj]
  exact_mod_cast h'

theorem normSq_entry_le_one_of_mem_unitary {S : Matrix n n ℂ} (hS : S ∈ unitaryGroup n ℂ)
    (i j : n) : Complex.normSq (S i j) ≤ 1 := by
  rw [← sum_normSq_row_of_mem_unitary hS i]
  exact single_le_sum (fun k _ => Complex.normSq_nonneg _) (mem_univ j)

/-- A unitary matrix whose determinant is the product of its diagonal entries has unimodular
diagonal. -/
theorem abs_diag_eq_one_of_det_eq_prod_diag {S : Matrix n n ℂ} (hS : S ∈ unitaryGroup n ℂ)
    (hdet : S.det = ∏ i, S i i) (i : n) : ‖S i i‖ = 1 := by
  have hdu : ‖S.det‖ = 1 := by
    have h := det_of_mem_unitary hS
    have h1 : star S.det * S.det = 1 := (Unitary.mem_iff.mp h).1
    have h2 : (Complex.normSq S.det : ℂ) = 1 := by
      rw [← Complex.mul_conj, mul_comm, ← Complex.star_def]; exact h1
    have h3 : Complex.normSq S.det = 1 := by exact_mod_cast h2
    rw [← Complex.sq_norm] at h3
    nlinarith [norm_nonneg S.det]
  have hprod : ∏ j, ‖S j j‖₊ = 1 := by
    have : ‖∏ j, S j j‖₊ = 1 := by
      rw [← hdet]; exact NNReal.coe_eq_one.mp (by rw [coe_nnnorm]; exact hdu)
    rwa [nnnorm_prod] at this
  have hle : ∀ j ∈ (univ : Finset n), ‖S j j‖₊ ≤ 1 := by
    intro j _
    have h := normSq_entry_le_one_of_mem_unitary hS j j
    rw [← Complex.sq_norm] at h
    have h' : ‖S j j‖ ≤ 1 := by nlinarith [norm_nonneg (S j j)]
    exact_mod_cast h'
  have := ((prod_eq_one_iff_of_le_one' hle).mp hprod) i (mem_univ i)
  rw [← coe_nnnorm, this, NNReal.coe_one]

/-- **Unitary Euler rigidity.** A unitary matrix whose determinant is the product of its diagonal
entries is diagonal. -/
theorem offDiag_eq_zero_of_det_eq_prod_diag {S : Matrix n n ℂ} (hS : S ∈ unitaryGroup n ℂ)
    (hdet : S.det = ∏ i, S i i) {i j : n} (hij : i ≠ j) : S i j = 0 := by
  have hrow := sum_normSq_row_of_mem_unitary hS i
  have hii : Complex.normSq (S i i) = 1 := by
    rw [← Complex.sq_norm, abs_diag_eq_one_of_det_eq_prod_diag hS hdet i]; norm_num
  rw [← add_sum_erase _ _ (mem_univ i), hii] at hrow
  have hzero : ∑ k ∈ univ.erase i, Complex.normSq (S i k) = 0 := by linarith
  have hj := (sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (S i k))).mp hzero j
    (mem_erase.mpr ⟨hij.symm, mem_univ j⟩)
  exact Complex.normSq_eq_zero.mp hj

end RHTower
