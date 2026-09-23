/-
# Block eigenvectors as `ℓ²` eigenvectors

An eigenvector of the finite block `blockMatrix K s`, extended by zero, is an eigenvector of the
operator on `ℓ²(ι)` represented by the truncated kernel, with the same eigenvalue and the same
norm.  Together with the operator-norm convergence of the truncations this is what lets a limit of
block eigenvalues be recognised as an eigenvalue of the kernel itself.

Main results:
* `liftBlock`, `liftBlockLp` — the zero extension of a block vector, as an `ℓ²` vector.
* `toOperator_truncKernel_liftBlockLp` — it is an eigenvector of the truncated operator.
* `norm_toOperator_sub_le` — the operator norm is bounded by the Hilbert–Schmidt distance.
* `tendsto_norm_toOperator_truncKernel_sub` — the truncated operators converge in operator norm.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockMatrix
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

namespace HilbertSchmidt

open Filter Matrix

variable {ι : Type*} [DecidableEq ι]

/-- The zero extension of a vector on a finite block. -/
def liftBlock {s : Finset ι} (v : ↥s → ℂ) : ι → ℂ :=
  fun i => if h : i ∈ s then v ⟨i, h⟩ else 0

theorem liftBlock_apply_of_mem {s : Finset ι} (v : ↥s → ℂ) {i : ι} (hi : i ∈ s) :
    liftBlock v i = v ⟨i, hi⟩ := by simp [liftBlock, hi]

theorem liftBlock_apply_of_notMem {s : Finset ι} (v : ↥s → ℂ) {i : ι} (hi : i ∉ s) :
    liftBlock v i = 0 := by simp [liftBlock, hi]

theorem summable_sq_liftBlock {s : Finset ι} (v : ↥s → ℂ) :
    Summable fun i => ‖liftBlock v i‖ ^ (2 : ℕ) := by
  refine summable_of_ne_finset_zero (s := s) fun i hi => ?_
  rw [liftBlock_apply_of_notMem v hi]
  simp

/-- The zero extension as an `ℓ²` vector. -/
noncomputable def liftBlockLp {s : Finset ι} (v : ↥s → ℂ) : lp (fun _ : ι => ℂ) 2 :=
  ⟨liftBlock v, memℓp_of_sq (summable_sq_liftBlock v)⟩

@[simp] theorem liftBlockLp_apply {s : Finset ι} (v : ↥s → ℂ) (i : ι) :
    liftBlockLp v i = liftBlock v i := rfl

theorem liftBlockLp_ne_zero {s : Finset ι} {v : ↥s → ℂ} (hv : v ≠ 0) : liftBlockLp v ≠ 0 := by
  intro h
  refine hv (funext fun i => ?_)
  have := congrFun (congrArg (fun w : lp (fun _ : ι => ℂ) 2 => (w : ι → ℂ)) h) (i : ι)
  simpa [liftBlockLp_apply, liftBlock_apply_of_mem v i.2] using this

/-- **A block eigenvector is an `ℓ²` eigenvector of the truncated operator.** -/
theorem toOperator_truncKernel_liftBlockLp {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι)
    {v : ↥s → ℂ} {lam : ℂ} (hv : (blockMatrix K s) *ᵥ v = lam • v) :
    toOperator (isHS_truncKernel hK s) (liftBlockLp v) = lam • liftBlockLp v := by
  apply lp.ext
  funext i
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  show (∑' j, truncKernel K s (i, j) * liftBlock v j) = lam * liftBlock v i
  by_cases hi : i ∈ s
  · have hzero : ∀ j ∉ s, truncKernel K s (i, j) * liftBlock v j = 0 := by
      intro j hj
      rw [liftBlock_apply_of_notMem v hj, mul_zero]
    rw [tsum_eq_sum (s := s) hzero,
      ← Finset.sum_coe_sort s fun j : ι => truncKernel K s (i, j) * liftBlock v j]
    have hentry : ∀ j : ↥s, truncKernel K s (i, (j : ι)) * liftBlock v (j : ι)
        = (blockMatrix K s) ⟨i, hi⟩ j * v j := by
      intro j
      rw [liftBlock_apply_of_mem v j.2]
      simp [truncKernel, blockMatrix, hi, j.2]
    rw [Finset.sum_congr rfl fun j _ => hentry j]
    have := congrFun hv ⟨i, hi⟩
    rw [Matrix.mulVec, dotProduct] at this
    rw [this, Pi.smul_apply, smul_eq_mul, liftBlock_apply_of_mem v hi]
  · have hzero : ∀ j : ι, truncKernel K s (i, j) * liftBlock v j = 0 := by
      intro j
      have : truncKernel K s (i, j) = 0 := by simp [truncKernel, hi]
      rw [this, zero_mul]
    rw [liftBlock_apply_of_notMem v hi, mul_zero]
    simp [hzero]

/-! ## Operator-norm convergence of the truncations -/

omit [DecidableEq ι] in
theorem toOperator_sub {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) :
    toOperator hA - toOperator hB = toOperator (isHS_sub hA hB) := by
  ext f i
  show (toOperator hA f i - toOperator hB f i) = ∑' j, (A - B) (i, j) * f j
  rw [toOperator_apply, toOperator_apply,
    ← (summable_row_mul hA f i).tsum_sub (summable_row_mul hB f i)]
  exact tsum_congr fun j => by simp [sub_mul]

omit [DecidableEq ι] in
theorem norm_toOperator_sub_le {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) :
    ‖toOperator hA - toOperator hB‖ ≤ hsNorm (A - B) := by
  rw [toOperator_sub hA hB]
  exact norm_toOperator_le _

/-- **The truncated operators converge in operator norm.** -/
theorem tendsto_norm_toOperator_truncKernel_sub {K : ι × ι → ℂ} (hK : IsHS K) :
    Tendsto (fun s : Finset ι => ‖toOperator (isHS_truncKernel hK s) - toOperator hK‖)
      atTop (nhds 0) := by
  have hneg : ∀ s : Finset ι, hsNorm (truncKernel K s - K) = hsNorm (K - truncKernel K s) := by
    intro s
    have hE : truncKernel K s - K = -(K - truncKernel K s) := by funext p; simp
    rw [hE, hsNorm_neg]
  have hmaj : Tendsto (fun s : Finset ι => hsNorm (truncKernel K s - K)) atTop (nhds 0) :=
    (tendsto_hsNorm_sub_truncKernel hK).congr fun s => (hneg s).symm
  exact squeeze_zero (fun s => norm_nonneg _)
    (fun s => norm_toOperator_sub_le (isHS_truncKernel hK s) hK) hmaj

end HilbertSchmidt
