import Mathlib
import GaloisForLFunctions.HTGeometry.DiagonalCommutantGeneration

/-!
# The Gaussian Toeplitz operator generates `B(ℓ²(ℕ))` over the diagonal algebra

For `x > 0` let `H x` be the operator on `ℓ²(ℕ)` with matrix entries
`⟪e m, H x (e n)⟫ = exp (-π x (m - n) ^ 2)` in the standard basis.  It is assembled here as a
norm-convergent series in the powers of the backward shift and its adjoint, the coefficients being
the Gaussian band weights `exp (-π x j ^ 2)`, whose summability comes from `j ≤ j ^ 2`.

Every matrix entry of `H x` is nonzero, so `H x` together with the algebra `ℓ^∞(ℕ)` of diagonal
multiplication operators has trivial commutant, and the generated von Neumann algebra is all of
`B(ℓ²(ℕ))`.
-/

namespace GaloisForLFunctions.GaussianToeplitz

open scoped InnerProductSpace ENNReal

/-- The complex sequence space `ℓ²(ℕ)`. -/
abbrev L2N : Type := lp (fun _ : ℕ => ℂ) 2

/-- The standard Hilbert basis of `ℓ²(ℕ)`. -/
noncomputable def stdBasis : HilbertBasis ℕ ℂ L2N := default

theorem stdBasis_apply (i : ℕ) : stdBasis i = lp.single 2 i (1 : ℂ) :=
  (HilbertBasis.repr_symm_single (stdBasis) i).symm

theorem stdBasis_coe (i j : ℕ) : ((stdBasis i : L2N) : ℕ → ℂ) j = if j = i then 1 else 0 := by
  rw [stdBasis_apply, lp.single_apply]
  simp [Pi.single_apply, eq_comm]

theorem memℓp_shift (v : L2N) : Memℓp (fun n : ℕ => (v : ℕ → ℂ) (n + 1)) 2 := by
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hv : Summable (fun n : ℕ => ‖(v : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal) :=
    (memℓp_gen_iff hp).mp (lp.memℓp v)
  exact memℓp_gen ((summable_nat_add_iff 1).mpr hv)

/-- The backward shift on `ℓ²(ℕ)`, as a linear map. -/
noncomputable def backShiftLin : L2N →ₗ[ℂ] L2N where
  toFun v := ⟨fun n => (v : ℕ → ℂ) (n + 1), memℓp_shift v⟩
  map_add' v w := by
    refine lp.ext ?_
    funext n
    simp
  map_smul' c v := by
    refine lp.ext ?_
    funext n
    simp

@[simp] theorem backShiftLin_coe (v : L2N) (n : ℕ) :
    ((backShiftLin v : L2N) : ℕ → ℂ) n = (v : ℕ → ℂ) (n + 1) := rfl

theorem norm_backShiftLin_le (v : L2N) : ‖backShiftLin v‖ ≤ 1 * ‖v‖ := by
  rw [one_mul]
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsum : Summable (fun n : ℕ => ‖(v : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal) :=
    (memℓp_gen_iff hp).mp (lp.memℓp v)
  have h1 : ‖backShiftLin v‖ ^ (2 : ℝ≥0∞).toReal
      = ∑' n : ℕ, ‖(v : ℕ → ℂ) (n + 1)‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum hp]
    rfl
  have h2 : ‖v‖ ^ (2 : ℝ≥0∞).toReal = ∑' n : ℕ, ‖(v : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal :=
    lp.norm_rpow_eq_tsum hp v
  have hle : ‖backShiftLin v‖ ^ (2 : ℝ≥0∞).toReal ≤ ‖v‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [h1, h2, ← hsum.sum_add_tsum_nat_add 1]
    have hnn : 0 ≤ ∑ i ∈ Finset.range 1, ‖(v : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal := by positivity
    linarith
  have h2R : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2R, Real.rpow_two, Real.rpow_two] at hle
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- The backward shift on `ℓ²(ℕ)`. -/
noncomputable def backShift : L2N →L[ℂ] L2N :=
  backShiftLin.mkContinuous 1 norm_backShiftLin_le

@[simp] theorem backShift_coe (v : L2N) (n : ℕ) :
    ((backShift v : L2N) : ℕ → ℂ) n = (v : ℕ → ℂ) (n + 1) := rfl

theorem backShift_pow_coe : ∀ (j : ℕ) (v : L2N) (n : ℕ),
    (((backShift ^ j) v : L2N) : ℕ → ℂ) n = (v : ℕ → ℂ) (n + j) := by
  intro j
  induction j with
  | zero => intro v n; simp
  | succ j ih =>
      intro v n
      rw [pow_succ]
      simp only [mul_apply_eq_comp]
      rw [ih (backShift v) n, backShift_coe]
      congr 1

theorem norm_backShift_le : ‖backShift‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _



theorem inner_stdBasis_left (m : ℕ) (w : L2N) : ⟪stdBasis m, w⟫_ℂ = (w : ℕ → ℂ) m := by
  rw [stdBasis_apply, lp.inner_single_left]
  simp

theorem norm_pow_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : E →L[ℂ] E} (hT : ‖T‖ ≤ 1) (j : ℕ) : ‖T ^ j‖ ≤ 1 := by
  induction j with
  | zero =>
      have h := ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E)
      simpa [ContinuousLinearMap.one_def] using h
  | succ j ih =>
      rw [pow_succ]
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      calc ‖T ^ j‖ * ‖T‖ ≤ 1 * 1 := by
              exact mul_le_mul ih hT (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

/-- The forward shift, adjoint to `backShift`. -/
noncomputable def fwdShift : L2N →L[ℂ] L2N := ContinuousLinearMap.adjoint backShift

theorem norm_fwdShift_le : ‖fwdShift‖ ≤ 1 := by
  rw [fwdShift, ContinuousLinearMap.adjoint.norm_map]
  exact norm_backShift_le

theorem fwdShift_pow_eq (j : ℕ) :
    fwdShift ^ j = ContinuousLinearMap.adjoint (backShift ^ j) := by
  rw [fwdShift, ← ContinuousLinearMap.star_eq_adjoint, ← star_pow,
    ContinuousLinearMap.star_eq_adjoint]

theorem inner_stdBasis_backShift_pow (j m n : ℕ) :
    ⟪stdBasis m, (backShift ^ j) (stdBasis n)⟫_ℂ = if n = m + j then 1 else 0 := by
  rw [inner_stdBasis_left, backShift_pow_coe, stdBasis_coe]
  by_cases h : n = m + j
  · simp [h]
  · rw [if_neg (fun hh => h hh.symm), if_neg h]

theorem inner_stdBasis_fwdShift_pow (j m n : ℕ) :
    ⟪stdBasis m, (fwdShift ^ j) (stdBasis n)⟫_ℂ = if m = n + j then 1 else 0 := by
  rw [fwdShift_pow_eq, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
    inner_stdBasis_backShift_pow]
  split <;> simp

/-- The Gaussian band coefficients `exp (-π x j ^ 2)`. -/
noncomputable def gaussKernelToeplitz (x : ℝ) (j : ℕ) : ℂ :=
  ((Real.exp (-(Real.pi * x * (j : ℝ) ^ 2)) : ℝ) : ℂ)

theorem gaussKernelToeplitz_ne_zero (x : ℝ) (j : ℕ) : gaussKernelToeplitz x j ≠ 0 := by
  simp [gaussKernelToeplitz]

theorem norm_gaussKernelToeplitz (x : ℝ) (j : ℕ) :
    ‖gaussKernelToeplitz x j‖ = Real.exp (-(Real.pi * x * (j : ℝ) ^ 2)) := by
  rw [gaussKernelToeplitz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem summable_norm_gaussKernelToeplitz {x : ℝ} (hx : 0 < x) :
    Summable (fun j : ℕ => ‖gaussKernelToeplitz x j‖) := by
  have hr : Real.exp (-(Real.pi * x)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < Real.pi * x := mul_pos Real.pi_pos hx
    linarith
  have hgeo : Summable (fun j : ℕ => Real.exp (-(Real.pi * x)) ^ j) :=
    summable_geometric_of_lt_one (le_of_lt (Real.exp_pos _)) hr
  refine hgeo.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
  rw [norm_gaussKernelToeplitz, ← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hj : (j : ℝ) ≤ (j : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos j with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
      nlinarith
  have hpx : 0 < Real.pi * x := mul_pos Real.pi_pos hx
  nlinarith



theorem summable_gaussFwd {x : ℝ} (hx : 0 < x) :
    Summable (fun j : ℕ => gaussKernelToeplitz x j • (fwdShift ^ j)) := by
  refine Summable.of_norm_bounded (summable_norm_gaussKernelToeplitz hx) (fun j => ?_)
  rw [norm_smul]
  calc ‖gaussKernelToeplitz x j‖ * ‖fwdShift ^ j‖ ≤ ‖gaussKernelToeplitz x j‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_pow_le_one norm_fwdShift_le j) (norm_nonneg _)
    _ = ‖gaussKernelToeplitz x j‖ := mul_one _

theorem summable_gaussBack {x : ℝ} (hx : 0 < x) :
    Summable (fun j : ℕ => gaussKernelToeplitz x (j + 1) • (backShift ^ (j + 1))) := by
  refine Summable.of_norm_bounded
    ((summable_nat_add_iff 1).mpr (summable_norm_gaussKernelToeplitz hx)) (fun j => ?_)
  rw [norm_smul]
  calc ‖gaussKernelToeplitz x (j + 1)‖ * ‖backShift ^ (j + 1)‖ ≤ ‖gaussKernelToeplitz x (j + 1)‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_pow_le_one norm_backShift_le (j + 1)) (norm_nonneg _)
    _ = ‖gaussKernelToeplitz x (j + 1)‖ := mul_one _

/-- The Gaussian Toeplitz operator with matrix entries `exp (-π x (m - n) ^ 2)`. -/
noncomputable def gaussToeplitz (x : ℝ) : L2N →L[ℂ] L2N :=
  (∑' j : ℕ, gaussKernelToeplitz x j • (fwdShift ^ j))
    + (∑' j : ℕ, gaussKernelToeplitz x (j + 1) • (backShift ^ (j + 1)))

theorem tsum_inner_apply {T : ℕ → L2N →L[ℂ] L2N} (hT : Summable T) (m n : ℕ) :
    ⟪stdBasis m, (∑' j, T j) (stdBasis n)⟫_ℂ
      = ∑' j, ⟪stdBasis m, (T j) (stdBasis n)⟫_ℂ := by
  have h1 : HasSum (fun j => (T j) (stdBasis n)) ((∑' j, T j) (stdBasis n)) :=
    hT.hasSum.mapL (ContinuousLinearMap.apply ℂ L2N (stdBasis n))
  exact (h1.mapL (innerSL ℂ (stdBasis m))).tsum_eq.symm

theorem tsum_entry_fwd (x : ℝ) (m n : ℕ) :
    ∑' j : ℕ, ⟪stdBasis m, (gaussKernelToeplitz x j • (fwdShift ^ j)) (stdBasis n)⟫_ℂ
      = if n ≤ m then gaussKernelToeplitz x (m - n) else 0 := by
  have hterm : ∀ j : ℕ, ⟪stdBasis m, (gaussKernelToeplitz x j • (fwdShift ^ j)) (stdBasis n)⟫_ℂ
      = gaussKernelToeplitz x j * (if m = n + j then 1 else 0) := by
    intro j
    rw [smul_apply, inner_smul_right, inner_stdBasis_fwdShift_pow]
  simp only [hterm]
  by_cases h : n ≤ m
  · rw [if_pos h]
    refine (tsum_eq_single (m - n) ?_).trans ?_
    · intro j hj
      have : m ≠ n + j := by omega
      rw [if_neg this, mul_zero]
    · rw [if_pos (by omega), mul_one]
  · rw [if_neg h]
    have hz : ∀ j : ℕ, gaussKernelToeplitz x j * (if m = n + j then 1 else 0) = 0 := by
      intro j
      rw [if_neg (by omega : ¬ (m = n + j)), mul_zero]
    simp [hz]



theorem tsum_entry_back (x : ℝ) (m n : ℕ) :
    ∑' j : ℕ, ⟪stdBasis m, (gaussKernelToeplitz x (j + 1) • (backShift ^ (j + 1))) (stdBasis n)⟫_ℂ
      = if m < n then gaussKernelToeplitz x (n - m) else 0 := by
  have hterm : ∀ j : ℕ,
      ⟪stdBasis m, (gaussKernelToeplitz x (j + 1) • (backShift ^ (j + 1))) (stdBasis n)⟫_ℂ
        = gaussKernelToeplitz x (j + 1) * (if n = m + (j + 1) then 1 else 0) := by
    intro j
    rw [smul_apply, inner_smul_right, inner_stdBasis_backShift_pow]
  simp only [hterm]
  by_cases h : m < n
  · rw [if_pos h]
    refine (tsum_eq_single (n - m - 1) ?_).trans ?_
    · intro j hj
      have : n ≠ m + (j + 1) := by omega
      rw [if_neg this, mul_zero]
    · rw [if_pos (by omega), mul_one]
      congr 1
      omega
  · rw [if_neg h]
    have hz : ∀ j : ℕ, gaussKernelToeplitz x (j + 1) * (if n = m + (j + 1) then 1 else 0) = 0 := by
      intro j
      rw [if_neg (by omega : ¬ (n = m + (j + 1))), mul_zero]
    simp [hz]

theorem inner_stdBasis_gaussToeplitz {x : ℝ} (hx : 0 < x) (m n : ℕ) :
    ⟪stdBasis m, gaussToeplitz x (stdBasis n)⟫_ℂ
      = ((Real.exp (-(Real.pi * x * ((m : ℝ) - (n : ℝ)) ^ 2)) : ℝ) : ℂ) := by
  rw [gaussToeplitz, add_apply, inner_add_right,
    tsum_inner_apply (summable_gaussFwd hx), tsum_inner_apply (summable_gaussBack hx),
    tsum_entry_fwd, tsum_entry_back]
  by_cases h : n ≤ m
  · rw [if_pos h, if_neg (by omega : ¬ (m < n)), add_zero, gaussKernelToeplitz]
    have hc : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
      have := Nat.cast_sub (R := ℝ) h
      exact this
    rw [hc]
  · rw [if_neg h, if_pos (by omega : m < n), zero_add, gaussKernelToeplitz]
    have hc : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
      have := Nat.cast_sub (R := ℝ) (le_of_lt (by omega : m < n))
      exact this
    rw [hc]
    congr 2
    ring

theorem inner_stdBasis_gaussToeplitz_ne_zero {x : ℝ} (hx : 0 < x) (m n : ℕ) :
    ⟪stdBasis m, gaussToeplitz x (stdBasis n)⟫_ℂ ≠ 0 := by
  rw [inner_stdBasis_gaussToeplitz hx]
  simp



theorem memℓp_diagMul {c : ℕ → ℂ} {M : ℝ} (hc : ∀ n, ‖c n‖ ≤ M) (v : L2N) :
    Memℓp (fun n => c n * (v : ℕ → ℂ) n) 2 := by
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hq : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hv : Summable (fun n : ℕ => ‖(v : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal) :=
    (memℓp_gen_iff hp).mp (lp.memℓp v)
  refine memℓp_gen (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hv.mul_left (M ^ 2)))
  rw [hq] at hv ⊢
  rw [Real.rpow_two, Real.rpow_two, norm_mul, mul_pow]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hc n)
  have : ‖c n‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (c n), hc n]
  nlinarith [sq_nonneg ‖(v : ℕ → ℂ) n‖, norm_nonneg ((v : ℕ → ℂ) n)]

/-- Multiplication by a bounded sequence, as a linear map on `ℓ²(ℕ)`. -/
noncomputable def diagMulLin (c : ℕ → ℂ) (M : ℝ) (hc : ∀ n, ‖c n‖ ≤ M) : L2N →ₗ[ℂ] L2N where
  toFun v := ⟨fun n => c n * (v : ℕ → ℂ) n, memℓp_diagMul hc v⟩
  map_add' v w := by
    refine lp.ext ?_
    funext n
    simp [mul_add]
  map_smul' a v := by
    refine lp.ext ?_
    funext n
    simp [mul_left_comm]

@[simp] theorem diagMulLin_coe (c : ℕ → ℂ) (M : ℝ) (hc : ∀ n, ‖c n‖ ≤ M) (v : L2N) (n : ℕ) :
    ((diagMulLin c M hc v : L2N) : ℕ → ℂ) n = c n * (v : ℕ → ℂ) n := rfl

theorem norm_diagMulLin_le (c : ℕ → ℂ) (M : ℝ) (hc : ∀ n, ‖c n‖ ≤ M) (v : L2N) :
    ‖diagMulLin c M hc v‖ ≤ M * ‖v‖ := by
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hq : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hc 0)
  have hv : Summable (fun n : ℕ => ‖(v : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal) :=
    (memℓp_gen_iff hp).mp (lp.memℓp v)
  have h1 : ‖diagMulLin c M hc v‖ ^ (2 : ℝ≥0∞).toReal
      = ∑' n : ℕ, ‖c n * (v : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum hp]
    rfl
  have h2 : ‖v‖ ^ (2 : ℝ≥0∞).toReal = ∑' n : ℕ, ‖(v : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal :=
    lp.norm_rpow_eq_tsum hp v
  have hbound : ∀ n : ℕ, ‖c n * (v : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ M ^ 2 * ‖(v : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal := by
    intro n
    rw [hq, Real.rpow_two, Real.rpow_two, norm_mul, mul_pow]
    have hcn : ‖c n‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (c n), hc n]
    nlinarith [sq_nonneg ‖(v : ℕ → ℂ) n‖, norm_nonneg ((v : ℕ → ℂ) n)]
  have hsum2 : Summable (fun n : ℕ => ‖c n * (v : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal) :=
    (memℓp_gen_iff hp).mp (memℓp_diagMul hc v)
  have hle : ‖diagMulLin c M hc v‖ ^ (2 : ℝ≥0∞).toReal ≤ M ^ 2 * ‖v‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [h1, h2, ← tsum_mul_left]
    exact hsum2.tsum_le_tsum hbound (hv.mul_left (M ^ 2))
  rw [hq, Real.rpow_two, Real.rpow_two] at hle
  have hfin : ‖diagMulLin c M hc v‖ ^ 2 ≤ (M * ‖v‖) ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt hfin
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at this

/-- Multiplication by a bounded sequence, as a bounded operator on `ℓ²(ℕ)`. -/
noncomputable def diagMul (c : ℕ → ℂ) (M : ℝ) (hc : ∀ n, ‖c n‖ ≤ M) : L2N →L[ℂ] L2N :=
  (diagMulLin c M hc).mkContinuous M (norm_diagMulLin_le c M hc)

@[simp] theorem diagMul_coe (c : ℕ → ℂ) (M : ℝ) (hc : ∀ n, ‖c n‖ ≤ M) (v : L2N) (n : ℕ) :
    ((diagMul c M hc v : L2N) : ℕ → ℂ) n = c n * (v : ℕ → ℂ) n := rfl

/-- The algebra `ℓ^∞(ℕ)` acting on `ℓ²(ℕ)` by diagonal multiplication. -/
def multiplierAlgebra : Set (L2N →L[ℂ] L2N) :=
  {T | ∃ (c : ℕ → ℂ) (M : ℝ) (hc : ∀ n, ‖c n‖ ≤ M), T = diagMul c M hc}

/-- Each rank-one basis projection is multiplication by an indicator sequence. -/
theorem basisProj_mem_multiplierAlgebra (i : ℕ) :
    DiagonalCommutant.basisProj stdBasis i ∈ multiplierAlgebra := by
  refine ⟨fun n => if n = i then 1 else 0, 1, ?_, ?_⟩
  · intro n
    by_cases h : n = i <;> simp [h]
  · refine ContinuousLinearMap.ext (fun v => ?_)
    refine lp.ext ?_
    funext n
    rw [diagMul_coe, DiagonalCommutant.basisProj_apply, inner_stdBasis_left, lp.coeFn_smul]
    by_cases h : n = i <;> simp [h, stdBasis_coe]

/-- **The heat diagonal generates the full operator algebra.**
For every `x > 0` the von Neumann algebra generated by the diagonal algebra `ℓ^∞(ℕ)` together
with the Gaussian Toeplitz operator `H x` is all of `B(ℓ²(ℕ))`. -/
theorem vonNeumannGen_multiplierAlgebra_gaussToeplitz {x : ℝ} (hx : 0 < x) :
    DiagonalCommutant.vonNeumannGen (multiplierAlgebra ∪ {gaussToeplitz x})
      = (Set.univ : Set (L2N →L[ℂ] L2N)) :=
  DiagonalCommutant.vonNeumannGen_eq_univ' stdBasis
    (fun i => Or.inl (basisProj_mem_multiplierAlgebra i)) (Or.inr rfl)
    (fun m n => inner_stdBasis_gaussToeplitz_ne_zero hx m n)

/-- The same statement for the full algebra of operators diagonal in the standard basis. -/
theorem vonNeumannGen_diagonalOps_gaussToeplitz {x : ℝ} (hx : 0 < x) :
    DiagonalCommutant.vonNeumannGen (DiagonalCommutant.diagonalOps stdBasis ∪ {gaussToeplitz x})
      = (Set.univ : Set (L2N →L[ℂ] L2N)) :=
  DiagonalCommutant.vonNeumannGen_diagonalOps_eq_univ stdBasis
    (fun m n => inner_stdBasis_gaussToeplitz_ne_zero hx m n)

end GaloisForLFunctions.GaussianToeplitz
