import Mathlib

/-!
# Operator-valued block diagonals on a Hilbert direct sum

A uniformly bounded family of operators `T i : K i →L[𝕜] K i` acts blockwise on the direct sum
`lp K 2` and defines a bounded operator `blockOperator T`.  This is the operator-valued companion of
the scalar block diagonal: the blocks are arbitrary operators, not multiplications by scalars.

* `blockOperator_memℓp`, `blockOperator`, `norm_blockOperator_le` — the construction and its norm
  bound;
* `blockOperator_injective` — blockwise injectivity is injectivity;
* `denseRange_blockOperator` — blockwise surjectivity gives dense range, because the range contains
  every `lp.single` and those sum to an arbitrary vector;
* `not_surjective_blockOperator`, `range_blockOperator_ne_top`,
  `not_isClosed_range_blockOperator` — if the blocks are not uniformly bounded below then the
  operator is not invertible, so its dense range is proper and therefore not closed.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal

section BlockOperator

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} {K : ι → Type*}
  [∀ i, NormedAddCommGroup (K i)] [∀ i, NormedSpace 𝕜 (K i)]

/-- A uniformly bounded family of block operators preserves the Hilbert direct sum. -/
theorem blockOperator_memℓp (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : lp K 2) : Memℓp (fun i => T i (x i)) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun i => ‖(x : ∀ i, K i) i‖ ^ (2 : ℝ) :=
    (lp.memℓp x).summable (by norm_num)
  refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (C ^ (2 : ℝ)))
  intro i
  have hle : ‖T i ((x : ∀ i, K i) i)‖ ≤ C * ‖(x : ∀ i, K i) i‖ :=
    le_trans ((T i).le_opNorm _) (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
  calc ‖T i ((x : ∀ i, K i) i)‖ ^ (2 : ℝ)
      ≤ (C * ‖(x : ∀ i, K i) i‖) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hle (by norm_num)
    _ = C ^ (2 : ℝ) * ‖(x : ∀ i, K i) i‖ ^ (2 : ℝ) := Real.mul_rpow hC (norm_nonneg _)

/-- The blockwise action as a linear map. -/
def blockOperatorLinear (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) :
    lp K 2 →ₗ[𝕜] lp K 2 where
  toFun x := ⟨fun i => T i (x i), blockOperator_memℓp T hC hT x⟩
  map_add' x y := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp

@[simp] theorem blockOperatorLinear_apply (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : lp K 2) (i : ι) :
    blockOperatorLinear T hC hT x i = T i (x i) := rfl

theorem blockOperatorLinear_norm_le (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : lp K 2) :
    ‖blockOperatorLinear T hC hT x‖ ≤ C * ‖x‖ := by
  have hleft : (0 : ℝ) ≤ ‖blockOperatorLinear T hC hT x‖ := norm_nonneg _
  have hright : (0 : ℝ) ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  have hdiag : ‖blockOperatorLinear T hC hT x‖ ^ (2 : ℝ)
      = ∑' i, ‖(blockOperatorLinear T hC hT x : ∀ i, K i) i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := K) (by norm_num)
      (blockOperatorLinear T hC hT x)
  have hx : ‖x‖ ^ (2 : ℝ) = ∑' i, ‖(x : ∀ i, K i) i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := K) (by norm_num) x
  have hsumx : Summable fun i => ‖(x : ∀ i, K i) i‖ ^ (2 : ℝ) :=
    (lp.memℓp x).summable (by norm_num)
  have hsumdiag : Summable fun i =>
      ‖(blockOperatorLinear T hC hT x : ∀ i, K i) i‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ i, ‖(blockOperatorLinear T hC hT x : ∀ i, K i) i‖ ^ (2 : ℝ)
      ≤ C ^ (2 : ℝ) * ‖(x : ∀ i, K i) i‖ ^ (2 : ℝ) := by
    intro i
    have hle : ‖T i ((x : ∀ i, K i) i)‖ ≤ C * ‖(x : ∀ i, K i) i‖ :=
      le_trans ((T i).le_opNorm _) (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
    calc ‖(blockOperatorLinear T hC hT x : ∀ i, K i) i‖ ^ (2 : ℝ)
        = ‖T i ((x : ∀ i, K i) i)‖ ^ (2 : ℝ) := by rw [blockOperatorLinear_apply]
      _ ≤ (C * ‖(x : ∀ i, K i) i‖) ^ (2 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) hle (by norm_num)
      _ = C ^ (2 : ℝ) * ‖(x : ∀ i, K i) i‖ ^ (2 : ℝ) := Real.mul_rpow hC (norm_nonneg _)
  have hpow : ‖blockOperatorLinear T hC hT x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ) := by
    rw [hdiag, Real.mul_rpow hC (norm_nonneg _), hx, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumdiag (hsumx.mul_left (C ^ (2 : ℝ)))
  have hleft2 : ‖blockOperatorLinear T hC hT x‖ ^ (2 : ℝ)
      = ‖blockOperatorLinear T hC hT x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hright2 : (C * ‖x‖) ^ (2 : ℝ) = (C * ‖x‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hleft2, hright2] at hpow
  have hsqrt := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

/-- **The block-diagonal operator** attached to a uniformly bounded family of blocks. -/
noncomputable def blockOperator (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) : lp K 2 →L[𝕜] lp K 2 :=
  LinearMap.mkContinuous (blockOperatorLinear T hC hT) C (blockOperatorLinear_norm_le T hC hT)

@[simp] theorem blockOperator_apply (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : lp K 2) (i : ι) :
    blockOperator T hC hT x i = T i (x i) := rfl

theorem norm_blockOperator_le (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) : ‖blockOperator T hC hT‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (blockOperatorLinear_norm_le T hC hT)

/-- **Blockwise injectivity is injectivity.** -/
theorem blockOperator_injective (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (hinj : ∀ i, Function.Injective (T i)) :
    Function.Injective (blockOperator T hC hT) := by
  intro x y hxy
  refine lp.ext ?_
  funext i
  refine hinj i ?_
  have := congrArg (fun z : lp K 2 => (z : ∀ i, K i) i) hxy
  simpa using this

variable [DecidableEq ι]

theorem blockOperator_single (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (i : ι) (v : K i) :
    blockOperator T hC hT (lp.single 2 i v) = lp.single 2 i (T i v) := by
  refine lp.ext ?_
  funext j
  rw [blockOperator_apply, lp.single_apply, lp.single_apply]
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

/-- **Blockwise surjectivity gives dense range.** -/
theorem denseRange_blockOperator (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (hsurj : ∀ i, Function.Surjective (T i)) :
    DenseRange (blockOperator T hC hT) := by
  set R : Submodule 𝕜 (lp K 2) := LinearMap.range (blockOperator T hC hT : lp K 2 →ₗ[𝕜] lp K 2)
    with hR
  have hsingle : ∀ (i : ι) (v : K i), lp.single 2 i v ∈ R := by
    intro i v
    obtain ⟨w, hw⟩ := hsurj i v
    exact ⟨lp.single 2 i w, by simp [blockOperator_single, hw]⟩
  have hcoe : (R : Set (lp K 2)) = Set.range (blockOperator T hC hT) := by
    ext y
    simp [hR, LinearMap.mem_range, Set.mem_range]
  intro f
  rw [← hcoe]
  have hsum := lp.hasSum_single (E := K) (p := 2) (by norm_num) f
  refine mem_closure_of_tendsto hsum (Filter.Eventually.of_forall fun s => ?_)
  exact Submodule.sum_mem _ fun i _ => hsingle i _

variable [∀ i, CompleteSpace (K i)]

/-- **Blocks that are not uniformly bounded below make the operator non-invertible.** -/
theorem not_surjective_blockOperator (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (hinj : ∀ i, Function.Injective (T i))
    (hnull : ∀ ε : ℝ, 0 < ε → ∃ (i : ι) (v : K i), ‖v‖ = 1 ∧ ‖T i v‖ < ε) :
    ¬ Function.Surjective (blockOperator T hC hT) := by
  intro hsurj
  have hunit : IsUnit (blockOperator T hC hT) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨blockOperator_injective T hC hT hinj, hsurj⟩
  obtain ⟨u, hu⟩ := hunit
  set S : lp K 2 →L[𝕜] lp K 2 := (↑u⁻¹ : lp K 2 →L[𝕜] lp K 2) with hS
  have hSinv : ∀ x : lp K 2, S (blockOperator T hC hT x) = x := by
    intro x
    have : (↑u⁻¹ * ↑u : lp K 2 →L[𝕜] lp K 2) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hx := congrArg (fun f : lp K 2 →L[𝕜] lp K 2 => f x) this
    simpa [hS, hu] using hx
  have hSpos : 0 < ‖S‖ + 1 := by positivity
  obtain ⟨i, v, hv1, hvlt⟩ := hnull ((‖S‖ + 1)⁻¹) (by positivity)
  have hnorm : ‖lp.single 2 i v‖ = 1 := by
    rw [lp.norm_single (by norm_num), hv1]
  have hkey : ‖lp.single 2 i v‖ ≤ ‖S‖ * ‖blockOperator T hC hT (lp.single 2 i v)‖ := by
    conv_lhs => rw [← hSinv (lp.single 2 i v)]
    exact S.le_opNorm _
  rw [hnorm, blockOperator_single, lp.norm_single (by norm_num)] at hkey
  have hSnn : (0 : ℝ) ≤ ‖S‖ := norm_nonneg _
  have hlt : ‖S‖ * ‖T i v‖ < 1 := by
    calc ‖S‖ * ‖T i v‖ ≤ ‖S‖ * (‖S‖ + 1)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hvlt.le hSnn
      _ < 1 := by
          rw [mul_inv_lt_iff₀ hSpos]
          linarith
  linarith

theorem range_blockOperator_ne_top (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (hinj : ∀ i, Function.Injective (T i))
    (hnull : ∀ ε : ℝ, 0 < ε → ∃ (i : ι) (v : K i), ‖v‖ = 1 ∧ ‖T i v‖ < ε) :
    LinearMap.range (blockOperator T hC hT : lp K 2 →ₗ[𝕜] lp K 2) ≠ ⊤ := by
  intro h
  exact not_surjective_blockOperator T hC hT hinj hnull (LinearMap.range_eq_top.mp h)

/-- **The dense range is not closed.**  A closed dense subspace would be everything. -/
theorem not_isClosed_range_blockOperator (T : ∀ i, K i →L[𝕜] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (hinj : ∀ i, Function.Injective (T i))
    (hsurj : ∀ i, Function.Surjective (T i))
    (hnull : ∀ ε : ℝ, 0 < ε → ∃ (i : ι) (v : K i), ‖v‖ = 1 ∧ ‖T i v‖ < ε) :
    ¬ IsClosed (Set.range (blockOperator T hC hT)) := by
  intro hclosed
  have hdense := denseRange_blockOperator T hC hT hsurj
  have huniv : Set.range (blockOperator T hC hT) = Set.univ := by
    rw [← hclosed.closure_eq]
    exact hdense.closure_eq
  exact not_surjective_blockOperator T hC hT hinj hnull
    (Set.range_eq_univ.mp huniv)

end BlockOperator

end GaloisForLFunctions.HTGeometry
