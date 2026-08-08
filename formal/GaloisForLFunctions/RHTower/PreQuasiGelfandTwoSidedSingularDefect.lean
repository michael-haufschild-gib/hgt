import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator
import GaloisForLFunctions.HTGeometry.MaximalRealDiagonalSelfAdjoint
import Mathlib.Analysis.PSeries

/-!
# Two-sided singular defects in pre-quasi Gelfand triples

This module gives three unconditional results.

* `preQuasi_graph_le_canonical_graph` and
  `preQuasi_of_closed_biDense_canonicalGraphSubspace` classify compatible negative embeddings as
  closed bi-dense subspaces of the inverse-adjoint graph.
* `twoSidedSingular_iff_hasProperClosedBiDenseSubspace` proves the sharp boundary: a proper closed
  bi-dense graph defect exists exactly when both graph-coordinate maps lack uniform lower bounds;
  the construction is a codimension-one orthogonal hyperplane.
* `exists_hilbertPreQuasiPair_not_quasi` constructs an explicit counterexample on
  `ℓ²(Bool × ℕ)`. The two Bool channels are the even and odd coordinates of `ℓ²(ℕ)`. One diagonal
  is singular only in the first channel and the other only in the second. Their common defect
  hyperplane has dense domain and dense range, but it is a proper closed restriction.

These statements falsify automatic Hilbert pre-quasi-to-quasi compatibility. No spectral,
positivity, finite-dimensional, or unproved density hypothesis is used.
-/

open scoped InnerProductSpace LinearPMap

noncomputable section

namespace RHTower

abbrev PQIndex := Bool × ℕ
abbrev PQHilbert := DiagonalL2 PQIndex

def pqInv (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ)⁻¹

def pqPWeight : PQIndex → ℝ
  | (false, k) => pqInv k
  | (true, _) => 1

def pqQWeight : PQIndex → ℝ
  | (false, _) => 1
  | (true, k) => pqInv k

def pqVWeight : PQIndex → ℂ := fun q => (pqInv q.2 : ℂ)

theorem pqInv_pos (k : ℕ) : 0 < pqInv k := by
  simp [pqInv]
  positivity

theorem pqInv_le_one (k : ℕ) : pqInv k ≤ 1 := by
  rw [pqInv, inv_le_one₀]
  · norm_num
  · positivity

theorem pqPWeight_norm_le_one (q : PQIndex) : ‖(pqPWeight q : ℂ)‖ ≤ 1 := by
  rcases q with ⟨b, k⟩
  cases b <;> simp [pqPWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pqInv_pos k).le, pqInv_le_one]

theorem pqQWeight_norm_le_one (q : PQIndex) : ‖(pqQWeight q : ℂ)‖ ≤ 1 := by
  rcases q with ⟨b, k⟩
  cases b <;> simp [pqQWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pqInv_pos k).le, pqInv_le_one]

theorem pq_memℓp_diagonal {lam : PQIndex → ℂ} {C : ℝ}
    (hC : ∀ q, ‖lam q‖ ≤ C) (f : PQHilbert) :
    Memℓp (fun q => lam q * f q) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun q => ‖f q‖ ^ (2 : ℝ) :=
    (lp.memℓp f).summable (by norm_num)
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC (false, 0))
  refine Summable.of_nonneg_of_le
    (fun q => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (C ^ (2 : ℝ)))
  intro q
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) (hC q) (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) 2)

def pqDiagonalLinearMap (lam : PQIndex → ℂ) {C : ℝ} (hC : ∀ q, ‖lam q‖ ≤ C) :
    PQHilbert →ₗ[ℂ] PQHilbert where
  toFun f := ⟨fun q => lam q * f q, pq_memℓp_diagonal hC f⟩
  map_add' := by
    intro f g
    ext q
    simp [mul_add]
  map_smul' := by
    intro c f
    ext q
    simp [mul_left_comm]

@[simp] theorem pqDiagonalLinearMap_apply (lam : PQIndex → ℂ) {C : ℝ}
    (hC : ∀ q, ‖lam q‖ ≤ C) (f : PQHilbert) (q : PQIndex) :
    pqDiagonalLinearMap lam hC f q = lam q * f q := rfl

theorem norm_pqDiagonalLinearMap_le (lam : PQIndex → ℂ) {C : ℝ}
    (hC : ∀ q, ‖lam q‖ ≤ C) (f : PQHilbert) :
    ‖pqDiagonalLinearMap lam hC f‖ ≤ C * ‖f‖ := by
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC (false, 0))
  have hnn : (0 : ℝ) ≤ ‖pqDiagonalLinearMap lam hC f‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ C * ‖f‖ := mul_nonneg hCnn (norm_nonneg _)
  have htsumD : ‖pqDiagonalLinearMap lam hC f‖ ^ (2 : ℝ) =
      ∑' q, ‖(pqDiagonalLinearMap lam hC f) q‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : PQIndex => ℂ)
      (by norm_num) (pqDiagonalLinearMap lam hC f)
  have htsumf : ‖f‖ ^ (2 : ℝ) = ∑' q, ‖f q‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : PQIndex => ℂ)
      (by norm_num) f
  have hsumf : Summable fun q => ‖f q‖ ^ (2 : ℝ) :=
    (lp.memℓp f).summable (by norm_num)
  have hsumD : Summable fun q => ‖(pqDiagonalLinearMap lam hC f) q‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ q, ‖(pqDiagonalLinearMap lam hC f) q‖ ^ (2 : ℝ) ≤
      C ^ (2 : ℝ) * ‖f q‖ ^ (2 : ℝ) := by
    intro q
    rw [pqDiagonalLinearMap_apply, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (hC q) (by norm_num))
      (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow : ‖pqDiagonalLinearMap lam hC f‖ ^ (2 : ℝ) ≤
      (C * ‖f‖) ^ (2 : ℝ) := by
    rw [htsumD, Real.mul_rpow hCnn (norm_nonneg _), htsumf, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumD
      (hsumf.mul_left (C ^ (2 : ℝ)))
  have hx2 : ‖pqDiagonalLinearMap lam hC f‖ ^ (2 : ℝ) =
      ‖pqDiagonalLinearMap lam hC f‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hy2 : (C * ‖f‖) ^ (2 : ℝ) = (C * ‖f‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs] at hs

def pqDiagonalOperator (lam : PQIndex → ℂ) {C : ℝ} (hC : ∀ q, ‖lam q‖ ≤ C) :
    PQHilbert →L[ℂ] PQHilbert :=
  LinearMap.mkContinuous (pqDiagonalLinearMap lam hC) C
    (norm_pqDiagonalLinearMap_le lam hC)

@[simp] theorem pqDiagonalOperator_apply (lam : PQIndex → ℂ) {C : ℝ}
    (hC : ∀ q, ‖lam q‖ ≤ C) (f : PQHilbert) (q : PQIndex) :
    pqDiagonalOperator lam hC f q = lam q * f q := rfl

def pqP : PQHilbert →L[ℂ] PQHilbert :=
  pqDiagonalOperator (fun q => (pqPWeight q : ℂ)) pqPWeight_norm_le_one

def pqQ : PQHilbert →L[ℂ] PQHilbert :=
  pqDiagonalOperator (fun q => (pqQWeight q : ℂ)) pqQWeight_norm_le_one

@[simp] theorem pqP_apply (x : PQHilbert) (q : PQIndex) :
    pqP x q = (pqPWeight q : ℂ) * x q :=
  pqDiagonalOperator_apply _ _ _ _

@[simp] theorem pqQ_apply (x : PQHilbert) (q : PQIndex) :
    pqQ x q = (pqQWeight q : ℂ) * x q :=
  pqDiagonalOperator_apply _ _ _ _

theorem pqVWeight_summable_sq : Summable (fun q : PQIndex => ‖pqVWeight q‖ ^ 2) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  have hbase : Summable (fun k : ℕ => (1 / (((k + 1 : ℕ) : ℝ) ^ 2))) := by
    exact (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  constructor
  · intro b
    refine hbase.congr fun k => ?_
    simp [pqVWeight, pqInv, Nat.cast_add, Nat.cast_one,
      one_div, inv_pow]
    have hnorm : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
      rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by norm_num,
        norm_natCast]
      norm_num
    rw [hnorm]
  · exact Summable.of_finite

def pqV : PQHilbert :=
  ⟨pqVWeight, HilbertSchmidt.memℓp_of_sq pqVWeight_summable_sq⟩

@[simp] theorem pqV_apply (q : PQIndex) : pqV q = pqVWeight q := rfl

theorem pqPWeight_ne_zero (q : PQIndex) : (pqPWeight q : ℂ) ≠ 0 := by
  rcases q with ⟨b, k⟩
  cases b
  · exact_mod_cast (pqInv_pos k).ne'
  · simp [pqPWeight]

theorem pqQWeight_ne_zero (q : PQIndex) : (pqQWeight q : ℂ) ≠ 0 := by
  rcases q with ⟨b, k⟩
  cases b
  · simp [pqQWeight]
  · exact_mod_cast (pqInv_pos k).ne'

theorem pqP_injective : Function.Injective pqP := by
  intro x y hxy
  ext q
  have hq := congrArg (fun z : PQHilbert => z q) hxy
  simp only [pqP_apply] at hq
  exact mul_left_cancel₀ (pqPWeight_ne_zero q) hq

theorem pqQ_injective : Function.Injective pqQ := by
  intro x y hxy
  ext q
  have hq := congrArg (fun z : PQHilbert => z q) hxy
  simp only [pqQ_apply] at hq
  exact mul_left_cancel₀ (pqQWeight_ne_zero q) hq

theorem pqP_denseRange : DenseRange pqP := by
  have hle : Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis PQIndex)) ≤
      LinearMap.range pqP.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    rw [HilbertSchmidt.lpBasis_apply]
    refine ⟨((pqPWeight q : ℂ)⁻¹ • lp.single 2 q 1 : PQHilbert), ?_⟩
    ext r
    change (pqPWeight r : ℂ) *
      (((pqPWeight q : ℂ)⁻¹ • lp.single 2 q 1 : PQHilbert) r) =
        (lp.single 2 q 1 : PQHilbert) r
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hr : r = q
    · subst r
      simpa using mul_inv_cancel₀ (pqPWeight_ne_zero q)
    · simp [lp.single_apply, hr]
  apply (Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (HilbertSchmidt.lpBasis PQIndex).dense_span).mono
  intro x hx
  rcases hle hx with ⟨y, hy⟩
  exact ⟨y, hy⟩

theorem pqQ_denseRange : DenseRange pqQ := by
  have hle : Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis PQIndex)) ≤
      LinearMap.range pqQ.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    rw [HilbertSchmidt.lpBasis_apply]
    refine ⟨((pqQWeight q : ℂ)⁻¹ • lp.single 2 q 1 : PQHilbert), ?_⟩
    ext r
    change (pqQWeight r : ℂ) *
      (((pqQWeight q : ℂ)⁻¹ • lp.single 2 q 1 : PQHilbert) r) =
        (lp.single 2 q 1 : PQHilbert) r
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hr : r = q
    · subst r
      simpa using mul_inv_cancel₀ (pqQWeight_ne_zero q)
    · simp [lp.single_apply, hr]
  apply (Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (HilbertSchmidt.lpBasis PQIndex).dense_span).mono
  intro x hx
  rcases hle hx with ⟨y, hy⟩
  exact ⟨y, hy⟩

theorem pqP_inner (x y : PQHilbert) :
    inner ℂ (pqP x) y = inner ℂ x (pqP y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  rw [pqP_apply, pqP_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem pqQ_inner (x y : PQHilbert) :
    inner ℂ (pqQ x) y = inner ℂ x (pqQ y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  rw [pqQ_apply, pqQ_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem pqV_not_mem_range_pqP : pqV ∉ LinearMap.range pqP.toLinearMap := by
  rintro ⟨x, hx⟩
  have hxone : ∀ k : ℕ, x (false, k) = 1 := by
    intro k
    have hk := congrArg (fun z : PQHilbert => z (false, k)) hx
    change (pqInv k : ℂ) * x (false, k) = (pqInv k : ℂ) at hk
    exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (pqInv_pos k).ne')
      (by simpa using hk))
  have hs := (HilbertSchmidt.summable_coe_sq x).comp_injective
    (i := fun k : ℕ => (false, k)) (by intro i j h; exact congrArg Prod.snd h)
  have hsone : Summable (fun _k : ℕ => (1 : ℝ)) := by
    refine hs.congr fun k => ?_
    simp [hxone k]
  exact Set.infinite_univ (Set.Finite.of_summable_const (by norm_num) hsone)

theorem pqV_not_mem_range_pqQ : pqV ∉ LinearMap.range pqQ.toLinearMap := by
  rintro ⟨x, hx⟩
  have hxone : ∀ k : ℕ, x (true, k) = 1 := by
    intro k
    have hk := congrArg (fun z : PQHilbert => z (true, k)) hx
    change (pqInv k : ℂ) * x (true, k) = (pqInv k : ℂ) at hk
    exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (pqInv_pos k).ne')
      (by simpa using hk))
  have hs := (HilbertSchmidt.summable_coe_sq x).comp_injective
    (i := fun k : ℕ => (true, k)) (by intro i j h; exact congrArg Prod.snd h)
  have hsone : Summable (fun _k : ℕ => (1 : ℝ)) := by
    refine hs.congr fun k => ?_
    simp [hxone k]
  exact Set.infinite_univ (Set.Finite.of_summable_const (by norm_num) hsone)

def pqDefectHyperplane : Submodule ℂ PQHilbert := (ℂ ∙ pqV)ᗮ

def pqDefectDomain : Submodule ℂ PQHilbert :=
  pqDefectHyperplane.map pqP.toLinearMap

def pqDefectRange : Submodule ℂ PQHilbert :=
  pqDefectHyperplane.map pqQ.toLinearMap

theorem pqDefectHyperplane_orthogonal : pqDefectHyperplaneᗮ = ℂ ∙ pqV := by
  rw [pqDefectHyperplane, Submodule.orthogonal_orthogonal_eq_closure,
    (ℂ ∙ pqV).closed_of_finiteDimensional.submodule_topologicalClosure_eq]

theorem pqDefectDomain_dense : Dense (pqDefectDomain : Set PQHilbert) := by
  have horth : pqDefectDomainᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hPy : pqP y ∈ pqDefectHyperplaneᗮ := by
      rw [Submodule.mem_orthogonal]
      intro m hm
      rw [← pqP_inner]
      exact hy (pqP m) ⟨m, hm, rfl⟩
    rw [pqDefectHyperplane_orthogonal, Submodule.mem_span_singleton] at hPy
    rcases hPy with ⟨a, ha⟩
    by_cases ha0 : a = 0
    · rw [ha0, zero_smul] at ha
      apply pqP_injective
      simpa using ha.symm
    · exfalso
      apply pqV_not_mem_range_pqP
      refine ⟨a⁻¹ • y, ?_⟩
      rw [map_smul]
      change a⁻¹ • (pqP y : PQHilbert) = pqV
      calc
        a⁻¹ • (pqP y : PQHilbert) = a⁻¹ • (a • pqV) := congrArg (a⁻¹ • ·) ha.symm
        _ = pqV := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  simpa using horth

theorem pqDefectRange_dense : Dense (pqDefectRange : Set PQHilbert) := by
  have horth : pqDefectRangeᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hQy : pqQ y ∈ pqDefectHyperplaneᗮ := by
      rw [Submodule.mem_orthogonal]
      intro m hm
      rw [← pqQ_inner]
      exact hy (pqQ m) ⟨m, hm, rfl⟩
    rw [pqDefectHyperplane_orthogonal, Submodule.mem_span_singleton] at hQy
    rcases hQy with ⟨a, ha⟩
    by_cases ha0 : a = 0
    · rw [ha0, zero_smul] at ha
      apply pqQ_injective
      simpa using ha.symm
    · exfalso
      apply pqV_not_mem_range_pqQ
      refine ⟨a⁻¹ • y, ?_⟩
      rw [map_smul]
      change a⁻¹ • (pqQ y : PQHilbert) = pqV
      calc
        a⁻¹ • (pqQ y : PQHilbert) = a⁻¹ • (a • pqV) := congrArg (a⁻¹ • ·) ha.symm
        _ = pqV := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  simpa using horth

def pqFalseMaskWeight : PQIndex → ℂ
  | (false, _) => 1
  | (true, _) => 0

def pqTrueMaskWeight : PQIndex → ℂ
  | (false, _) => 0
  | (true, _) => 1

theorem pqFalseMaskWeight_norm_le_one (q : PQIndex) : ‖pqFalseMaskWeight q‖ ≤ 1 := by
  rcases q with ⟨b, k⟩
  cases b <;> simp [pqFalseMaskWeight]

theorem pqTrueMaskWeight_norm_le_one (q : PQIndex) : ‖pqTrueMaskWeight q‖ ≤ 1 := by
  rcases q with ⟨b, k⟩
  cases b <;> simp [pqTrueMaskWeight]

def pqFalseMask : PQHilbert →L[ℂ] PQHilbert :=
  pqDiagonalOperator pqFalseMaskWeight pqFalseMaskWeight_norm_le_one

def pqTrueMask : PQHilbert →L[ℂ] PQHilbert :=
  pqDiagonalOperator pqTrueMaskWeight pqTrueMaskWeight_norm_le_one

@[simp] theorem pqFalseMask_apply_false (x : PQHilbert) (k : ℕ) :
    pqFalseMask x (false, k) = x (false, k) := by
  simp [pqFalseMask, pqDiagonalOperator_apply, pqFalseMaskWeight]

@[simp] theorem pqFalseMask_apply_true (x : PQHilbert) (k : ℕ) :
    pqFalseMask x (true, k) = 0 := by
  simp [pqFalseMask, pqDiagonalOperator_apply, pqFalseMaskWeight]

@[simp] theorem pqTrueMask_apply_false (x : PQHilbert) (k : ℕ) :
    pqTrueMask x (false, k) = 0 := by
  simp [pqTrueMask, pqDiagonalOperator_apply, pqTrueMaskWeight]

@[simp] theorem pqTrueMask_apply_true (x : PQHilbert) (k : ℕ) :
    pqTrueMask x (true, k) = x (true, k) := by
  simp [pqTrueMask, pqDiagonalOperator_apply, pqTrueMaskWeight]

/-- Recover graph parameter from `(P m, Q m)`: use `Q m` in first channel and `P m` in second. -/
def pqGraphRecover : PQHilbert × PQHilbert →L[ℂ] PQHilbert :=
  pqFalseMask.comp (ContinuousLinearMap.snd ℂ PQHilbert PQHilbert) +
    pqTrueMask.comp (ContinuousLinearMap.fst ℂ PQHilbert PQHilbert)

theorem pqGraphRecover_pair (m : PQHilbert) : pqGraphRecover (pqP m, pqQ m) = m := by
  ext q
  rcases q with ⟨b, k⟩
  cases b <;> simp [pqGraphRecover, pqPWeight, pqQWeight]

def pqGraphMap : PQHilbert →ₗ[ℂ] PQHilbert × PQHilbert :=
  pqP.toLinearMap.prod pqQ.toLinearMap

def pqDefectGraph : Submodule ℂ (PQHilbert × PQHilbert) :=
  pqDefectHyperplane.map pqGraphMap

def pqGraphFirstDefect : PQHilbert × PQHilbert →L[ℂ] PQHilbert :=
  pqP.comp pqGraphRecover - ContinuousLinearMap.fst ℂ PQHilbert PQHilbert

def pqGraphSecondDefect : PQHilbert × PQHilbert →L[ℂ] PQHilbert :=
  pqQ.comp pqGraphRecover - ContinuousLinearMap.snd ℂ PQHilbert PQHilbert

def pqGraphHyperplaneDefect : PQHilbert × PQHilbert →L[ℂ] ℂ :=
  (innerSL ℂ pqV).comp pqGraphRecover

theorem mem_pqDefectHyperplane_iff (x : PQHilbert) :
    x ∈ pqDefectHyperplane ↔ inner ℂ pqV x = 0 := by
  rw [pqDefectHyperplane, Submodule.mem_orthogonal]
  constructor
  · intro hx
    exact hx pqV (Submodule.mem_span_singleton_self pqV)
  · intro hx y hy
    rcases Submodule.mem_span_singleton.mp hy with ⟨a, rfl⟩
    rw [inner_smul_left, hx, mul_zero]

theorem pqDefectGraph_eq_kernels :
    pqDefectGraph = pqGraphFirstDefect.ker ⊓ pqGraphSecondDefect.ker ⊓
      pqGraphHyperplaneDefect.ker := by
  ext z
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hrecover := pqGraphRecover_pair m
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change pqP (pqGraphRecover (pqP m, pqQ m)) - pqP m = 0
      rw [hrecover, sub_self]
    · change pqQ (pqGraphRecover (pqP m, pqQ m)) - pqQ m = 0
      rw [hrecover, sub_self]
    · change inner ℂ pqV (pqGraphRecover (pqP m, pqQ m)) = 0
      rw [hrecover]
      exact (mem_pqDefectHyperplane_iff m).mp hm
  · rintro ⟨⟨hfirst, hsecond⟩, hhyper⟩
    let m : PQHilbert := pqGraphRecover z
    have hPm : pqP m = z.1 := by
      change pqP (pqGraphRecover z) - z.1 = 0 at hfirst
      exact sub_eq_zero.mp hfirst
    have hQm : pqQ m = z.2 := by
      change pqQ (pqGraphRecover z) - z.2 = 0 at hsecond
      exact sub_eq_zero.mp hsecond
    have hm : m ∈ pqDefectHyperplane := by
      rw [mem_pqDefectHyperplane_iff]
      exact hhyper
    refine ⟨m, hm, ?_⟩
    exact Prod.ext hPm hQm

theorem pqDefectGraph_isClosed : IsClosed (pqDefectGraph : Set (PQHilbert × PQHilbert)) := by
  rw [pqDefectGraph_eq_kernels]
  exact (pqGraphFirstDefect.isClosed_ker.inter pqGraphSecondDefect.isClosed_ker).inter
    pqGraphHyperplaneDefect.isClosed_ker

theorem pqDefectGraph_vertical_unique (z : PQHilbert × PQHilbert)
    (hz : z ∈ pqDefectGraph) (hz0 : z.1 = 0) : z.2 = 0 := by
  rcases hz with ⟨m, hm, hmz⟩
  have hPm : pqP m = z.1 := congrArg Prod.fst hmz
  have hm0 : m = 0 := pqP_injective (hPm.trans (hz0.trans (map_zero pqP).symm))
  have hQm : pqQ m = z.2 := congrArg Prod.snd hmz
  simpa [hm0] using hQm.symm

def pqDefectNegativeEmbedding : PQHilbert →ₗ.[ℂ] PQHilbert :=
  pqDefectGraph.toLinearPMap

theorem pqDefectNegativeEmbedding_graph : pqDefectNegativeEmbedding.graph = pqDefectGraph :=
  Submodule.toLinearPMap_graph_eq pqDefectGraph pqDefectGraph_vertical_unique

theorem pqDefectNegativeEmbedding_isClosed : pqDefectNegativeEmbedding.IsClosed := by
  rw [LinearPMap.IsClosed, pqDefectNegativeEmbedding_graph]
  exact pqDefectGraph_isClosed

theorem pqDefectNegativeEmbedding_domain :
    pqDefectNegativeEmbedding.domain = pqDefectDomain := by
  rw [← LinearPMap.graph_map_fst_eq_domain, pqDefectNegativeEmbedding_graph]
  ext x
  simp [pqDefectGraph, pqDefectDomain, pqGraphMap]

theorem pqDefectNegativeEmbedding_range :
    LinearMap.range pqDefectNegativeEmbedding.toFun = pqDefectRange := by
  rw [← LinearPMap.graph_map_snd_eq_range, pqDefectNegativeEmbedding_graph]
  ext x
  constructor
  · intro hx
    rcases hx with ⟨z, hz, hzx⟩
    rcases hz with ⟨m, hm, hmz⟩
    refine ⟨m, hm, ?_⟩
    exact (congrArg Prod.snd hmz).trans hzx
  · intro hx
    rcases hx with ⟨m, hm, hmx⟩
    refine ⟨(pqP m, pqQ m), ⟨m, hm, rfl⟩, ?_⟩
    exact hmx

theorem pqDefectNegativeEmbedding_dense_domain :
    Dense (pqDefectNegativeEmbedding.domain : Set PQHilbert) := by
  rw [pqDefectNegativeEmbedding_domain]
  exact pqDefectDomain_dense

theorem pqDefectNegativeEmbedding_dense_range :
    Dense (LinearMap.range pqDefectNegativeEmbedding.toFun : Set PQHilbert) := by
  rw [pqDefectNegativeEmbedding_range]
  exact pqDefectRange_dense

theorem pqDefectNegativeEmbedding_injective :
    Function.Injective pqDefectNegativeEmbedding.toFun := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hgraph := pqDefectNegativeEmbedding.mem_graph x
  rw [pqDefectNegativeEmbedding_graph] at hgraph
  rcases hgraph with ⟨m, hm, hmgraph⟩
  have hPm : pqP m = (x : PQHilbert) := congrArg Prod.fst hmgraph
  have hQm : pqQ m = pqDefectNegativeEmbedding x := congrArg Prod.snd hmgraph
  have hm0 : m = 0 := pqQ_injective (hQm.trans (hx.trans (map_zero pqQ).symm))
  apply Subtype.ext
  simpa [hm0] using hPm.symm

def pqPositiveEnergy : PQIndex → ℝ
  | (false, k) => pqInv k
  | (true, k) => (k + 1 : ℕ)

def pqCanonicalNegativeEnergy : PQIndex → ℝ
  | (false, k) => (k + 1 : ℕ)
  | (true, k) => pqInv k

def pqPositiveEmbedding : PQHilbert →ₗ.[ℂ] PQHilbert :=
  maximalRealDiagonal pqPositiveEnergy

def pqCanonicalNegativeEmbedding : PQHilbert →ₗ.[ℂ] PQHilbert :=
  maximalRealDiagonal pqCanonicalNegativeEnergy

theorem pqPositiveEnergy_ne_zero (q : PQIndex) : (pqPositiveEnergy q : ℂ) ≠ 0 := by
  rcases q with ⟨b, k⟩
  cases b
  · exact_mod_cast (pqInv_pos k).ne'
  · apply Complex.ofReal_ne_zero.mpr
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    exact hk.ne'

theorem pqCanonicalNegativeEnergy_ne_zero (q : PQIndex) :
    (pqCanonicalNegativeEnergy q : ℂ) ≠ 0 := by
  rcases q with ⟨b, k⟩
  cases b
  · apply Complex.ofReal_ne_zero.mpr
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    exact hk.ne'
  · exact_mod_cast (pqInv_pos k).ne'

theorem pqPositiveEmbedding_injective : Function.Injective pqPositiveEmbedding.toFun := by
  intro x y hxy
  apply Subtype.ext
  ext q
  have hq := congrArg (fun z : PQHilbert => z q) hxy
  change (pqPositiveEnergy q : ℂ) * (x : PQHilbert) q =
    (pqPositiveEnergy q : ℂ) * (y : PQHilbert) q at hq
  exact mul_left_cancel₀ (pqPositiveEnergy_ne_zero q) hq

theorem pqCanonicalNegativeEmbedding_injective :
    Function.Injective pqCanonicalNegativeEmbedding.toFun := by
  intro x y hxy
  apply Subtype.ext
  ext q
  have hq := congrArg (fun z : PQHilbert => z q) hxy
  change (pqCanonicalNegativeEnergy q : ℂ) * (x : PQHilbert) q =
    (pqCanonicalNegativeEnergy q : ℂ) * (y : PQHilbert) q at hq
  exact mul_left_cancel₀ (pqCanonicalNegativeEnergy_ne_zero q) hq

theorem pqPositiveEnergy_mul_qWeight (q : PQIndex) :
    (pqPositiveEnergy q : ℂ) * (pqQWeight q : ℂ) = (pqPWeight q : ℂ) := by
  rcases q with ⟨b, k⟩
  cases b
  · simp [pqPositiveEnergy, pqQWeight, pqPWeight]
  · change (((k + 1 : ℕ) : ℝ) : ℂ) *
      ((((k + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) = 1
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    norm_cast
    exact mul_inv_cancel₀ hk.ne'

theorem pqCanonicalNegativeEnergy_mul_pWeight (q : PQIndex) :
    (pqCanonicalNegativeEnergy q : ℂ) * (pqPWeight q : ℂ) = (pqQWeight q : ℂ) := by
  rcases q with ⟨b, k⟩
  cases b
  · change (((k + 1 : ℕ) : ℝ) : ℂ) *
      ((((k + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) = 1
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    norm_cast
    exact mul_inv_cancel₀ hk.ne'
  · simp [pqCanonicalNegativeEnergy, pqPWeight, pqQWeight]

theorem pqQ_mem_positiveEmbedding_domain (x : PQHilbert) :
    pqQ x ∈ pqPositiveEmbedding.domain := by
  change Memℓp (fun q => (pqPositiveEnergy q : ℂ) * pqQ x q) 2
  rw [show (fun q => (pqPositiveEnergy q : ℂ) * pqQ x q) = fun q => pqP x q by
    funext q
    rw [pqQ_apply, pqP_apply, ← mul_assoc, pqPositiveEnergy_mul_qWeight]]
  exact lp.memℓp (pqP x)

theorem pqPositiveEmbedding_pqQ (x : PQHilbert) :
    pqPositiveEmbedding ⟨pqQ x, pqQ_mem_positiveEmbedding_domain x⟩ = pqP x := by
  ext q
  change (pqPositiveEnergy q : ℂ) * pqQ x q = pqP x q
  rw [pqQ_apply, pqP_apply, ← mul_assoc,
    pqPositiveEnergy_mul_qWeight]

theorem pqP_mem_canonicalNegativeEmbedding_domain (x : PQHilbert) :
    pqP x ∈ pqCanonicalNegativeEmbedding.domain := by
  change Memℓp (fun q => (pqCanonicalNegativeEnergy q : ℂ) * pqP x q) 2
  rw [show (fun q => (pqCanonicalNegativeEnergy q : ℂ) * pqP x q) = fun q => pqQ x q by
    funext q
    rw [pqP_apply, pqQ_apply, ← mul_assoc, pqCanonicalNegativeEnergy_mul_pWeight]]
  exact lp.memℓp (pqQ x)

theorem pqCanonicalNegativeEmbedding_pqP (x : PQHilbert) :
    pqCanonicalNegativeEmbedding
      ⟨pqP x, pqP_mem_canonicalNegativeEmbedding_domain x⟩ = pqQ x := by
  ext q
  change (pqCanonicalNegativeEnergy q : ℂ) * pqP x q = pqQ x q
  rw [pqP_apply, pqQ_apply, ← mul_assoc,
    pqCanonicalNegativeEnergy_mul_pWeight]

theorem pqPositiveEmbedding_isSelfAdjoint : IsSelfAdjoint pqPositiveEmbedding :=
  maximalRealDiagonal_isSelfAdjoint pqPositiveEnergy

theorem pqCanonicalNegativeEmbedding_isSelfAdjoint :
    IsSelfAdjoint pqCanonicalNegativeEmbedding :=
  maximalRealDiagonal_isSelfAdjoint pqCanonicalNegativeEnergy

theorem pqPositiveEmbedding_dense_domain :
    Dense (pqPositiveEmbedding.domain : Set PQHilbert) :=
  pqPositiveEmbedding_isSelfAdjoint.dense_domain

theorem pqPositiveEmbedding_isClosed : pqPositiveEmbedding.IsClosed :=
  pqPositiveEmbedding_isSelfAdjoint.isClosed

theorem pqPositiveEmbedding_dense_range :
    Dense (LinearMap.range pqPositiveEmbedding.toFun : Set PQHilbert) := by
  apply pqP_denseRange.mono
  rintro y ⟨x, rfl⟩
  exact ⟨⟨pqQ x, pqQ_mem_positiveEmbedding_domain x⟩,
    pqPositiveEmbedding_pqQ x⟩

theorem pqDefect_pairing
    (g : pqDefectNegativeEmbedding.domain) (f : pqPositiveEmbedding.domain) :
    inner ℂ (pqDefectNegativeEmbedding g) (pqPositiveEmbedding f) =
      inner ℂ (g : PQHilbert) (f : PQHilbert) := by
  have hg := pqDefectNegativeEmbedding.mem_graph g
  rw [pqDefectNegativeEmbedding_graph] at hg
  rcases hg with ⟨m, hm, hmgraph⟩
  have hPm : pqP m = (g : PQHilbert) := congrArg Prod.fst hmgraph
  have hQm : pqQ m = pqDefectNegativeEmbedding g := congrArg Prod.snd hmgraph
  rw [← hQm, ← hPm, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  rw [pqQ_apply, pqP_apply]
  change inner ℂ ((pqQWeight q : ℂ) * m q)
      ((pqPositiveEnergy q : ℂ) * ((f : PQHilbert) q)) =
    inner ℂ ((pqPWeight q : ℂ) * m q) ((f : PQHilbert) q)
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  have hcoeff := pqPositiveEnergy_mul_qWeight q
  rw [mul_comm] at hcoeff
  linear_combination (starRingEnd ℂ) (m q) * ((f : PQHilbert) q) * hcoeff

structure HilbertPreQuasiPair {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (plus minus : H →ₗ.[ℂ] H) : Prop where
  plus_closed : plus.IsClosed
  minus_closed : minus.IsClosed
  plus_dense_domain : Dense (plus.domain : Set H)
  minus_dense_domain : Dense (minus.domain : Set H)
  plus_injective : Function.Injective plus.toFun
  minus_injective : Function.Injective minus.toFun
  plus_dense_range : Dense (LinearMap.range plus.toFun : Set H)
  minus_dense_range : Dense (LinearMap.range minus.toFun : Set H)
  pairing : ∀ (g : minus.domain) (f : plus.domain),
    inner ℂ (minus g) (plus f) = inner ℂ (g : H) (f : H)

def HilbertQuasiCompatibility {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (plus minus : H →ₗ.[ℂ] H) : Prop :=
  LinearMap.range minus.toFun = plus†.domain

section AbstractClassification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Canonical negative embedding forced by a positive embedding: inverse of its adjoint. -/
noncomputable def canonicalNegativeEmbedding (plus : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H :=
  plus†.inverse

theorem adjoint_ker_eq_bot_of_denseRange (plus : H →ₗ.[ℂ] H)
    (hdomain : Dense (plus.domain : Set H))
    (hrange : Dense (LinearMap.range plus.toFun : Set H)) :
    LinearMap.ker plus†.toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro y hy
  apply Subtype.ext
  apply hrange.eq_of_inner_left ℂ
  rintro z ⟨x, rfl⟩
  have hformal := LinearPMap.adjoint_isFormalAdjoint hdomain y x
  calc
    inner ℂ (y : H) (plus x) = inner ℂ (plus† y) (x : H) := hformal.symm
    _ = 0 := by
      have hy' : plus† y = 0 := hy
      rw [hy']
      simp
    _ = inner ℂ (0 : H) (plus x) := by simp

theorem canonicalNegativeEmbedding_injective (plus : H →ₗ.[ℂ] H)
    (hdomain : Dense (plus.domain : Set H))
    (hrange : Dense (LinearMap.range plus.toFun : Set H)) :
    Function.Injective (canonicalNegativeEmbedding plus).toFun := by
  let hker := adjoint_ker_eq_bot_of_denseRange plus hdomain hrange
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hxrange : (x : H) ∈ LinearMap.range plus†.toFun := by
    simpa [canonicalNegativeEmbedding, LinearPMap.inverse_domain] using x.property
  rcases hxrange with ⟨y, hy⟩
  have hinv : canonicalNegativeEmbedding plus x = y := by
    exact LinearPMap.inverse_apply_eq hker hy
  have hy0 : (y : H) = 0 := calc
    (y : H) = canonicalNegativeEmbedding plus x := hinv.symm
    _ = 0 := hx
  have hx0 : (x : H) = 0 := calc
    (x : H) = plus† y := hy.symm
    _ = plus† (0 : plus†.domain) := by congr 1; exact Subtype.ext hy0
    _ = 0 := LinearPMap.map_zero plus†
  exact Subtype.ext hx0

/-- Canonical inverse-adjoint pairing. -/
theorem canonicalNegativeEmbedding_pairing (plus : H →ₗ.[ℂ] H)
    (hdomain : Dense (plus.domain : Set H))
    (hrange : Dense (LinearMap.range plus.toFun : Set H))
    (g : (canonicalNegativeEmbedding plus).domain) (f : plus.domain) :
    inner ℂ (canonicalNegativeEmbedding plus g) (plus f) =
      inner ℂ (g : H) (f : H) := by
  let hker := adjoint_ker_eq_bot_of_denseRange plus hdomain hrange
  have hgrange : (g : H) ∈ LinearMap.range plus†.toFun := by
    simpa [canonicalNegativeEmbedding, LinearPMap.inverse_domain] using g.property
  rcases hgrange with ⟨y, hy⟩
  have hinv : canonicalNegativeEmbedding plus g = y :=
    LinearPMap.inverse_apply_eq hker hy
  have hformal := LinearPMap.adjoint_isFormalAdjoint hdomain y f
  rw [hinv, ← hy]
  exact hformal.symm

/-- Compatibility forces every negative embedding into canonical inverse-adjoint graph. -/
theorem compatible_le_canonicalNegativeEmbedding
    (plus minus : H →ₗ.[ℂ] H)
    (hdomain : Dense (plus.domain : Set H))
    (hrange : Dense (LinearMap.range plus.toFun : Set H))
    (hpair : ∀ (g : minus.domain) (f : plus.domain),
      inner ℂ (minus g) (plus f) = inner ℂ (g : H) (f : H)) :
    minus ≤ canonicalNegativeEmbedding plus := by
  let hker := adjoint_ker_eq_bot_of_denseRange plus hdomain hrange
  apply LinearPMap.le_of_le_graph
  intro z hz
  rw [LinearPMap.mem_graph_iff] at hz
  rcases hz with ⟨g, hzg, hzout⟩
  have hminusAdj : minus g ∈ plus†.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨(g : H), ?_⟩
    intro f
    exact (hpair g f).symm
  let y : plus†.domain := ⟨minus g, hminusAdj⟩
  have hadj : plus† y = (g : H) := by
    apply LinearPMap.adjoint_apply_eq hdomain
    intro f
    exact (hpair g f).symm
  have hinvgraph := LinearPMap.mem_inverse_graph hker y
  change (plus† y, (y : H)) ∈ (canonicalNegativeEmbedding plus).graph at hinvgraph
  rw [hadj] at hinvgraph
  simpa [hzg, hzout, y] using hinvgraph

/-- Necessity half of graph-subspace classification. -/
theorem preQuasi_graph_le_canonical_graph
    (plus minus : H →ₗ.[ℂ] H) (h : HilbertPreQuasiPair plus minus) :
    minus.graph ≤ (canonicalNegativeEmbedding plus).graph :=
  LinearPMap.le_graph_of_le
    (compatible_le_canonicalNegativeEmbedding plus minus h.plus_dense_domain
      h.plus_dense_range h.pairing)

theorem canonicalNegativeEmbedding_range_eq_adjointDomain
    (plus : H →ₗ.[ℂ] H)
    (hdomain : Dense (plus.domain : Set H))
    (hrange : Dense (LinearMap.range plus.toFun : Set H)) :
    LinearMap.range (canonicalNegativeEmbedding plus).toFun = plus†.domain := by
  exact LinearPMap.inverse_range
    (adjoint_ker_eq_bot_of_denseRange plus hdomain hrange)

/-- Quasi compatibility is exactly saturation of canonical graph. -/
theorem preQuasi_quasi_iff_eq_canonicalNegative
    (plus minus : H →ₗ.[ℂ] H) (h : HilbertPreQuasiPair plus minus) :
    HilbertQuasiCompatibility plus minus ↔ minus = canonicalNegativeEmbedding plus := by
  let hle := compatible_le_canonicalNegativeEmbedding plus minus h.plus_dense_domain
    h.plus_dense_range h.pairing
  let hinj := canonicalNegativeEmbedding_injective plus h.plus_dense_domain h.plus_dense_range
  constructor
  · intro hquasi
    apply LinearPMap.eq_of_le_of_domain_eq hle
    apply le_antisymm hle.1
    intro x hx
    have hBx : canonicalNegativeEmbedding plus ⟨x, hx⟩ ∈ plus†.domain := by
      rw [← canonicalNegativeEmbedding_range_eq_adjointDomain plus
        h.plus_dense_domain h.plus_dense_range]
      exact ⟨⟨x, hx⟩, rfl⟩
    rw [← hquasi] at hBx
    rcases hBx with ⟨y, hy⟩
    have hBy : minus y = canonicalNegativeEmbedding plus
        ⟨(y : H), hle.1 y.property⟩ := hle.2 rfl
    have hyx : (y : H) = x := congrArg Subtype.val <| hinj <| by
      exact hBy.symm.trans hy
    exact hyx ▸ y.property
  · rintro rfl
    exact canonicalNegativeEmbedding_range_eq_adjointDomain plus
      h.plus_dense_domain h.plus_dense_range

/-- Sufficiency half: every closed bi-dense graph subspace of canonical graph gives pre-quasi pair. -/
theorem preQuasi_of_closed_biDense_canonicalGraphSubspace
    (plus : H →ₗ.[ℂ] H)
    (hplusClosed : plus.IsClosed)
    (hplusDomain : Dense (plus.domain : Set H))
    (hplusInjective : Function.Injective plus.toFun)
    (hplusRange : Dense (LinearMap.range plus.toFun : Set H))
    (M : Submodule ℂ (H × H))
    (hMle : M ≤ (canonicalNegativeEmbedding plus).graph)
    (hMclosed : IsClosed (M : Set (H × H)))
    (hMfst : Dense (M.map (LinearMap.fst ℂ H H) : Set H))
    (hMsnd : Dense (M.map (LinearMap.snd ℂ H H) : Set H)) :
    HilbertPreQuasiPair plus M.toLinearPMap := by
  let hker := adjoint_ker_eq_bot_of_denseRange plus hplusDomain hplusRange
  have hvertical : ∀ z : H × H, z ∈ M → z.1 = 0 → z.2 = 0 := by
    intro z hz hz0
    exact (canonicalNegativeEmbedding plus).graph_fst_eq_zero_snd (hMle hz) hz0
  have hgraph : M.toLinearPMap.graph = M :=
    Submodule.toLinearPMap_graph_eq M hvertical
  have hminusLe : M.toLinearPMap ≤ canonicalNegativeEmbedding plus := by
    apply LinearPMap.le_of_le_graph
    rw [hgraph]
    exact hMle
  have hminusInj : Function.Injective M.toLinearPMap.toFun := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hBzero : canonicalNegativeEmbedding plus
        ⟨(x : H), hminusLe.1 x.property⟩ = 0 := by
      calc
        canonicalNegativeEmbedding plus
            ⟨(x : H), hminusLe.1 x.property⟩ = M.toLinearPMap x :=
          (hminusLe.2 (x := x)
            (y := ⟨(x : H), hminusLe.1 x.property⟩) rfl).symm
        _ = 0 := hx
    have hxzero : (⟨(x : H), hminusLe.1 x.property⟩ :
        (canonicalNegativeEmbedding plus).domain) = 0 :=
      (canonicalNegativeEmbedding_injective plus hplusDomain hplusRange) <| by
        simpa using hBzero
    apply Subtype.ext
    change (x : H) = 0
    exact congrArg Subtype.val hxzero
  refine
    { plus_closed := hplusClosed
      minus_closed := by
        rw [LinearPMap.IsClosed, hgraph]
        exact hMclosed
      plus_dense_domain := hplusDomain
      minus_dense_domain := by
        rw [← LinearPMap.graph_map_fst_eq_domain, hgraph]
        exact hMfst
      plus_injective := hplusInjective
      minus_injective := hminusInj
      plus_dense_range := hplusRange
      minus_dense_range := by
        rw [← LinearPMap.graph_map_snd_eq_range, hgraph]
        exact hMsnd
      pairing := ?_ }
  intro g f
  have hcanonical := canonicalNegativeEmbedding_pairing plus hplusDomain hplusRange
    ⟨(g : H), hminusLe.1 g.property⟩ f
  have happly := hminusLe.2 (x := g)
    (y := ⟨(g : H), hminusLe.1 g.property⟩) rfl
  simpa [happly] using hcanonical

end AbstractClassification

theorem pqV_ne_zero : pqV ≠ 0 := by
  intro hv
  have h := congrArg (fun x : PQHilbert => x (false, 0)) hv
  norm_num [pqV, pqVWeight, pqInv] at h

theorem pqV_not_mem_defectHyperplane : pqV ∉ pqDefectHyperplane := by
  rw [mem_pqDefectHyperplane_iff]
  exact inner_self_ne_zero.mpr pqV_ne_zero

theorem pqDefect_is_preQuasi :
    HilbertPreQuasiPair pqPositiveEmbedding pqDefectNegativeEmbedding where
  plus_closed := pqPositiveEmbedding_isClosed
  minus_closed := pqDefectNegativeEmbedding_isClosed
  plus_dense_domain := pqPositiveEmbedding_dense_domain
  minus_dense_domain := pqDefectNegativeEmbedding_dense_domain
  plus_injective := pqPositiveEmbedding_injective
  minus_injective := pqDefectNegativeEmbedding_injective
  plus_dense_range := pqPositiveEmbedding_dense_range
  minus_dense_range := pqDefectNegativeEmbedding_dense_range
  pairing := pqDefect_pairing

theorem pqDefect_not_quasi :
    ¬ HilbertQuasiCompatibility pqPositiveEmbedding pqDefectNegativeEmbedding := by
  intro hquasi
  have hQvdom : pqQ pqV ∈ pqPositiveEmbedding†.domain := by
    rw [LinearPMap.isSelfAdjoint_def.mp pqPositiveEmbedding_isSelfAdjoint]
    exact pqQ_mem_positiveEmbedding_domain pqV
  have hQvrange : pqQ pqV ∈ LinearMap.range pqDefectNegativeEmbedding.toFun := by
    rw [hquasi]
    exact hQvdom
  rw [pqDefectNegativeEmbedding_range] at hQvrange
  rcases hQvrange with ⟨m, hm, hQm⟩
  have hmv : m = pqV := pqQ_injective hQm
  exact pqV_not_mem_defectHyperplane (hmv ▸ hm)

/-- Explicit unconditional counterexample to automatic quasi compatibility on `ℓ²(Bool × ℕ)`. -/
theorem exists_hilbertPreQuasiPair_not_quasi :
    ∃ (plus minus : PQHilbert →ₗ.[ℂ] PQHilbert),
      HilbertPreQuasiPair plus minus ∧ ¬ HilbertQuasiCompatibility plus minus :=
  ⟨pqPositiveEmbedding, pqDefectNegativeEmbedding,
    pqDefect_is_preQuasi, pqDefect_not_quasi⟩

section SharpTwoSidedCriterion

variable {G H₁ H₂ : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- A bounded Hilbert operator has surjective adjoint exactly when it is uniformly bounded below,
provided it is injective with dense range. -/
theorem adjoint_surjective_iff_antilipschitz
    (T : G →L[ℂ] H₁) (hinj : Function.Injective T) (hdense : DenseRange T) :
    Function.Surjective T.adjoint ↔ ∃ K : NNReal, AntilipschitzWith K T := by
  constructor
  · intro hsurj
    obtain ⟨C, hC, hpre⟩ := T.adjoint.exists_preimage_norm_le hsurj
    refine ⟨⟨C, hC.le⟩, AntilipschitzWith.of_le_mul_dist ?_⟩
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    let z := x - y
    by_cases hz : z = 0
    · simp [z, hz]
    · obtain ⟨u, hu, hnu⟩ := hpre z
      have hinner : inner ℂ z z = inner ℂ u (T z) := by
        rw [← hu, T.adjoint_inner_left]
      have hsq : ‖z‖ ^ 2 ≤ C * ‖z‖ * ‖T z‖ := calc
        ‖z‖ ^ 2 = (inner ℂ z z).re :=
          (inner_self_eq_norm_sq (𝕜 := ℂ) z).symm
        _ = (inner ℂ u (T z)).re := congrArg Complex.re hinner
        _ ≤ ‖inner ℂ u (T z)‖ := Complex.re_le_norm _
        _ ≤ ‖u‖ * ‖T z‖ := norm_inner_le_norm u (T z)
        _ ≤ (C * ‖z‖) * ‖T z‖ :=
          mul_le_mul_of_nonneg_right hnu (norm_nonneg _)
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      change ‖z‖ ≤ C * ‖T z‖
      nlinarith
  · rintro ⟨K, hanti⟩
    have hclosed : IsClosed (Set.range T) := hanti.isClosed_range T.uniformContinuous
    have hTsurj : Function.Surjective T := by
      intro y
      have hy : y ∈ closure (Set.range T) := by
        rw [hdense.closure_eq]
        trivial
      rwa [hclosed.closure_eq] at hy
    let e : G ≃L[ℂ] H₁ := ContinuousLinearEquiv.ofBijective T
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hTsurj)
    intro z
    let S : H₁ →L[ℂ] G := (e.symm : H₁ →L[ℂ] G)
    refine ⟨S.adjoint z, ?_⟩
    apply ext_inner_right ℂ
    intro x
    rw [T.adjoint_inner_left, S.adjoint_inner_left]
    change inner ℂ z (e.symm (T x)) = inner ℂ z x
    rw [show T x = e x by rfl, e.symm_apply_apply]

theorem adjoint_injective_of_denseRange (T : G →L[ℂ] H₁) (hdense : DenseRange T) :
    Function.Injective T.adjoint := by
  intro x y hxy
  refine hdense.eq_of_inner_right ℂ ?_
  intro i
  calc
    inner ℂ (T i) x = starRingEnd ℂ (inner ℂ x (T i)) := by rw [inner_conj_symm]
    _ = starRingEnd ℂ (inner ℂ (T.adjoint x) i) := by rw [T.adjoint_inner_left]
    _ = starRingEnd ℂ (inner ℂ (T.adjoint y) i) := by rw [hxy]
    _ = starRingEnd ℂ (inner ℂ y (T i)) := by rw [T.adjoint_inner_left]
    _ = inner ℂ (T i) y := by rw [inner_conj_symm]

/-- Image of a hyperplane is dense when its normal misses the adjoint range. -/
theorem dense_image_orthogonal_hyperplane
    (T : G →L[ℂ] H₁) (hdense : DenseRange T) (v : G)
    (hv : v ∉ LinearMap.range T.adjoint.toLinearMap) :
    Dense (((ℂ ∙ v)ᗮ).map T.toLinearMap : Set H₁) := by
  have horth : (((ℂ ∙ v)ᗮ).map T.toLinearMap)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hTy : T.adjoint y ∈ ((ℂ ∙ v)ᗮ)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro m hm
      calc
        inner ℂ m (T.adjoint y) = starRingEnd ℂ (inner ℂ (T.adjoint y) m) := by
          rw [inner_conj_symm]
        _ = starRingEnd ℂ (inner ℂ y (T m)) := by rw [T.adjoint_inner_left]
        _ = inner ℂ (T m) y := by rw [inner_conj_symm]
        _ = 0 := hy (T m) ⟨m, hm, rfl⟩
    rw [Submodule.orthogonal_orthogonal_eq_closure,
      (ℂ ∙ v).closed_of_finiteDimensional.submodule_topologicalClosure_eq,
      Submodule.mem_span_singleton] at hTy
    rcases hTy with ⟨a, ha⟩
    by_cases ha0 : a = 0
    · rw [ha0, zero_smul] at ha
      apply adjoint_injective_of_denseRange T hdense
      simpa using ha.symm
    · exfalso
      apply hv
      refine ⟨a⁻¹ • y, ?_⟩
      rw [map_smul]
      calc
        a⁻¹ • T.adjoint y = a⁻¹ • (a • v) := congrArg (a⁻¹ • ·) ha.symm
        _ = v := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  simpa using horth

/-- Two coordinate projections are simultaneously singular when neither is uniformly bounded
below. For a closed operator graph these are exactly: operator unbounded and not bounded below. -/
def IsTwoSidedSingular (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂) : Prop :=
  (¬ ∃ K : NNReal, AntilipschitzWith K P) ∧
    (¬ ∃ K : NNReal, AntilipschitzWith K Q)

def HasProperClosedBiDenseSubspace (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂) : Prop :=
  ∃ M : Submodule ℂ G, IsClosed (M : Set G) ∧ M ≠ ⊤ ∧
    Dense (M.map P.toLinearMap : Set H₁) ∧
    Dense (M.map Q.toLinearMap : Set H₂)

theorem exists_biDense_hyperplane_of_twoSidedSingular
    (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂)
    (hPinj : Function.Injective P) (hQinj : Function.Injective Q)
    (hPdense : DenseRange P) (hQdense : DenseRange Q)
    (hsing : IsTwoSidedSingular P Q) :
    ∃ v : G, v ≠ 0 ∧
      Dense (((ℂ ∙ v)ᗮ).map P.toLinearMap : Set H₁) ∧
      Dense (((ℂ ∙ v)ᗮ).map Q.toLinearMap : Set H₂) := by
  have hPns : ¬ Function.Surjective P.adjoint := by
    intro h
    exact hsing.1 ((adjoint_surjective_iff_antilipschitz P hPinj hPdense).mp h)
  have hQns : ¬ Function.Surjective Q.adjoint := by
    intro h
    exact hsing.2 ((adjoint_surjective_iff_antilipschitz Q hQinj hQdense).mp h)
  have hPrange : LinearMap.range P.adjoint.toLinearMap ≠ ⊤ := by
    intro hrange
    apply hPns
    exact LinearMap.range_eq_top.mp hrange
  have hQrange : LinearMap.range Q.adjoint.toLinearMap ≠ ⊤ := by
    intro hrange
    apply hQns
    exact LinearMap.range_eq_top.mp hrange
  obtain ⟨x, _hxtop, hxP⟩ :=
    SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hPrange)
  obtain ⟨y, _hytop, hyQ⟩ :=
    SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hQrange)
  by_cases hxQ : x ∈ LinearMap.range Q.adjoint.toLinearMap
  · by_cases hyP : y ∈ LinearMap.range P.adjoint.toLinearMap
    · let v := x + y
      have hvP : v ∉ LinearMap.range P.adjoint.toLinearMap := by
        intro hv
        exact hxP (show x ∈ LinearMap.range P.adjoint.toLinearMap from by
          rw [show x = v - y by simp [v]]
          exact Submodule.sub_mem _ hv hyP)
      have hvQ : v ∉ LinearMap.range Q.adjoint.toLinearMap := by
        intro hv
        exact hyQ (show y ∈ LinearMap.range Q.adjoint.toLinearMap from by
          rw [show y = v - x by simp [v]]
          exact Submodule.sub_mem _ hv hxQ)
      have hv0 : v ≠ 0 := by
        intro hvzero
        exact hvP (hvzero ▸ Submodule.zero_mem _)
      exact ⟨v, hv0, dense_image_orthogonal_hyperplane P hPdense v hvP,
        dense_image_orthogonal_hyperplane Q hQdense v hvQ⟩
    · have hy0 : y ≠ 0 := by
        intro hyzero
        exact hyP (hyzero ▸ Submodule.zero_mem _)
      exact ⟨y, hy0, dense_image_orthogonal_hyperplane P hPdense y hyP,
        dense_image_orthogonal_hyperplane Q hQdense y hyQ⟩
  · have hx0 : x ≠ 0 := by
      intro hxzero
      exact hxP (hxzero ▸ Submodule.zero_mem _)
    exact ⟨x, hx0, dense_image_orthogonal_hyperplane P hPdense x hxP,
      dense_image_orthogonal_hyperplane Q hQdense x hxQ⟩

omit [CompleteSpace H₁] in
theorem closed_biDense_eq_top_of_antilipschitz
    (T : G →L[ℂ] H₁) (hinj : Function.Injective T)
    (M : Submodule ℂ G) (hMclosed : IsClosed (M : Set G))
    (hMdense : Dense (M.map T.toLinearMap : Set H₁))
    {K : NNReal} (hanti : AntilipschitzWith K T) : M = ⊤ := by
  let TM : M →L[ℂ] H₁ := T.comp M.subtypeL
  have hantiM : AntilipschitzWith K TM := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    rw [Subtype.dist_eq]
    simpa [TM] using hanti.le_mul_dist (x : G) (y : G)
  have hclosed : IsClosed (Set.range TM) := hantiM.isClosed_range TM.uniformContinuous
  have hdenseTM : DenseRange TM := by
    have hset : (M.map T.toLinearMap : Set H₁) = Set.range TM := by
      ext y
      simp [TM]
    change Dense (Set.range TM)
    rw [← hset]
    exact hMdense
  have hsurj : Function.Surjective TM := by
    intro y
    have hy : y ∈ closure (Set.range TM) := by
      rw [hdenseTM.closure_eq]
      trivial
    rwa [hclosed.closure_eq] at hy
  rw [eq_top_iff]
  intro x _hx
  obtain ⟨m, hm⟩ := hsurj (T x)
  have hmx : (m : G) = x := hinj hm
  exact hmx ▸ m.property

/-- Sharp criterion: a proper closed bi-dense graph defect exists iff both coordinate projections
are singular. The forward construction is a codimension-one orthogonal hyperplane. -/
theorem twoSidedSingular_iff_hasProperClosedBiDenseSubspace
    (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂)
    (hPinj : Function.Injective P) (hQinj : Function.Injective Q)
    (hPdense : DenseRange P) (hQdense : DenseRange Q) :
    IsTwoSidedSingular P Q ↔ HasProperClosedBiDenseSubspace P Q := by
  constructor
  · intro hsing
    obtain ⟨v, hv0, hPv, hQv⟩ :=
      exists_biDense_hyperplane_of_twoSidedSingular P Q hPinj hQinj hPdense hQdense hsing
    refine ⟨(ℂ ∙ v)ᗮ, (ℂ ∙ v).isClosed_orthogonal, ?_, hPv, hQv⟩
    intro htop
    have hvorth : v ∈ (ℂ ∙ v)ᗮ := htop ▸ Submodule.mem_top
    have hzero := hvorth v (Submodule.mem_span_singleton_self v)
    exact hv0 (inner_self_eq_zero.mp hzero)
  · rintro ⟨M, hMclosed, hMproper, hPMdense, hQMdense⟩
    constructor
    · rintro ⟨K, hK⟩
      exact hMproper (closed_biDense_eq_top_of_antilipschitz P hPinj M hMclosed hPMdense hK)
    · rintro ⟨K, hK⟩
      exact hMproper (closed_biDense_eq_top_of_antilipschitz Q hQinj M hMclosed hQMdense hK)

end SharpTwoSidedCriterion

end RHTower
