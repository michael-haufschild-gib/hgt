import GaloisForLFunctions.RHTower.PreQuasiGelfandTwoSidedSingularDefect

/-!
# Pythagorean observer blindness

This module formalizes the Hilbert-space core of observer--annihilator duality:
for a dense-range bounded observer `T`, the image of the orthogonal defect
`Dᗮ` is dense exactly when the closed normal space `D` misses
`range T.adjoint`.

It also constructs an explicit stable pair of injective dense-range diagonal
observers.  Their common blind normal space misses both adjoint ranges yet
contains a countably infinite linearly independent family.  Thus simultaneous
dense observability is compatible with infinite-codimensional closed defects;
the earlier codimension-one witness is not the endpoint phenomenon.
-/

open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {G H : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem dense_image_orthogonal_iff_inf_adjointRange_eq_bot
    (T : G →L[ℂ] H) (hdense : DenseRange T)
    (D : Submodule ℂ G) (hDclosed : IsClosed (D : Set G)) :
    Dense (Dᗮ.map T.toLinearMap : Set H) ↔
      D ⊓ LinearMap.range T.adjoint.toLinearMap = ⊥ := by
  constructor
  · intro himage
    rw [Submodule.eq_bot_iff]
    intro z hz
    rcases hz.2 with ⟨y, hy⟩
    have hyzero : y = 0 := by
      apply himage.eq_of_inner_left ℂ
      rintro _ ⟨m, hm, rfl⟩
      have hzD : z ∈ (Dᗮ)ᗮ := by
        rw [Submodule.orthogonal_orthogonal_eq_closure,
          hDclosed.submodule_topologicalClosure_eq]
        exact hz.1
      calc
        inner ℂ y (T m) = inner ℂ (T.adjoint y) m :=
          (T.adjoint_inner_left m y).symm
        _ = inner ℂ z m := congrArg (fun w : G => inner ℂ w m) hy
        _ = starRingEnd ℂ (inner ℂ m z) := by rw [inner_conj_symm]
        _ = 0 := by rw [hzD m hm, map_zero]
        _ = inner ℂ 0 (T m) := by simp
    calc
      z = T.adjoint y := hy.symm
      _ = 0 := by rw [hyzero, map_zero]
  · intro hinter
    have horth : (Dᗮ.map T.toLinearMap)ᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      have hTy : T.adjoint y ∈ D := by
        rw [← hDclosed.submodule_topologicalClosure_eq,
          ← Submodule.orthogonal_orthogonal_eq_closure]
        rw [Submodule.mem_orthogonal]
        intro m hm
        calc
          inner ℂ m (T.adjoint y) = starRingEnd ℂ (inner ℂ (T.adjoint y) m) := by
            rw [inner_conj_symm]
          _ = starRingEnd ℂ (inner ℂ y (T m)) := by rw [T.adjoint_inner_left]
          _ = inner ℂ (T m) y := by rw [inner_conj_symm]
          _ = 0 := hy (T m) ⟨m, hm, rfl⟩
      have hTrange : T.adjoint y ∈ LinearMap.range T.adjoint.toLinearMap := ⟨y, rfl⟩
      have hTzero : T.adjoint y = 0 := by
        have hmem : T.adjoint y ∈
            D ⊓ LinearMap.range T.adjoint.toLinearMap := ⟨hTy, hTrange⟩
        rw [hinter] at hmem
        exact hmem
      apply adjoint_injective_of_denseRange T hdense
      simpa using hTzero
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    apply Submodule.orthogonal_eq_bot_iff.mp
    simpa using horth

abbrev PQWildIndex := Bool × (ℕ × ℕ)
abbrev PQWildHilbert := DiagonalL2 PQWildIndex

def pqWildPWeight : PQWildIndex → ℝ
  | (false, (_, n)) => pqInv n
  | (true, _) => 1

def pqWildQWeight : PQWildIndex → ℝ
  | (false, _) => 1
  | (true, (_, n)) => pqInv n

theorem pqWildPWeight_norm_le_one (q : PQWildIndex) :
    ‖(pqWildPWeight q : ℂ)‖ ≤ 1 := by
  rcases q with ⟨b, k, n⟩
  cases b <;> simp [pqWildPWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pqInv_pos n).le, pqInv_le_one]

theorem pqWildQWeight_norm_le_one (q : PQWildIndex) :
    ‖(pqWildQWeight q : ℂ)‖ ≤ 1 := by
  rcases q with ⟨b, k, n⟩
  cases b <;> simp [pqWildQWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pqInv_pos n).le, pqInv_le_one]

theorem pqWild_memℓp_diagonal {lam : PQWildIndex → ℂ} {C : ℝ}
    (hC : ∀ q, ‖lam q‖ ≤ C) (f : PQWildHilbert) :
    Memℓp (fun q => lam q * f q) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun q => ‖f q‖ ^ (2 : ℝ) :=
    (lp.memℓp f).summable (by norm_num)
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC (false, (0, 0)))
  refine Summable.of_nonneg_of_le
    (fun q => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (C ^ (2 : ℝ)))
  intro q
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) (hC q) (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) 2)

def pqWildDiagonalLinearMap (lam : PQWildIndex → ℂ) {C : ℝ}
    (hC : ∀ q, ‖lam q‖ ≤ C) : PQWildHilbert →ₗ[ℂ] PQWildHilbert where
  toFun f := ⟨fun q => lam q * f q, pqWild_memℓp_diagonal hC f⟩
  map_add' := by
    intro f g
    ext q
    simp [mul_add]
  map_smul' := by
    intro c f
    ext q
    simp [mul_left_comm]

@[simp] theorem pqWildDiagonalLinearMap_apply (lam : PQWildIndex → ℂ) {C : ℝ}
    (hC : ∀ q, ‖lam q‖ ≤ C) (f : PQWildHilbert) (q : PQWildIndex) :
    pqWildDiagonalLinearMap lam hC f q = lam q * f q := rfl

theorem norm_pqWildDiagonalLinearMap_le (lam : PQWildIndex → ℂ) {C : ℝ}
    (hC : ∀ q, ‖lam q‖ ≤ C) (f : PQWildHilbert) :
    ‖pqWildDiagonalLinearMap lam hC f‖ ≤ C * ‖f‖ := by
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC (false, (0, 0)))
  have hnn : (0 : ℝ) ≤ ‖pqWildDiagonalLinearMap lam hC f‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ C * ‖f‖ := mul_nonneg hCnn (norm_nonneg _)
  have htsumD : ‖pqWildDiagonalLinearMap lam hC f‖ ^ (2 : ℝ) =
      ∑' q, ‖(pqWildDiagonalLinearMap lam hC f) q‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : PQWildIndex => ℂ)
      (by norm_num) (pqWildDiagonalLinearMap lam hC f)
  have htsumf : ‖f‖ ^ (2 : ℝ) = ∑' q, ‖f q‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : PQWildIndex => ℂ)
      (by norm_num) f
  have hsumf : Summable fun q => ‖f q‖ ^ (2 : ℝ) :=
    (lp.memℓp f).summable (by norm_num)
  have hsumD : Summable fun q =>
      ‖(pqWildDiagonalLinearMap lam hC f) q‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ q, ‖(pqWildDiagonalLinearMap lam hC f) q‖ ^ (2 : ℝ) ≤
      C ^ (2 : ℝ) * ‖f q‖ ^ (2 : ℝ) := by
    intro q
    rw [pqWildDiagonalLinearMap_apply, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (hC q) (by norm_num))
      (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow : ‖pqWildDiagonalLinearMap lam hC f‖ ^ (2 : ℝ) ≤
      (C * ‖f‖) ^ (2 : ℝ) := by
    rw [htsumD, Real.mul_rpow hCnn (norm_nonneg _), htsumf, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumD
      (hsumf.mul_left (C ^ (2 : ℝ)))
  have hx2 : ‖pqWildDiagonalLinearMap lam hC f‖ ^ (2 : ℝ) =
      ‖pqWildDiagonalLinearMap lam hC f‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hy2 : (C * ‖f‖) ^ (2 : ℝ) = (C * ‖f‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs] at hs

def pqWildDiagonalOperator (lam : PQWildIndex → ℂ) {C : ℝ}
    (hC : ∀ q, ‖lam q‖ ≤ C) : PQWildHilbert →L[ℂ] PQWildHilbert :=
  LinearMap.mkContinuous (pqWildDiagonalLinearMap lam hC) C
    (norm_pqWildDiagonalLinearMap_le lam hC)

@[simp] theorem pqWildDiagonalOperator_apply (lam : PQWildIndex → ℂ) {C : ℝ}
    (hC : ∀ q, ‖lam q‖ ≤ C) (f : PQWildHilbert) (q : PQWildIndex) :
    pqWildDiagonalOperator lam hC f q = lam q * f q := rfl

def pqWildP : PQWildHilbert →L[ℂ] PQWildHilbert :=
  pqWildDiagonalOperator (fun q => (pqWildPWeight q : ℂ))
    pqWildPWeight_norm_le_one

def pqWildQ : PQWildHilbert →L[ℂ] PQWildHilbert :=
  pqWildDiagonalOperator (fun q => (pqWildQWeight q : ℂ))
    pqWildQWeight_norm_le_one

@[simp] theorem pqWildP_apply (x : PQWildHilbert) (q : PQWildIndex) :
    pqWildP x q = (pqWildPWeight q : ℂ) * x q := rfl

@[simp] theorem pqWildQ_apply (x : PQWildHilbert) (q : PQWildIndex) :
    pqWildQ x q = (pqWildQWeight q : ℂ) * x q := rfl

theorem pqWildPWeight_ne_zero (q : PQWildIndex) : (pqWildPWeight q : ℂ) ≠ 0 := by
  rcases q with ⟨b, k, n⟩
  cases b
  · exact_mod_cast (pqInv_pos n).ne'
  · simp [pqWildPWeight]

theorem pqWildQWeight_ne_zero (q : PQWildIndex) : (pqWildQWeight q : ℂ) ≠ 0 := by
  rcases q with ⟨b, k, n⟩
  cases b
  · simp [pqWildQWeight]
  · exact_mod_cast (pqInv_pos n).ne'

theorem pqWildP_injective : Function.Injective pqWildP := by
  intro x y hxy
  ext q
  have hq := congrArg (fun z : PQWildHilbert => z q) hxy
  simp only [pqWildP_apply] at hq
  exact mul_left_cancel₀ (pqWildPWeight_ne_zero q) hq

theorem pqWildQ_injective : Function.Injective pqWildQ := by
  intro x y hxy
  ext q
  have hq := congrArg (fun z : PQWildHilbert => z q) hxy
  simp only [pqWildQ_apply] at hq
  exact mul_left_cancel₀ (pqWildQWeight_ne_zero q) hq

theorem pqWildP_denseRange : DenseRange pqWildP := by
  have hle : Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis PQWildIndex)) ≤
      LinearMap.range pqWildP.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    rw [HilbertSchmidt.lpBasis_apply]
    refine ⟨((pqWildPWeight q : ℂ)⁻¹ • lp.single 2 q 1 : PQWildHilbert), ?_⟩
    ext r
    change (pqWildPWeight r : ℂ) *
      (((pqWildPWeight q : ℂ)⁻¹ • lp.single 2 q 1 : PQWildHilbert) r) =
        (lp.single 2 q 1 : PQWildHilbert) r
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hr : r = q
    · subst r
      simp [lp.single_apply, mul_inv_cancel₀ (pqWildPWeight_ne_zero q)]
    · simp [lp.single_apply, hr]
  apply (Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (HilbertSchmidt.lpBasis PQWildIndex).dense_span).mono
  intro x hx
  rcases hle hx with ⟨y, hy⟩
  exact ⟨y, hy⟩

theorem pqWildQ_denseRange : DenseRange pqWildQ := by
  have hle : Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis PQWildIndex)) ≤
      LinearMap.range pqWildQ.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    rw [HilbertSchmidt.lpBasis_apply]
    refine ⟨((pqWildQWeight q : ℂ)⁻¹ • lp.single 2 q 1 : PQWildHilbert), ?_⟩
    ext r
    change (pqWildQWeight r : ℂ) *
      (((pqWildQWeight q : ℂ)⁻¹ • lp.single 2 q 1 : PQWildHilbert) r) =
        (lp.single 2 q 1 : PQWildHilbert) r
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hr : r = q
    · subst r
      simp [lp.single_apply, mul_inv_cancel₀ (pqWildQWeight_ne_zero q)]
    · simp [lp.single_apply, hr]
  apply (Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (HilbertSchmidt.lpBasis PQWildIndex).dense_span).mono
  intro x hx
  rcases hle hx with ⟨y, hy⟩
  exact ⟨y, hy⟩

theorem pqWildP_inner (x y : PQWildHilbert) :
    inner ℂ (pqWildP x) y = inner ℂ x (pqWildP y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  rw [pqWildP_apply, pqWildP_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem pqWildQ_inner (x y : PQWildHilbert) :
    inner ℂ (pqWildQ x) y = inner ℂ x (pqWildQ y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  rw [pqWildQ_apply, pqWildQ_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem pqWildP_adjoint : pqWildP.adjoint = pqWildP := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  exact pqWildP_inner

theorem pqWildQ_adjoint : pqWildQ.adjoint = pqWildQ := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  exact pqWildQ_inner

def pqWildEval (q : PQWildIndex) : PQWildHilbert →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun x => by simpa using lp.norm_apply_le_norm (by norm_num) x q)

@[simp] theorem pqWildEval_apply (q : PQWildIndex) (x : PQWildHilbert) :
    pqWildEval q x = x q := rfl

def pqWildNormalSubspace : Submodule ℂ PQWildHilbert :=
  ⨅ b : Bool, ⨅ k : ℕ, ⨅ n : ℕ,
    (pqWildEval (b, (k, n)) -
      (pqInv n : ℂ) • pqWildEval (false, (k, 0))).ker

theorem mem_pqWildNormalSubspace_iff (x : PQWildHilbert) :
    x ∈ pqWildNormalSubspace ↔
      ∀ b k n, x (b, (k, n)) = (pqInv n : ℂ) * x (false, (k, 0)) := by
  rw [pqWildNormalSubspace]
  simp only [Submodule.mem_iInf]
  constructor
  · intro h b k n
    have h' := h b k n
    change (pqWildEval (b, (k, n)) -
      (pqInv n : ℂ) • pqWildEval (false, (k, 0))) x = 0 at h'
    simpa [sub_eq_zero] using h'
  · intro h b k n
    change (pqWildEval (b, (k, n)) -
      (pqInv n : ℂ) • pqWildEval (false, (k, 0))) x = 0
    simpa [sub_eq_zero] using h b k n

theorem pqWildNormalSubspace_isClosed :
    IsClosed (pqWildNormalSubspace : Set PQWildHilbert) := by
  have heq : (pqWildNormalSubspace : Set PQWildHilbert) =
      ⋂ b : Bool, ⋂ k : ℕ, ⋂ n : ℕ,
        ((pqWildEval (b, (k, n)) -
          (pqInv n : ℂ) • pqWildEval (false, (k, 0))).ker : Set PQWildHilbert) := by
    ext x
    change x ∈ pqWildNormalSubspace ↔ x ∈
      ⋂ b : Bool, ⋂ k : ℕ, ⋂ n : ℕ,
        ((pqWildEval (b, (k, n)) -
          (pqInv n : ℂ) • pqWildEval (false, (k, 0))).ker : Set PQWildHilbert)
    rw [mem_pqWildNormalSubspace_iff]
    simp only [Set.mem_iInter]
    constructor
    · intro h b k n
      change (pqWildEval (b, (k, n)) -
        (pqInv n : ℂ) • pqWildEval (false, (k, 0))) x = 0
      simpa [sub_eq_zero] using h b k n
    · intro h b k n
      have h' := h b k n
      change (pqWildEval (b, (k, n)) -
        (pqInv n : ℂ) • pqWildEval (false, (k, 0))) x = 0 at h'
      simpa [sub_eq_zero] using h'
  rw [heq]
  exact isClosed_iInter fun b => isClosed_iInter fun k => isClosed_iInter fun n =>
    (pqWildEval (b, (k, n)) -
      (pqInv n : ℂ) • pqWildEval (false, (k, 0))).isClosed_ker

theorem pqWildNormalSubspace_inf_range_pqWildP_eq_bot :
    pqWildNormalSubspace ⊓ LinearMap.range pqWildP.toLinearMap = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rcases hx.2 with ⟨y, hy⟩
  have hxD := (mem_pqWildNormalSubspace_iff x).mp hx.1
  have hcoeff : ∀ k : ℕ, x (false, (k, 0)) = 0 := by
    intro k
    by_contra hk
    have hyconst : ∀ n : ℕ, y (false, (k, n)) = x (false, (k, 0)) := by
      intro n
      have hn := congrArg (fun z : PQWildHilbert => z (false, (k, n))) hy
      change (pqInv n : ℂ) * y (false, (k, n)) = x (false, (k, n)) at hn
      rw [hxD false k n] at hn
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (pqInv_pos n).ne') hn
    have hs := (HilbertSchmidt.summable_coe_sq y).comp_injective
      (i := fun n : ℕ => (false, (k, n))) (by
        intro i j h
        exact congrArg (fun q : PQWildIndex => q.2.2) h)
    have hsconst : Summable (fun _n : ℕ => ‖x (false, (k, 0))‖ ^ 2) := by
      refine hs.congr fun n => ?_
      change ‖y (false, (k, n))‖ ^ 2 = ‖x (false, (k, 0))‖ ^ 2
      rw [hyconst n]
    exact Set.infinite_univ (Set.Finite.of_summable_const
      (pow_pos (norm_pos_iff.mpr hk) 2) hsconst)
  ext q
  rcases q with ⟨b, k, n⟩
  rw [hxD b k n, hcoeff k, mul_zero]
  rfl

theorem pqWildNormalSubspace_inf_range_pqWildQ_eq_bot :
    pqWildNormalSubspace ⊓ LinearMap.range pqWildQ.toLinearMap = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rcases hx.2 with ⟨y, hy⟩
  have hxD := (mem_pqWildNormalSubspace_iff x).mp hx.1
  have hcoeff : ∀ k : ℕ, x (false, (k, 0)) = 0 := by
    intro k
    by_contra hk
    have hyconst : ∀ n : ℕ, y (true, (k, n)) = x (false, (k, 0)) := by
      intro n
      have hn := congrArg (fun z : PQWildHilbert => z (true, (k, n))) hy
      change (pqInv n : ℂ) * y (true, (k, n)) = x (true, (k, n)) at hn
      rw [hxD true k n] at hn
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (pqInv_pos n).ne') hn
    have hs := (HilbertSchmidt.summable_coe_sq y).comp_injective
      (i := fun n : ℕ => (true, (k, n))) (by
        intro i j h
        exact congrArg (fun q : PQWildIndex => q.2.2) h)
    have hsconst : Summable (fun _n : ℕ => ‖x (false, (k, 0))‖ ^ 2) := by
      refine hs.congr fun n => ?_
      change ‖y (true, (k, n))‖ ^ 2 = ‖x (false, (k, 0))‖ ^ 2
      rw [hyconst n]
    exact Set.infinite_univ (Set.Finite.of_summable_const
      (pow_pos (norm_pos_iff.mpr hk) 2) hsconst)
  ext q
  rcases q with ⟨b, k, n⟩
  rw [hxD b k n, hcoeff k, mul_zero]
  rfl

def pqWildBlindDefect : Submodule ℂ PQWildHilbert := pqWildNormalSubspaceᗮ

theorem pqWildBlindDefect_p_dense :
    Dense (pqWildBlindDefect.map pqWildP.toLinearMap : Set PQWildHilbert) := by
  apply (dense_image_orthogonal_iff_inf_adjointRange_eq_bot pqWildP
    pqWildP_denseRange pqWildNormalSubspace pqWildNormalSubspace_isClosed).mpr
  rw [pqWildP_adjoint]
  exact pqWildNormalSubspace_inf_range_pqWildP_eq_bot

theorem pqWildBlindDefect_q_dense :
    Dense (pqWildBlindDefect.map pqWildQ.toLinearMap : Set PQWildHilbert) := by
  apply (dense_image_orthogonal_iff_inf_adjointRange_eq_bot pqWildQ
    pqWildQ_denseRange pqWildNormalSubspace pqWildNormalSubspace_isClosed).mpr
  rw [pqWildQ_adjoint]
  exact pqWildNormalSubspace_inf_range_pqWildQ_eq_bot

def pqWildNormalWeight (k : ℕ) : PQWildIndex → ℂ
  | (_, (j, n)) => if j = k then (pqInv n : ℂ) else 0

theorem pqWildNormalWeight_summable_sq (k : ℕ) :
    Summable (fun q : PQWildIndex => ‖pqWildNormalWeight k q‖ ^ 2) := by
  have hbase : Summable (fun n : ℕ => ‖(pqInv n : ℂ)‖ ^ 2) := by
    have hsplit :=
      (summable_prod_of_nonneg (fun q : PQIndex => sq_nonneg ‖pqVWeight q‖)).mp
        pqVWeight_summable_sq
    exact (hsplit.1 false).congr fun n => by simp [pqVWeight]
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · intro _
    rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
    constructor
    · intro j
      by_cases hj : j = k
      · subst j
        exact hbase.congr fun n => by simp [pqWildNormalWeight]
      · simp [pqWildNormalWeight, hj]
    · apply summable_of_ne_finset_zero (s := {k})
      intro j hj
      have hjk : j ≠ k := by simpa using hj
      simp [pqWildNormalWeight, hjk]
  · exact Summable.of_finite

def pqWildNormalVector (k : ℕ) : PQWildHilbert :=
  ⟨pqWildNormalWeight k, HilbertSchmidt.memℓp_of_sq (pqWildNormalWeight_summable_sq k)⟩

@[simp] theorem pqWildNormalVector_apply (k : ℕ) (b : Bool) (j n : ℕ) :
    pqWildNormalVector k (b, (j, n)) =
      if j = k then (pqInv n : ℂ) else 0 := rfl

theorem pqWildNormalVector_mem (k : ℕ) :
    pqWildNormalVector k ∈ pqWildNormalSubspace := by
  rw [mem_pqWildNormalSubspace_iff]
  intro b j n
  by_cases hj : j = k
  · subst j
    simp [pqInv]
  · simp [pqWildNormalVector_apply, hj]

def pqWildNormalVectorSub (k : ℕ) : pqWildNormalSubspace :=
  ⟨pqWildNormalVector k, pqWildNormalVector_mem k⟩

@[simp] theorem pqWildNormalVectorSub_apply (k : ℕ) (b : Bool) (j n : ℕ) :
    (pqWildNormalVectorSub k : PQWildHilbert) (b, (j, n)) =
      if j = k then (pqInv n : ℂ) else 0 := rfl

def pqWildNormalCoordinate (k : ℕ) : pqWildNormalSubspace →ₗ[ℂ] ℂ :=
  (pqWildEval (false, (k, 0))).toLinearMap.comp pqWildNormalSubspace.subtype

@[simp] theorem pqWildNormalCoordinate_apply (k : ℕ) (x : pqWildNormalSubspace) :
    pqWildNormalCoordinate k x = (x : PQWildHilbert) (false, (k, 0)) := rfl

theorem pqWildNormalVectorSub_linearIndependent :
    LinearIndependent ℂ pqWildNormalVectorSub := by
  rw [linearIndependent_iff]
  intro l hl
  apply Finsupp.ext
  intro k
  have hk := congrArg (pqWildNormalCoordinate k) hl
  rw [Finsupp.apply_linearCombination] at hk
  simpa [Finsupp.linearCombination_apply, pqWildNormalCoordinate,
    pqWildNormalVectorSub, pqWildNormalVector, pqWildNormalWeight, pqInv,
    Finsupp.sum] using hk

theorem pqWildNormalSubspace_has_countable_independent_family :
    ∃ v : ℕ → pqWildNormalSubspace, LinearIndependent ℂ v :=
  ⟨pqWildNormalVectorSub, pqWildNormalVectorSub_linearIndependent⟩

end RHTower

