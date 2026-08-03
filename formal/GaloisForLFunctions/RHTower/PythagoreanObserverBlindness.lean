import GaloisForLFunctions.RHTower.PreQuasiGelfandTwoSidedSingularDefect

/-!
# Countable observer blindness and annihilator weaving

This module formalizes the Hilbert-space core of observer--annihilator duality:
for a dense-range bounded observer `T`, the image of the orthogonal defect
`Dᗮ` is dense exactly when the closed normal space `D` misses
`range T.adjoint`.

It constructs an explicit diagonal model and proves finite- and countable-family
laws.  For every countable family of non-coercive injective dense-range
Hilbert observers, a closed common normal space misses every adjoint range,
contains a countably infinite linearly independent family, and transfers every
closed subspace below it to a simultaneous dense-image orthogonal defect.  If
one observer is coercive, every closed simultaneous dense-image defect is the
whole source.  No stability, commutation, self-adjointness, or spectral
hypothesis is used.
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

theorem dense_image_iff_orthogonal_inf_adjointRange_eq_bot
    (T : G →L[ℂ] H) (hdense : DenseRange T)
    (M : Submodule ℂ G) (hMclosed : IsClosed (M : Set G)) :
    Dense (M.map T.toLinearMap : Set H) ↔
      Mᗮ ⊓ LinearMap.range T.adjoint.toLinearMap = ⊥ := by
  have h := dense_image_orthogonal_iff_inf_adjointRange_eq_bot
    T hdense Mᗮ M.isClosed_orthogonal
  rw [Submodule.orthogonal_orthogonal_eq_closure,
    hMclosed.submodule_topologicalClosure_eq] at h
  exact h

theorem dense_images_iff_orthogonal_avoids_adjointRanges
    {I : Type*} {F : I → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
    [∀ i, CompleteSpace (F i)]
    (T : ∀ i, G →L[ℂ] F i) (hdense : ∀ i, DenseRange (T i))
    (M : Submodule ℂ G) (hMclosed : IsClosed (M : Set G)) :
    (∀ i, Dense (M.map (T i).toLinearMap : Set (F i))) ↔
      ∀ i, Mᗮ ⊓ LinearMap.range (T i).adjoint.toLinearMap = ⊥ := by
  exact forall_congr' fun i =>
    dense_image_iff_orthogonal_inf_adjointRange_eq_bot
      (T i) (hdense i) M hMclosed

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

def HilbertRangeSingular (T : G →L[ℂ] H) : Prop :=
  ¬ IsClosed (Set.range T)

noncomputable def dependentSeqAux {α : Type*} [DecidableEq α]
    (P : ℕ → α → Prop) (r : α → α → Prop)
    (h : ∀ n (s : Finset α), ∃ y, P n y ∧ ∀ x ∈ s, r x y) : ℕ → α
  | n => Classical.choose
      (h n (Finset.image (fun i : Fin n => dependentSeqAux P r h i)
        (Finset.univ : Finset (Fin n))))

theorem exists_seq_dependent_pairwise {α : Type*}
    (P : ℕ → α → Prop) (r : α → α → Prop) [Std.Symm r]
    (h : ∀ n (s : Finset α), ∃ y, P n y ∧ ∀ x ∈ s, r x y) :
    ∃ f : ℕ → α, (∀ n, P n (f n)) ∧
      Pairwise (fun m n => r (f m) (f n)) := by
  classical
  haveI : Nonempty α := by
    rcases h 0 ∅ with ⟨y, -⟩
    exact ⟨y⟩
  set f := dependentSeqAux P r h with hf
  have hP : ∀ n, P n (f n) := by
    intro n
    rw [hf, dependentSeqAux]
    exact (Classical.choose_spec
      (h n (Finset.image (fun i : Fin n => dependentSeqAux P r h i)
        (Finset.univ : Finset (Fin n))))).1
  have hlt : ∀ m n, m < n → r (f m) (f n) := by
    intro m n hmn
    conv_rhs => rw [hf]
    rw [dependentSeqAux]
    apply (Classical.choose_spec
      (h n (Finset.image (fun i : Fin n => dependentSeqAux P r h i)
        (Finset.univ : Finset (Fin n))))).2
    exact Finset.mem_image.2 ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩
  refine ⟨f, hP, fun m n hmn => ?_⟩
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt m n h
  · exact symm (hlt n m h)

omit [CompleteSpace H] in
theorem exists_unit_norm_map_lt_of_hilbertRangeSingular
    (T : G →L[ℂ] H) (hT : HilbertRangeSingular T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : G, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  by_contra hno
  push Not at hno
  have hlower : ∀ x : G, ε * ‖x‖ ≤ ‖T x‖ := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    · let z : G := (‖x‖ : ℂ)⁻¹ • x
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hz : ‖z‖ = 1 := by
        simp [z, norm_smul, Complex.norm_real, hxpos.ne']
      have hsmall := hno z hz
      have hTz : ‖T z‖ = ‖T x‖ / ‖x‖ := by
        simp [z, norm_smul, Complex.norm_real, div_eq_mul_inv, mul_comm]
      rw [hTz] at hsmall
      exact (le_div_iff₀ hxpos).mp hsmall
  have hanti : AntilipschitzWith (Real.toNNReal ε⁻¹) T := by
    rw [antilipschitzWith_iff_le_mul_dist]
    intro x y
    have h := hlower (x - y)
    have hdist : dist (T x) (T y) = ‖T (x - y)‖ := by
      simp [dist_eq_norm, ← map_sub]
    have hdistG : dist x y = ‖x - y‖ := by rw [dist_eq_norm]
    rw [hdist, hdistG, Real.coe_toNNReal _ (by positivity),
      inv_mul_eq_div, le_div_iff₀ hε]
    simpa [mul_comm] using h
  exact hT (hanti.isClosed_range T.uniformContinuous)

omit [CompleteSpace H] in
theorem hilbertRangeSingular_domRestrict_orthogonal
    (T : G →L[ℂ] H) (hT : HilbertRangeSingular T)
    (F : Submodule ℂ G) [FiniteDimensional ℂ F] :
    HilbertRangeSingular (T.domRestrict Fᗮ) := by
  intro hclosed
  have hFclosed : IsClosed (F : Set G) := F.closed_of_finiteDimensional
  letI : F.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace F
  have hsup : F ⊔ Fᗮ = ⊤ :=
    Submodule.sup_orthogonal_of_hasOrthogonalProjection
  have hrangeOrth : IsClosed (LinearMap.range (T.domRestrict Fᗮ).toLinearMap :
      Set H) := by
    have heq : (LinearMap.range (T.domRestrict Fᗮ).toLinearMap : Set H) =
        Set.range (T.domRestrict Fᗮ) := by
      ext y
      simp
    rw [heq]
    exact hclosed
  have hrangeOrth' : IsClosed (Submodule.map T.toLinearMap Fᗮ : Set H) := by
    rw [← LinearMap.range_domRestrict]
    exact hrangeOrth
  let mapF : F →ₗ[ℂ] Submodule.map T.toLinearMap F :=
    (T.toLinearMap.domRestrict F).codRestrict _
      (fun x => ⟨x.1, x.2, rfl⟩)
  have hmapFsurj : Function.Surjective mapF := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  letI : FiniteDimensional ℂ (Submodule.map T.toLinearMap F) :=
    FiniteDimensional.of_surjective mapF hmapFsurj
  have hsum : IsClosed
      ((Submodule.map T.toLinearMap Fᗮ ⊔ Submodule.map T.toLinearMap F :
        Submodule ℂ H) : Set H) :=
    Submodule.isClosed_sup_finiteDimensional _ _ hrangeOrth'
  apply hT
  have heq : LinearMap.range T.toLinearMap =
      Submodule.map T.toLinearMap Fᗮ ⊔ Submodule.map T.toLinearMap F := by
    calc
      LinearMap.range T.toLinearMap = Submodule.map T.toLinearMap ⊤ :=
        LinearMap.range_eq_map T.toLinearMap
      _ = Submodule.map T.toLinearMap (F ⊔ Fᗮ) := by rw [hsup]
      _ = Submodule.map T.toLinearMap F ⊔ Submodule.map T.toLinearMap Fᗮ :=
        Submodule.map_sup _ _ _
      _ = _ := sup_comm _ _
  rw [show Set.range T = (LinearMap.range T.toLinearMap : Set H) by rfl, heq]
  exact hsum

def pqBlindScheduleEquiv : PQWildIndex ≃ ℕ :=
  (Equiv.prodCongr (Equiv.refl Bool) Nat.pairEquiv).trans
    Equiv.boolProdNatEquivNat

def pqObserverSmall {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℂ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℂ H₂]
    (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂)
    (q : PQWildIndex) (x : G) : Prop :=
  ‖x‖ = 1 ∧ if q.1 then ‖Q x‖ < (pqInv q.2.2) ^ 2
    else ‖P x‖ < (pqInv q.2.2) ^ 2

theorem exists_pq_singular_orthonormalArray
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂)
    (hP : HilbertRangeSingular P) (hQ : HilbertRangeSingular Q) :
    ∃ u : PQWildIndex → G, Orthonormal ℂ u ∧
      (∀ k n, ‖P (u (false, (k, n)))‖ < (pqInv n) ^ 2) ∧
      (∀ k n, ‖Q (u (true, (k, n)))‖ < (pqInv n) ^ 2) := by
  let rel : G → G → Prop := fun x y => inner ℂ x y = 0
  letI : Std.Symm rel := ⟨by
    intro x y hxy
    change inner ℂ x y = 0 at hxy
    change inner ℂ y x = 0
    exact inner_eq_zero_symm.mp hxy⟩
  let pred : ℕ → G → Prop := fun n x =>
    pqObserverSmall P Q (pqBlindScheduleEquiv.symm n) x
  have hstep : ∀ n (s : Finset G), ∃ y, pred n y ∧ ∀ x ∈ s, rel x y := by
    intro n s
    let F : Submodule ℂ G := Submodule.span ℂ (s : Set G)
    letI : FiniteDimensional ℂ F :=
      FiniteDimensional.span_of_finite ℂ s.finite_toSet
    let q := pqBlindScheduleEquiv.symm n
    have heps : 0 < (pqInv q.2.2) ^ 2 := sq_pos_of_pos (pqInv_pos _)
    cases hq : q.1 with
    | false =>
        have hs := hilbertRangeSingular_domRestrict_orthogonal P hP F
        obtain ⟨y, hy1, hyP⟩ :=
          exists_unit_norm_map_lt_of_hilbertRangeSingular
            (P.domRestrict Fᗮ) hs heps
        refine ⟨y, ?_, ?_⟩
        · change pqObserverSmall P Q q y
          rw [pqObserverSmall]
          refine ⟨hy1, ?_⟩
          simpa [hq] using hyP
        · intro x hx
          change inner ℂ x (y : G) = 0
          exact (Submodule.mem_orthogonal F (y : G)).mp y.2 x
            (Submodule.subset_span hx)
    | true =>
        have hs := hilbertRangeSingular_domRestrict_orthogonal Q hQ F
        obtain ⟨y, hy1, hyQ⟩ :=
          exists_unit_norm_map_lt_of_hilbertRangeSingular
            (Q.domRestrict Fᗮ) hs heps
        refine ⟨y, ?_, ?_⟩
        · change pqObserverSmall P Q q y
          rw [pqObserverSmall]
          refine ⟨hy1, ?_⟩
          simpa [hq] using hyQ
        · intro x hx
          change inner ℂ x (y : G) = 0
          exact (Submodule.mem_orthogonal F (y : G)).mp y.2 x
            (Submodule.subset_span hx)
  obtain ⟨f, hfPred, hfPair⟩ :=
    exists_seq_dependent_pairwise pred rel hstep
  let u : PQWildIndex → G := fun q => f (pqBlindScheduleEquiv q)
  have huPred : ∀ q, pqObserverSmall P Q q (u q) := by
    intro q
    simpa [pred, u] using hfPred (pqBlindScheduleEquiv q)
  have huOrtho : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro q r
    by_cases hqr : q = r
    · subst r
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K, (huPred q).1]
      norm_num
    · rw [if_neg hqr]
      exact hfPair (fun h => hqr (pqBlindScheduleEquiv.injective h))
  refine ⟨u, huOrtho, ?_, ?_⟩
  · intro k n
    have h := (huPred (false, (k, n))).2
    simpa [pqObserverSmall] using h
  · intro k n
    have h := (huPred (true, (k, n))).2
    simpa [pqObserverSmall] using h

theorem orthonormalSynthesis_inner_left
    {I : Type*} {u : I → G} (hu : Orthonormal ℂ u)
    (z : DiagonalL2 I) (i : I) :
    inner ℂ (u i) (hu.orthogonalFamily.linearIsometry z) = z i := by
  classical
  let U : DiagonalL2 I →ₗᵢ[ℂ] G := hu.orthogonalFamily.linearIsometry
  have hsingle : U (lp.single 2 i 1) = u i := by
    change hu.orthogonalFamily.linearIsometry (lp.single 2 i 1) = u i
    rw [OrthogonalFamily.linearIsometry_apply_single]
    simp [LinearIsometry.toSpanSingleton_apply]
  calc
    inner ℂ (u i) (U z) = inner ℂ (U (lp.single 2 i 1)) (U z) := by rw [hsingle]
    _ = inner ℂ (lp.single 2 i 1) z := U.inner_map_map _ z
    _ = inner ℂ 1 (z i) := lp.inner_single_left i 1 z
    _ = z i := by simp

theorem tendsto_pqInv_zero : Filter.Tendsto pqInv Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹)
    Filter.atTop (nhds 0)
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

noncomputable def wovenNormalIsometry
    {u : PQWildIndex → G} (hu : Orthonormal ℂ u) :
    pqWildNormalSubspace →ₗᵢ[ℂ] G :=
  hu.orthogonalFamily.linearIsometry.comp pqWildNormalSubspace.subtypeₗᵢ

def wovenNormalSubspace
    {u : PQWildIndex → G} (hu : Orthonormal ℂ u) : Submodule ℂ G :=
  LinearMap.range (wovenNormalIsometry hu).toLinearMap

theorem wovenNormalSubspace_isClosed
    {u : PQWildIndex → G} (hu : Orthonormal ℂ u) :
    IsClosed (wovenNormalSubspace hu : Set G) := by
  letI : CompleteSpace pqWildNormalSubspace :=
    pqWildNormalSubspace_isClosed.completeSpace_coe
  exact (wovenNormalIsometry hu).isometry.isClosedEmbedding.isClosed_range

theorem wovenNormalIsometry_inner_left
    {u : PQWildIndex → G} (hu : Orthonormal ℂ u)
    (z : pqWildNormalSubspace) (q : PQWildIndex) :
    inner ℂ (u q) (wovenNormalIsometry hu z) = (z : PQWildHilbert) q := by
  exact orthonormalSynthesis_inner_left hu (z : PQWildHilbert) q

theorem wovenNormalSubspace_inf_adjointRange_eq_bot
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : G →L[ℂ] H) (b : Bool) {u : PQWildIndex → G} (hu : Orthonormal ℂ u)
    (hsmall : ∀ k n, ‖T (u (b, (k, n)))‖ < (pqInv n) ^ 2) :
    wovenNormalSubspace hu ⊓ LinearMap.range T.adjoint.toLinearMap = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rcases hx.1 with ⟨z, hz⟩
  rcases hx.2 with ⟨y, hy⟩
  have hzy : wovenNormalIsometry hu z = T.adjoint y := by
    exact hz.trans hy.symm
  have hrel := (mem_pqWildNormalSubspace_iff (z : PQWildHilbert)).mp z.2
  have hcoeff : ∀ k : ℕ, (z : PQWildHilbert) (false, (k, 0)) = 0 := by
    intro k
    by_contra hk
    have hz0 : z ≠ 0 := by
      intro hzzero
      apply hk
      rw [hzzero]
      rfl
    have hy0 : y ≠ 0 := by
      intro hyzero
      apply hz0
      apply (wovenNormalIsometry hu).injective
      rw [hzy, hyzero]
      simp
    have hcoord : ∀ n : ℕ,
        (z : PQWildHilbert) (b, (k, n)) =
          inner ℂ (T (u (b, (k, n)))) y := by
      intro n
      calc
        (z : PQWildHilbert) (b, (k, n)) =
            inner ℂ (u (b, (k, n))) (wovenNormalIsometry hu z) :=
          (wovenNormalIsometry_inner_left hu z (b, (k, n))).symm
        _ = inner ℂ (u (b, (k, n))) (T.adjoint y) := by rw [hzy]
        _ = inner ℂ (T (u (b, (k, n)))) y := T.adjoint_inner_right _ _
    have hbound : ∀ n : ℕ,
        ‖(z : PQWildHilbert) (b, (k, n))‖ <
          (pqInv n) ^ 2 * ‖y‖ := by
      intro n
      rw [hcoord n]
      exact (norm_inner_le_norm _ _).trans_lt
        (mul_lt_mul_of_pos_right (hsmall k n) (norm_pos_iff.mpr hy0))
    have hnorm : ∀ n : ℕ,
        ‖(z : PQWildHilbert) (b, (k, n))‖ =
          pqInv n * ‖(z : PQWildHilbert) (false, (k, 0))‖ := by
      intro n
      rw [hrel b k n, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (pqInv_pos n)]
    have ht : Filter.Tendsto (fun n : ℕ => pqInv n * ‖y‖)
        Filter.atTop (nhds 0) := by
      simpa using tendsto_pqInv_zero.mul_const ‖y‖
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        pqInv n * ‖y‖ < ‖(z : PQWildHilbert) (false, (k, 0))‖ :=
      ht.eventually (Iio_mem_nhds (norm_pos_iff.mpr hk))
    rcases Filter.eventually_atTop.mp hev with ⟨n, hn⟩
    have hsmallAt := hn n le_rfl
    have hboundAt := hbound n
    rw [hnorm n] at hboundAt
    nlinarith [pqInv_pos n]
  have hzzero : z = 0 := by
    apply Subtype.ext
    ext q
    rcases q with ⟨b, k, n⟩
    rw [hrel b k n, hcoeff k, mul_zero]
    rfl
  rw [← hz, hzzero]
  exact (wovenNormalIsometry hu).map_zero

theorem wovenNormalSubspace_has_countable_independent_family
    {u : PQWildIndex → G} (hu : Orthonormal ℂ u) :
    ∃ v : ℕ → G, LinearIndependent ℂ v ∧
      ∀ k, v k ∈ wovenNormalSubspace hu := by
  let V := wovenNormalIsometry hu
  let v : ℕ → G := fun k => V (pqWildNormalVectorSub k)
  refine ⟨v, ?_, ?_⟩
  · have hker : LinearMap.ker V.toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr V.injective
    simpa [v, V, Function.comp_def] using
      pqWildNormalVectorSub_linearIndependent.map' V.toLinearMap hker
  · intro k
    exact ⟨pqWildNormalVectorSub k, rfl⟩

theorem dense_orthogonal_image_of_le_wovenNormalSubspace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : G →L[ℂ] H) (hDense : Dense (LinearMap.range T.toLinearMap : Set H))
    {u : PQWildIndex → G} (hu : Orthonormal ℂ u)
    (hAvoid : wovenNormalSubspace hu ⊓ LinearMap.range T.adjoint.toLinearMap = ⊥)
    (L : Submodule ℂ G) (hLclosed : IsClosed (L : Set G))
    (hLD : L ≤ wovenNormalSubspace hu) :
    Dense (Lᗮ.map T.toLinearMap : Set H) := by
  apply (dense_image_orthogonal_iff_inf_adjointRange_eq_bot
    T hDense L hLclosed).mpr
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxD : x ∈ wovenNormalSubspace hu ⊓
      LinearMap.range T.adjoint.toLinearMap := ⟨hLD hx.1, hx.2⟩
  rw [hAvoid] at hxD
  exact hxD

theorem exists_common_woven_normal_subspace
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂)
    (hP : HilbertRangeSingular P) (hQ : HilbertRangeSingular Q) :
    ∃ u : PQWildIndex → G, ∃ hu : Orthonormal ℂ u,
      IsClosed (wovenNormalSubspace hu : Set G) ∧
      wovenNormalSubspace hu ⊓ LinearMap.range P.adjoint.toLinearMap = ⊥ ∧
      wovenNormalSubspace hu ⊓ LinearMap.range Q.adjoint.toLinearMap = ⊥ ∧
      ∃ v : ℕ → G, LinearIndependent ℂ v ∧
        ∀ k, v k ∈ wovenNormalSubspace hu := by
  obtain ⟨u, hu, hPsmall, hQsmall⟩ :=
    exists_pq_singular_orthonormalArray P Q hP hQ
  exact ⟨u, hu, wovenNormalSubspace_isClosed hu,
    wovenNormalSubspace_inf_adjointRange_eq_bot P false hu hPsmall,
    wovenNormalSubspace_inf_adjointRange_eq_bot Q true hu hQsmall,
    wovenNormalSubspace_has_countable_independent_family hu⟩

theorem common_woven_defect_lattice
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂)
    (hPdense : Dense (LinearMap.range P.toLinearMap : Set H₁))
    (hQdense : Dense (LinearMap.range Q.toLinearMap : Set H₂))
    {u : PQWildIndex → G} (hu : Orthonormal ℂ u)
    (hPAvoid : wovenNormalSubspace hu ⊓ LinearMap.range P.adjoint.toLinearMap = ⊥)
    (hQAvoid : wovenNormalSubspace hu ⊓ LinearMap.range Q.adjoint.toLinearMap = ⊥) :
    ∀ L : Submodule ℂ G, IsClosed (L : Set G) → L ≤ wovenNormalSubspace hu →
      Dense (Lᗮ.map P.toLinearMap : Set H₁) ∧
      Dense (Lᗮ.map Q.toLinearMap : Set H₂) := by
  intro L hLclosed hLD
  exact ⟨dense_orthogonal_image_of_le_wovenNormalSubspace
      P hPdense hu hPAvoid L hLclosed hLD,
    dense_orthogonal_image_of_le_wovenNormalSubspace
      Q hQdense hu hQAvoid L hLclosed hLD⟩

theorem hilbertRangeSingular_iff_no_antilipschitz
    (T : G →L[ℂ] H) (hinj : Function.Injective T) :
    HilbertRangeSingular T ↔ ¬ ∃ K : NNReal, AntilipschitzWith K T := by
  exact not_congr (T.isClosed_range_iff_antilipschitz_of_injective hinj)

theorem twoSidedSingular_has_common_woven_normal_lattice
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂)
    (hPinj : Function.Injective P) (hQinj : Function.Injective Q)
    (hPdense : DenseRange P) (hQdense : DenseRange Q)
    (hsing : IsTwoSidedSingular P Q) :
    ∃ u : PQWildIndex → G, ∃ hu : Orthonormal ℂ u,
      IsClosed (wovenNormalSubspace hu : Set G) ∧
      wovenNormalSubspace hu ⊓ LinearMap.range P.adjoint.toLinearMap = ⊥ ∧
      wovenNormalSubspace hu ⊓ LinearMap.range Q.adjoint.toLinearMap = ⊥ ∧
      (∃ v : ℕ → G, LinearIndependent ℂ v ∧
        ∀ k, v k ∈ wovenNormalSubspace hu) ∧
      ∀ L : Submodule ℂ G, IsClosed (L : Set G) → L ≤ wovenNormalSubspace hu →
        Dense (Lᗮ.map P.toLinearMap : Set H₁) ∧
        Dense (Lᗮ.map Q.toLinearMap : Set H₂) := by
  have hPsing : HilbertRangeSingular P :=
    (hilbertRangeSingular_iff_no_antilipschitz P hPinj).mpr hsing.1
  have hQsing : HilbertRangeSingular Q :=
    (hilbertRangeSingular_iff_no_antilipschitz Q hQinj).mpr hsing.2
  obtain ⟨u, hu, hclosed, hPAvoid, hQAvoid, hinfinite⟩ :=
    exists_common_woven_normal_subspace P Q hPsing hQsing
  exact ⟨u, hu, hclosed, hPAvoid, hQAvoid, hinfinite,
    common_woven_defect_lattice P Q hPdense hQdense hu hPAvoid hQAvoid⟩

theorem one_coercive_observer_forces_trivial_common_defect
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂)
    (hPinj : Function.Injective P) (hQinj : Function.Injective Q)
    (hcoercive : (∃ K : NNReal, AntilipschitzWith K P) ∨
      ∃ K : NNReal, AntilipschitzWith K Q)
    (M : Submodule ℂ G) (hMclosed : IsClosed (M : Set G))
    (hPdense : Dense (M.map P.toLinearMap : Set H₁))
    (hQdense : Dense (M.map Q.toLinearMap : Set H₂)) :
    M = ⊤ := by
  rcases hcoercive with ⟨K, hK⟩ | ⟨K, hK⟩
  · exact closed_biDense_eq_top_of_antilipschitz P hPinj M hMclosed hPdense hK
  · exact closed_biDense_eq_top_of_antilipschitz Q hQinj M hMclosed hQdense hK

omit [CompleteSpace G] in
theorem coercive_or_twoSidedSingular
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℂ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℂ H₂]
    (P : G →L[ℂ] H₁) (Q : G →L[ℂ] H₂) :
    ((∃ K : NNReal, AntilipschitzWith K P) ∨
      ∃ K : NNReal, AntilipschitzWith K Q) ∨
      ((¬ ∃ K : NNReal, AntilipschitzWith K P) ∧
        ¬ ∃ K : NNReal, AntilipschitzWith K Q) := by
  by_cases hP : ∃ K : NNReal, AntilipschitzWith K P
  · exact Or.inl (Or.inl hP)
  · by_cases hQ : ∃ K : NNReal, AntilipschitzWith K Q
    · exact Or.inl (Or.inr hQ)
    · exact Or.inr ⟨hP, hQ⟩

omit [CompleteSpace G] in
theorem orthogonal_ne_top_of_ne_bot (L : Submodule ℂ G) (hL : L ≠ ⊥) :
    Lᗮ ≠ ⊤ := by
  exact fun h => hL ((L.orthogonal_eq_top_iff).mp h)

variable {G : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

abbrev FiniteWildIndex (m : ℕ) := Fin (m + 1) × (ℕ × ℕ)
abbrev FiniteWildHilbert (m : ℕ) := DiagonalL2 (FiniteWildIndex m)

def finiteWildScheduleEquiv (m : ℕ) : FiniteWildIndex m ≃ ℕ :=
  (Equiv.prodCongr (Equiv.refl (Fin (m + 1))) Nat.pairEquiv).trans
    ((Equiv.prodComm (Fin (m + 1)) ℕ).trans (Nat.divModEquiv (m + 1)).symm)

def finiteObserverSmall {m : ℕ} {H : Fin (m + 1) → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℂ (H i)]
    (T : ∀ i, G →L[ℂ] H i) (q : FiniteWildIndex m) (x : G) : Prop :=
  ‖x‖ = 1 ∧ ‖T q.1 x‖ < (pqInv q.2.2) ^ 2

theorem exists_finite_singular_orthonormalArray
    {m : ℕ} {H : Fin (m + 1) → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (T : ∀ i, G →L[ℂ] H i) (hT : ∀ i, HilbertRangeSingular (T i)) :
    ∃ u : FiniteWildIndex m → G, Orthonormal ℂ u ∧
      ∀ i k n, ‖T i (u (i, (k, n)))‖ < (pqInv n) ^ 2 := by
  let rel : G → G → Prop := fun x y => inner ℂ x y = 0
  letI : Std.Symm rel := ⟨by
    intro x y hxy
    exact inner_eq_zero_symm.mp hxy⟩
  let pred : ℕ → G → Prop := fun n x =>
    finiteObserverSmall T (finiteWildScheduleEquiv m |>.symm n) x
  have hstep : ∀ n (s : Finset G), ∃ y, pred n y ∧ ∀ x ∈ s, rel x y := by
    intro n s
    let q := (finiteWildScheduleEquiv m).symm n
    let F : Submodule ℂ G := Submodule.span ℂ (s : Set G)
    let Ts : Fᗮ →L[ℂ] H q.1 := (T q.1).domRestrict Fᗮ
    have hs : HilbertRangeSingular Ts :=
      hilbertRangeSingular_domRestrict_orthogonal (T q.1) (hT q.1) F
    have heps : 0 < (pqInv q.2.2) ^ 2 := sq_pos_of_pos (pqInv_pos _)
    obtain ⟨y, hy1, hyT⟩ :=
      exists_unit_norm_map_lt_of_hilbertRangeSingular Ts hs heps
    refine ⟨y, ?_, ?_⟩
    · change finiteObserverSmall T q y
      exact ⟨hy1, hyT⟩
    · intro x hx
      exact (Submodule.mem_orthogonal F (y : G)).mp y.2 x
        (Submodule.subset_span hx)
  obtain ⟨f, hfPred, hfPair⟩ := exists_seq_dependent_pairwise pred rel hstep
  let u : FiniteWildIndex m → G := fun q => f (finiteWildScheduleEquiv m q)
  have huPred : ∀ q, finiteObserverSmall T q (u q) := by
    intro q
    simpa [pred, u] using hfPred (finiteWildScheduleEquiv m q)
  have huOrtho : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro q r
    by_cases hqr : q = r
    · subst r
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K, (huPred q).1]
      norm_num
    · rw [if_neg hqr]
      exact hfPair (fun h => hqr ((finiteWildScheduleEquiv m).injective h))
  exact ⟨u, huOrtho, fun i k n => (huPred (i, (k, n))).2⟩

def finiteWildEval {m : ℕ} (q : FiniteWildIndex m) :
    FiniteWildHilbert m →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun x => by simpa using lp.norm_apply_le_norm (by norm_num) x q)

@[simp] theorem finiteWildEval_apply {m : ℕ} (q : FiniteWildIndex m)
    (x : FiniteWildHilbert m) : finiteWildEval q x = x q := rfl

def finiteWovenNormalSubspace (m : ℕ) : Submodule ℂ (FiniteWildHilbert m) :=
  ⨅ i : Fin (m + 1), ⨅ k : ℕ, ⨅ n : ℕ,
    (finiteWildEval (i, (k, n)) -
      (pqInv n : ℂ) • finiteWildEval ((0 : Fin (m + 1)), (k, 0))).ker

theorem mem_finiteWovenNormalSubspace_iff {m : ℕ} (x : FiniteWildHilbert m) :
    x ∈ finiteWovenNormalSubspace m ↔
      ∀ i k n, x (i, (k, n)) =
        (pqInv n : ℂ) * x ((0 : Fin (m + 1)), (k, 0)) := by
  rw [finiteWovenNormalSubspace]
  simp only [Submodule.mem_iInf]
  constructor
  · intro h i k n
    have h' := h i k n
    change (finiteWildEval (i, (k, n)) -
      (pqInv n : ℂ) • finiteWildEval ((0 : Fin (m + 1)), (k, 0))) x = 0 at h'
    simpa [sub_eq_zero] using h'
  · intro h i k n
    change (finiteWildEval (i, (k, n)) -
      (pqInv n : ℂ) • finiteWildEval ((0 : Fin (m + 1)), (k, 0))) x = 0
    simpa [sub_eq_zero] using h i k n

theorem finiteWovenNormalSubspace_isClosed (m : ℕ) :
    IsClosed (finiteWovenNormalSubspace m : Set (FiniteWildHilbert m)) := by
  have heq : (finiteWovenNormalSubspace m : Set (FiniteWildHilbert m)) =
      ⋂ i : Fin (m + 1), ⋂ k : ℕ, ⋂ n : ℕ,
        ((finiteWildEval (i, (k, n)) -
          (pqInv n : ℂ) • finiteWildEval ((0 : Fin (m + 1)), (k, 0))).ker :
            Set (FiniteWildHilbert m)) := by
    ext x
    change x ∈ finiteWovenNormalSubspace m ↔ x ∈
      ⋂ i : Fin (m + 1), ⋂ k : ℕ, ⋂ n : ℕ,
        ((finiteWildEval (i, (k, n)) -
          (pqInv n : ℂ) • finiteWildEval ((0 : Fin (m + 1)), (k, 0))).ker :
            Set (FiniteWildHilbert m))
    rw [mem_finiteWovenNormalSubspace_iff]
    simp only [Set.mem_iInter]
    constructor
    · intro h i k n
      change (finiteWildEval (i, (k, n)) -
        (pqInv n : ℂ) • finiteWildEval ((0 : Fin (m + 1)), (k, 0))) x = 0
      simpa [sub_eq_zero] using h i k n
    · intro h i k n
      have h' := h i k n
      change (finiteWildEval (i, (k, n)) -
        (pqInv n : ℂ) • finiteWildEval ((0 : Fin (m + 1)), (k, 0))) x = 0 at h'
      simpa [sub_eq_zero] using h'
  rw [heq]
  exact isClosed_iInter fun i => isClosed_iInter fun k => isClosed_iInter fun n =>
    (finiteWildEval (i, (k, n)) -
      (pqInv n : ℂ) • finiteWildEval ((0 : Fin (m + 1)), (k, 0))).isClosed_ker

def finiteWovenNormalWeight (m k : ℕ) : FiniteWildIndex m → ℂ
  | (_, (j, n)) => if j = k then (pqInv n : ℂ) else 0

theorem finiteWovenNormalWeight_summable_sq (m k : ℕ) :
    Summable (fun q : FiniteWildIndex m => ‖finiteWovenNormalWeight m k q‖ ^ 2) := by
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
        exact hbase.congr fun n => by simp [finiteWovenNormalWeight]
      · simp [finiteWovenNormalWeight, hj]
    · apply summable_of_ne_finset_zero (s := {k})
      intro j hj
      have hjk : j ≠ k := by simpa using hj
      simp [finiteWovenNormalWeight, hjk]
  · exact Summable.of_finite

def finiteWovenNormalVector (m k : ℕ) : FiniteWildHilbert m :=
  ⟨finiteWovenNormalWeight m k,
    HilbertSchmidt.memℓp_of_sq (finiteWovenNormalWeight_summable_sq m k)⟩

@[simp] theorem finiteWovenNormalVector_apply (m k : ℕ)
    (i : Fin (m + 1)) (j n : ℕ) :
    finiteWovenNormalVector m k (i, (j, n)) =
      if j = k then (pqInv n : ℂ) else 0 := rfl

theorem finiteWovenNormalVector_mem (m k : ℕ) :
    finiteWovenNormalVector m k ∈ finiteWovenNormalSubspace m := by
  rw [mem_finiteWovenNormalSubspace_iff]
  intro i j n
  by_cases hj : j = k
  · subst j
    simp [pqInv]
  · simp [finiteWovenNormalVector_apply, hj]

def finiteWovenNormalVectorSub (m k : ℕ) : finiteWovenNormalSubspace m :=
  ⟨finiteWovenNormalVector m k, finiteWovenNormalVector_mem m k⟩

def finiteWovenNormalCoordinate (m k : ℕ) :
    finiteWovenNormalSubspace m →ₗ[ℂ] ℂ :=
  (finiteWildEval ((0 : Fin (m + 1)), (k, 0))).toLinearMap.comp
    (finiteWovenNormalSubspace m).subtype

theorem finiteWovenNormalVectorSub_linearIndependent (m : ℕ) :
    LinearIndependent ℂ (finiteWovenNormalVectorSub m) := by
  rw [linearIndependent_iff]
  intro l hl
  apply Finsupp.ext
  intro k
  have hk := congrArg (finiteWovenNormalCoordinate m k) hl
  rw [Finsupp.apply_linearCombination] at hk
  simpa [Finsupp.linearCombination_apply, finiteWovenNormalCoordinate,
    finiteWovenNormalVectorSub, finiteWovenNormalVector, finiteWovenNormalWeight,
    pqInv, Finsupp.sum] using hk

noncomputable def finiteWovenNormalIsometry {m : ℕ}
    {u : FiniteWildIndex m → G} (hu : Orthonormal ℂ u) :
    finiteWovenNormalSubspace m →ₗᵢ[ℂ] G :=
  hu.orthogonalFamily.linearIsometry.comp (finiteWovenNormalSubspace m).subtypeₗᵢ

def finiteWovenNormalSpace {m : ℕ}
    {u : FiniteWildIndex m → G} (hu : Orthonormal ℂ u) : Submodule ℂ G :=
  LinearMap.range (finiteWovenNormalIsometry hu).toLinearMap

theorem finiteWovenNormalSpace_isClosed {m : ℕ}
    {u : FiniteWildIndex m → G} (hu : Orthonormal ℂ u) :
    IsClosed (finiteWovenNormalSpace hu : Set G) := by
  letI : CompleteSpace (finiteWovenNormalSubspace m) :=
    (finiteWovenNormalSubspace_isClosed m).completeSpace_coe
  exact (finiteWovenNormalIsometry hu).isometry.isClosedEmbedding.isClosed_range

theorem finiteWovenNormalIsometry_inner_left {m : ℕ}
    {u : FiniteWildIndex m → G} (hu : Orthonormal ℂ u)
    (z : finiteWovenNormalSubspace m) (q : FiniteWildIndex m) :
    inner ℂ (u q) (finiteWovenNormalIsometry hu z) =
      (z : FiniteWildHilbert m) q := by
  exact orthonormalSynthesis_inner_left hu (z : FiniteWildHilbert m) q

theorem finiteWovenNormalSpace_inf_adjointRange_eq_bot
    {m : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : G →L[ℂ] H) (i : Fin (m + 1))
    {u : FiniteWildIndex m → G} (hu : Orthonormal ℂ u)
    (hsmall : ∀ k n, ‖T (u (i, (k, n)))‖ < (pqInv n) ^ 2) :
    finiteWovenNormalSpace hu ⊓ LinearMap.range T.adjoint.toLinearMap = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rcases hx.1 with ⟨z, hz⟩
  rcases hx.2 with ⟨y, hy⟩
  have hzy : finiteWovenNormalIsometry hu z = T.adjoint y := hz.trans hy.symm
  have hrel :=
    (mem_finiteWovenNormalSubspace_iff (z : FiniteWildHilbert m)).mp z.2
  have hcoeff : ∀ k : ℕ,
      (z : FiniteWildHilbert m) ((0 : Fin (m + 1)), (k, 0)) = 0 := by
    intro k
    by_contra hk
    have hz0 : z ≠ 0 := by
      intro hzzero
      apply hk
      rw [hzzero]
      rfl
    have hy0 : y ≠ 0 := by
      intro hyzero
      apply hz0
      apply (finiteWovenNormalIsometry hu).injective
      rw [hzy, hyzero]
      simp
    have hcoord : ∀ n : ℕ,
        (z : FiniteWildHilbert m) (i, (k, n)) =
          inner ℂ (T (u (i, (k, n)))) y := by
      intro n
      calc
        (z : FiniteWildHilbert m) (i, (k, n)) =
            inner ℂ (u (i, (k, n))) (finiteWovenNormalIsometry hu z) :=
          (finiteWovenNormalIsometry_inner_left hu z (i, (k, n))).symm
        _ = inner ℂ (u (i, (k, n))) (T.adjoint y) := by rw [hzy]
        _ = inner ℂ (T (u (i, (k, n)))) y := T.adjoint_inner_right _ _
    have hbound : ∀ n : ℕ,
        ‖(z : FiniteWildHilbert m) (i, (k, n))‖ <
          (pqInv n) ^ 2 * ‖y‖ := by
      intro n
      rw [hcoord n]
      exact (norm_inner_le_norm _ _).trans_lt
        (mul_lt_mul_of_pos_right (hsmall k n) (norm_pos_iff.mpr hy0))
    have hnorm : ∀ n : ℕ,
        ‖(z : FiniteWildHilbert m) (i, (k, n))‖ =
          pqInv n *
            ‖(z : FiniteWildHilbert m) ((0 : Fin (m + 1)), (k, 0))‖ := by
      intro n
      rw [hrel i k n, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (pqInv_pos n)]
    have ht : Filter.Tendsto (fun n : ℕ => pqInv n * ‖y‖)
        Filter.atTop (nhds 0) := by
      simpa using tendsto_pqInv_zero.mul_const ‖y‖
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        pqInv n * ‖y‖ <
          ‖(z : FiniteWildHilbert m) ((0 : Fin (m + 1)), (k, 0))‖ :=
      ht.eventually (Iio_mem_nhds (norm_pos_iff.mpr hk))
    rcases Filter.eventually_atTop.mp hev with ⟨n, hn⟩
    have hsmallAt := hn n le_rfl
    have hboundAt := hbound n
    rw [hnorm n] at hboundAt
    nlinarith [pqInv_pos n]
  have hzzero : z = 0 := by
    apply Subtype.ext
    ext q
    rcases q with ⟨i', k, n⟩
    rw [hrel i' k n, hcoeff k, mul_zero]
    rfl
  rw [← hz, hzzero]
  exact (finiteWovenNormalIsometry hu).map_zero

theorem finiteWovenNormalSpace_has_countable_independent_family {m : ℕ}
    {u : FiniteWildIndex m → G} (hu : Orthonormal ℂ u) :
    ∃ v : ℕ → G, LinearIndependent ℂ v ∧
      ∀ k, v k ∈ finiteWovenNormalSpace hu := by
  let V := finiteWovenNormalIsometry hu
  let v : ℕ → G := fun k => V (finiteWovenNormalVectorSub m k)
  refine ⟨v, ?_, ?_⟩
  · have hker : LinearMap.ker V.toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr V.injective
    simpa [v, V, Function.comp_def] using
      (finiteWovenNormalVectorSub_linearIndependent m).map' V.toLinearMap hker
  · intro k
    exact ⟨finiteWovenNormalVectorSub m k, rfl⟩

theorem dense_orthogonal_image_of_le_finiteWovenNormalSpace
    {m : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : G →L[ℂ] H) (hDense : DenseRange T)
    {u : FiniteWildIndex m → G} (hu : Orthonormal ℂ u)
    (hAvoid : finiteWovenNormalSpace hu ⊓
      LinearMap.range T.adjoint.toLinearMap = ⊥)
    (L : Submodule ℂ G) (hLclosed : IsClosed (L : Set G))
    (hLD : L ≤ finiteWovenNormalSpace hu) :
    Dense (Lᗮ.map T.toLinearMap : Set H) := by
  apply (dense_image_orthogonal_iff_inf_adjointRange_eq_bot
    T hDense L hLclosed).mpr
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxD : x ∈ finiteWovenNormalSpace hu ⊓
      LinearMap.range T.adjoint.toLinearMap := ⟨hLD hx.1, hx.2⟩
  rw [hAvoid] at hxD
  exact hxD

theorem finite_singular_observer_wild_lattice
    {m : ℕ} {H : Fin (m + 1) → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (T : ∀ i, G →L[ℂ] H i)
    (hTsing : ∀ i, HilbertRangeSingular (T i))
    (hTdense : ∀ i, DenseRange (T i)) :
    ∃ u : FiniteWildIndex m → G, ∃ hu : Orthonormal ℂ u,
      IsClosed (finiteWovenNormalSpace hu : Set G) ∧
      (∀ i, finiteWovenNormalSpace hu ⊓
        LinearMap.range (T i).adjoint.toLinearMap = ⊥) ∧
      (∃ v : ℕ → G, LinearIndependent ℂ v ∧
        ∀ k, v k ∈ finiteWovenNormalSpace hu) ∧
      ∀ L : Submodule ℂ G, IsClosed (L : Set G) →
        L ≤ finiteWovenNormalSpace hu →
          ∀ i, Dense (Lᗮ.map (T i).toLinearMap : Set (H i)) := by
  obtain ⟨u, hu, hsmall⟩ := exists_finite_singular_orthonormalArray T hTsing
  have hAvoid : ∀ i, finiteWovenNormalSpace hu ⊓
      LinearMap.range (T i).adjoint.toLinearMap = ⊥ := fun i =>
    finiteWovenNormalSpace_inf_adjointRange_eq_bot (T i) i hu (hsmall i)
  refine ⟨u, hu, finiteWovenNormalSpace_isClosed hu, hAvoid,
    finiteWovenNormalSpace_has_countable_independent_family hu, ?_⟩
  intro L hLclosed hLD i
  exact dense_orthogonal_image_of_le_finiteWovenNormalSpace
    (T i) (hTdense i) hu (hAvoid i) L hLclosed hLD

theorem finite_noncoercive_observer_wild_lattice
    {m : ℕ} {H : Fin (m + 1) → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (T : ∀ i, G →L[ℂ] H i)
    (hTinj : ∀ i, Function.Injective (T i))
    (hTdense : ∀ i, DenseRange (T i))
    (hnoncoercive : ∀ i, ¬ ∃ K : NNReal, AntilipschitzWith K (T i)) :
    ∃ u : FiniteWildIndex m → G, ∃ hu : Orthonormal ℂ u,
      IsClosed (finiteWovenNormalSpace hu : Set G) ∧
      (∀ i, finiteWovenNormalSpace hu ⊓
        LinearMap.range (T i).adjoint.toLinearMap = ⊥) ∧
      (∃ v : ℕ → G, LinearIndependent ℂ v ∧
        ∀ k, v k ∈ finiteWovenNormalSpace hu) ∧
      ∀ L : Submodule ℂ G, IsClosed (L : Set G) →
        L ≤ finiteWovenNormalSpace hu →
          ∀ i, Dense (Lᗮ.map (T i).toLinearMap : Set (H i)) := by
  apply finite_singular_observer_wild_lattice T
  · intro i
    exact (hilbertRangeSingular_iff_no_antilipschitz (T i) (hTinj i)).mpr
      (hnoncoercive i)
  · exact hTdense

theorem finite_coercive_observer_forces_trivial_common_defect
    {m : ℕ} {H : Fin (m + 1) → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    (T : ∀ i, G →L[ℂ] H i) (hTinj : ∀ i, Function.Injective (T i))
    (M : Submodule ℂ G) (hMclosed : IsClosed (M : Set G))
    (hMdense : ∀ i, Dense (M.map (T i).toLinearMap : Set (H i)))
    (hcoercive : ∃ i, ∃ K : NNReal, AntilipschitzWith K (T i)) :
    M = ⊤ := by
  obtain ⟨i, K, hK⟩ := hcoercive
  exact closed_biDense_eq_top_of_antilipschitz
    (T i) (hTinj i) M hMclosed (hMdense i) hK

omit [CompleteSpace G] in
theorem finite_coercive_or_all_noncoercive
    {m : ℕ} {H : Fin (m + 1) → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℂ (H i)]
    (T : ∀ i, G →L[ℂ] H i) :
    (∃ i, ∃ K : NNReal, AntilipschitzWith K (T i)) ∨
      ∀ i, ¬ ∃ K : NNReal, AntilipschitzWith K (T i) := by
  by_cases h : ∃ i, ∃ K : NNReal, AntilipschitzWith K (T i)
  · exact Or.inl h
  · exact Or.inr fun i hi => h ⟨i, hi⟩

abbrev CountableWildIndex := ℕ × (ℕ × ℕ)
abbrev CountableWildHilbert := DiagonalL2 CountableWildIndex

def countableWildScheduleEquiv : CountableWildIndex ≃ ℕ :=
  (Equiv.prodCongr (Equiv.refl ℕ) Nat.pairEquiv).trans Nat.pairEquiv

def countableObserverSmall {H : ℕ → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℂ (H i)]
    (T : ∀ i, G →L[ℂ] H i) (q : CountableWildIndex) (x : G) : Prop :=
  ‖x‖ = 1 ∧ ‖T q.1 x‖ < (pqInv q.1 * pqInv q.2.2) ^ 2

theorem exists_countable_singular_orthonormalArray
    {H : ℕ → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (T : ∀ i, G →L[ℂ] H i) (hT : ∀ i, HilbertRangeSingular (T i)) :
    ∃ u : CountableWildIndex → G, Orthonormal ℂ u ∧
      ∀ i k n,
        ‖T i (u (i, (k, n)))‖ < (pqInv i * pqInv n) ^ 2 := by
  let rel : G → G → Prop := fun x y => inner ℂ x y = 0
  letI : Std.Symm rel := ⟨by
    intro x y hxy
    exact inner_eq_zero_symm.mp hxy⟩
  let pred : ℕ → G → Prop := fun n x =>
    countableObserverSmall T (countableWildScheduleEquiv.symm n) x
  have hstep : ∀ n (s : Finset G), ∃ y, pred n y ∧ ∀ x ∈ s, rel x y := by
    intro n s
    let q := countableWildScheduleEquiv.symm n
    let F : Submodule ℂ G := Submodule.span ℂ (s : Set G)
    let Ts : Fᗮ →L[ℂ] H q.1 := (T q.1).domRestrict Fᗮ
    have hs : HilbertRangeSingular Ts :=
      hilbertRangeSingular_domRestrict_orthogonal (T q.1) (hT q.1) F
    have heps : 0 < (pqInv q.1 * pqInv q.2.2) ^ 2 :=
      sq_pos_of_pos (mul_pos (pqInv_pos _) (pqInv_pos _))
    obtain ⟨y, hy1, hyT⟩ :=
      exists_unit_norm_map_lt_of_hilbertRangeSingular Ts hs heps
    refine ⟨y, ?_, ?_⟩
    · change countableObserverSmall T q y
      exact ⟨hy1, hyT⟩
    · intro x hx
      exact (Submodule.mem_orthogonal F (y : G)).mp y.2 x
        (Submodule.subset_span hx)
  obtain ⟨f, hfPred, hfPair⟩ := exists_seq_dependent_pairwise pred rel hstep
  let u : CountableWildIndex → G := fun q => f (countableWildScheduleEquiv q)
  have huPred : ∀ q, countableObserverSmall T q (u q) := by
    intro q
    simpa [pred, u] using hfPred (countableWildScheduleEquiv q)
  have huOrtho : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro q r
    by_cases hqr : q = r
    · subst r
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K, (huPred q).1]
      norm_num
    · rw [if_neg hqr]
      exact hfPair (fun h => hqr (countableWildScheduleEquiv.injective h))
  exact ⟨u, huOrtho, fun i k n => (huPred (i, (k, n))).2⟩

def countableWildEval (q : CountableWildIndex) : CountableWildHilbert →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun x => by simpa using lp.norm_apply_le_norm (by norm_num) x q)

@[simp] theorem countableWildEval_apply (q : CountableWildIndex)
    (x : CountableWildHilbert) : countableWildEval q x = x q := rfl

def countableWovenNormalSubspace : Submodule ℂ CountableWildHilbert :=
  ⨅ i : ℕ, ⨅ k : ℕ, ⨅ n : ℕ,
    (countableWildEval (i, (k, n)) -
      (pqInv i * pqInv n : ℂ) • countableWildEval (0, (k, 0))).ker

theorem mem_countableWovenNormalSubspace_iff (x : CountableWildHilbert) :
    x ∈ countableWovenNormalSubspace ↔
      ∀ i k n, x (i, (k, n)) =
        (pqInv i * pqInv n : ℂ) * x (0, (k, 0)) := by
  rw [countableWovenNormalSubspace]
  simp only [Submodule.mem_iInf]
  constructor
  · intro h i k n
    have h' := h i k n
    change (countableWildEval (i, (k, n)) -
      (pqInv i * pqInv n : ℂ) • countableWildEval (0, (k, 0))) x = 0 at h'
    simpa [sub_eq_zero] using h'
  · intro h i k n
    change (countableWildEval (i, (k, n)) -
      (pqInv i * pqInv n : ℂ) • countableWildEval (0, (k, 0))) x = 0
    simpa [sub_eq_zero] using h i k n

theorem countableWovenNormalSubspace_isClosed :
    IsClosed (countableWovenNormalSubspace : Set CountableWildHilbert) := by
  have heq : (countableWovenNormalSubspace : Set CountableWildHilbert) =
      ⋂ i : ℕ, ⋂ k : ℕ, ⋂ n : ℕ,
        ((countableWildEval (i, (k, n)) -
          (pqInv i * pqInv n : ℂ) • countableWildEval (0, (k, 0))).ker :
            Set CountableWildHilbert) := by
    ext x
    change x ∈ countableWovenNormalSubspace ↔ x ∈
      ⋂ i : ℕ, ⋂ k : ℕ, ⋂ n : ℕ,
        ((countableWildEval (i, (k, n)) -
          (pqInv i * pqInv n : ℂ) • countableWildEval (0, (k, 0))).ker :
            Set CountableWildHilbert)
    rw [mem_countableWovenNormalSubspace_iff]
    simp only [Set.mem_iInter]
    constructor
    · intro h i k n
      change (countableWildEval (i, (k, n)) -
        (pqInv i * pqInv n : ℂ) • countableWildEval (0, (k, 0))) x = 0
      simpa [sub_eq_zero] using h i k n
    · intro h i k n
      have h' := h i k n
      change (countableWildEval (i, (k, n)) -
        (pqInv i * pqInv n : ℂ) • countableWildEval (0, (k, 0))) x = 0 at h'
      simpa [sub_eq_zero] using h'
  rw [heq]
  exact isClosed_iInter fun i => isClosed_iInter fun k => isClosed_iInter fun n =>
    (countableWildEval (i, (k, n)) -
      (pqInv i * pqInv n : ℂ) • countableWildEval (0, (k, 0))).isClosed_ker

def countableWildWeightEquiv : CountableWildIndex ≃ (ℕ × ℕ) × ℕ where
  toFun q := ((q.1, q.2.2), q.2.1)
  invFun q := (q.1.1, (q.2, q.1.2))
  left_inv := by rintro ⟨i, j, n⟩; rfl
  right_inv := by rintro ⟨⟨i, n⟩, j⟩; rfl

def countableWovenNormalWeight (k : ℕ) : CountableWildIndex → ℂ
  | (i, (j, n)) =>
      if j = k then (pqInv i * pqInv n : ℂ) else 0

theorem countableWovenNormalWeight_summable_sq (k : ℕ) :
    Summable (fun q : CountableWildIndex =>
      ‖countableWovenNormalWeight k q‖ ^ 2) := by
  let a : ℕ → ℝ := fun n => ‖(pqInv n : ℂ)‖ ^ 2
  have ha : Summable a := by
    have hsplit :=
      (summable_prod_of_nonneg (fun q : PQIndex => sq_nonneg ‖pqVWeight q‖)).mp
        pqVWeight_summable_sq
    exact (hsplit.1 false).congr fun n => by simp [a, pqVWeight]
  have haNorm : Summable (fun n => ‖a n‖) := by
    exact ha.congr fun n => by simp [a]
  have hp : Summable (fun q : ℕ × ℕ => a q.1 * a q.2) :=
    summable_mul_of_summable_norm haNorm haNorm
  have hpNorm : Summable (fun q : ℕ × ℕ => ‖a q.1 * a q.2‖) := by
    exact hp.congr fun q => by simp [a]
  let s : ℕ → ℝ := fun j => if j = k then 1 else 0
  have hsNorm : Summable (fun j => ‖s j‖) := by
    apply summable_of_ne_finset_zero (s := {k})
    intro j hj
    have hjk : j ≠ k := by simpa using hj
    simp [s, hjk]
  have hfull : Summable (fun q : (ℕ × ℕ) × ℕ =>
      (a q.1.1 * a q.1.2) * s q.2) :=
    summable_mul_of_summable_norm hpNorm hsNorm
  refine (countableWildWeightEquiv.summable_iff.mpr hfull).congr ?_
  rintro ⟨i, j, n⟩
  by_cases hj : j = k
  · subst j
    simp [countableWovenNormalWeight, countableWildWeightEquiv, a, s,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (pqInv_pos i), abs_of_pos (pqInv_pos n)]
    ring
  · simp [countableWovenNormalWeight, countableWildWeightEquiv, a, s, hj]

def countableWovenNormalVector (k : ℕ) : CountableWildHilbert :=
  ⟨countableWovenNormalWeight k,
    HilbertSchmidt.memℓp_of_sq (countableWovenNormalWeight_summable_sq k)⟩

theorem countableWovenNormalVector_mem (k : ℕ) :
    countableWovenNormalVector k ∈ countableWovenNormalSubspace := by
  rw [mem_countableWovenNormalSubspace_iff]
  intro i j n
  by_cases hj : j = k
  · subst j
    simp [countableWovenNormalVector, countableWovenNormalWeight, pqInv]
  · simp [countableWovenNormalVector, countableWovenNormalWeight, hj]

def countableWovenNormalVectorSub (k : ℕ) : countableWovenNormalSubspace :=
  ⟨countableWovenNormalVector k, countableWovenNormalVector_mem k⟩

def countableWovenNormalCoordinate (k : ℕ) :
    countableWovenNormalSubspace →ₗ[ℂ] ℂ :=
  (countableWildEval (0, (k, 0))).toLinearMap.comp
    countableWovenNormalSubspace.subtype

theorem countableWovenNormalVectorSub_linearIndependent :
    LinearIndependent ℂ countableWovenNormalVectorSub := by
  rw [linearIndependent_iff]
  intro l hl
  apply Finsupp.ext
  intro k
  have hk := congrArg (countableWovenNormalCoordinate k) hl
  rw [Finsupp.apply_linearCombination] at hk
  simpa [Finsupp.linearCombination_apply, countableWovenNormalCoordinate,
    countableWovenNormalVectorSub, countableWovenNormalVector,
    countableWovenNormalWeight, pqInv, Finsupp.sum] using hk

noncomputable def countableWovenNormalIsometry
    {u : CountableWildIndex → G} (hu : Orthonormal ℂ u) :
    countableWovenNormalSubspace →ₗᵢ[ℂ] G :=
  hu.orthogonalFamily.linearIsometry.comp countableWovenNormalSubspace.subtypeₗᵢ

def countableWovenNormalSpace
    {u : CountableWildIndex → G} (hu : Orthonormal ℂ u) : Submodule ℂ G :=
  LinearMap.range (countableWovenNormalIsometry hu).toLinearMap

theorem countableWovenNormalSpace_isClosed
    {u : CountableWildIndex → G} (hu : Orthonormal ℂ u) :
    IsClosed (countableWovenNormalSpace hu : Set G) := by
  letI : CompleteSpace countableWovenNormalSubspace :=
    countableWovenNormalSubspace_isClosed.completeSpace_coe
  exact (countableWovenNormalIsometry hu).isometry.isClosedEmbedding.isClosed_range

theorem countableWovenNormalIsometry_inner_left
    {u : CountableWildIndex → G} (hu : Orthonormal ℂ u)
    (z : countableWovenNormalSubspace) (q : CountableWildIndex) :
    inner ℂ (u q) (countableWovenNormalIsometry hu z) =
      (z : CountableWildHilbert) q := by
  exact orthonormalSynthesis_inner_left hu (z : CountableWildHilbert) q

theorem countableWovenNormalSpace_inf_adjointRange_eq_bot
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : G →L[ℂ] H) (i : ℕ)
    {u : CountableWildIndex → G} (hu : Orthonormal ℂ u)
    (hsmall : ∀ k n,
      ‖T (u (i, (k, n)))‖ < (pqInv i * pqInv n) ^ 2) :
    countableWovenNormalSpace hu ⊓ LinearMap.range T.adjoint.toLinearMap = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rcases hx.1 with ⟨z, hz⟩
  rcases hx.2 with ⟨y, hy⟩
  have hzy : countableWovenNormalIsometry hu z = T.adjoint y := hz.trans hy.symm
  have hrel :=
    (mem_countableWovenNormalSubspace_iff (z : CountableWildHilbert)).mp z.2
  have hcoeff : ∀ k : ℕ, (z : CountableWildHilbert) (0, (k, 0)) = 0 := by
    intro k
    by_contra hk
    have hz0 : z ≠ 0 := by
      intro hzzero
      apply hk
      rw [hzzero]
      rfl
    have hy0 : y ≠ 0 := by
      intro hyzero
      apply hz0
      apply (countableWovenNormalIsometry hu).injective
      rw [hzy, hyzero]
      simp
    have hcoord : ∀ n : ℕ,
        (z : CountableWildHilbert) (i, (k, n)) =
          inner ℂ (T (u (i, (k, n)))) y := by
      intro n
      calc
        (z : CountableWildHilbert) (i, (k, n)) =
            inner ℂ (u (i, (k, n))) (countableWovenNormalIsometry hu z) :=
          (countableWovenNormalIsometry_inner_left hu z (i, (k, n))).symm
        _ = inner ℂ (u (i, (k, n))) (T.adjoint y) := by rw [hzy]
        _ = inner ℂ (T (u (i, (k, n)))) y := T.adjoint_inner_right _ _
    have hbound : ∀ n : ℕ,
        ‖(z : CountableWildHilbert) (i, (k, n))‖ <
          (pqInv i * pqInv n) ^ 2 * ‖y‖ := by
      intro n
      rw [hcoord n]
      exact (norm_inner_le_norm _ _).trans_lt
        (mul_lt_mul_of_pos_right (hsmall k n) (norm_pos_iff.mpr hy0))
    have hnorm : ∀ n : ℕ,
        ‖(z : CountableWildHilbert) (i, (k, n))‖ =
          (pqInv i * pqInv n) *
            ‖(z : CountableWildHilbert) (0, (k, 0))‖ := by
      intro n
      rw [hrel i k n, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (pqInv_pos i), abs_of_pos (pqInv_pos n)]
    have ht : Filter.Tendsto
        (fun n : ℕ => pqInv n * (pqInv i * ‖y‖)) Filter.atTop (nhds 0) := by
      simpa using tendsto_pqInv_zero.mul_const (pqInv i * ‖y‖)
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        pqInv n * (pqInv i * ‖y‖) <
          ‖(z : CountableWildHilbert) (0, (k, 0))‖ :=
      ht.eventually (Iio_mem_nhds (norm_pos_iff.mpr hk))
    rcases Filter.eventually_atTop.mp hev with ⟨n, hn⟩
    have hsmallAt := hn n le_rfl
    have hboundAt := hbound n
    rw [hnorm n] at hboundAt
    have hfactor : 0 < pqInv i * pqInv n := mul_pos (pqInv_pos i) (pqInv_pos n)
    have hreverse : (pqInv i * pqInv n) ^ 2 * ‖y‖ <
        (pqInv i * pqInv n) *
          ‖(z : CountableWildHilbert) (0, (k, 0))‖ := by
      calc
        (pqInv i * pqInv n) ^ 2 * ‖y‖ =
            (pqInv i * pqInv n) * (pqInv n * (pqInv i * ‖y‖)) := by ring
        _ < (pqInv i * pqInv n) *
            ‖(z : CountableWildHilbert) (0, (k, 0))‖ :=
          mul_lt_mul_of_pos_left hsmallAt hfactor
    exact (not_lt_of_ge hreverse.le) hboundAt
  have hzzero : z = 0 := by
    apply Subtype.ext
    ext q
    rcases q with ⟨i', k, n⟩
    rw [hrel i' k n, hcoeff k, mul_zero]
    rfl
  rw [← hz, hzzero]
  exact (countableWovenNormalIsometry hu).map_zero

theorem countableWovenNormalSpace_has_countable_independent_family
    {u : CountableWildIndex → G} (hu : Orthonormal ℂ u) :
    ∃ v : ℕ → G, LinearIndependent ℂ v ∧
      ∀ k, v k ∈ countableWovenNormalSpace hu := by
  let V := countableWovenNormalIsometry hu
  let v : ℕ → G := fun k => V (countableWovenNormalVectorSub k)
  refine ⟨v, ?_, ?_⟩
  · have hker : LinearMap.ker V.toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr V.injective
    simpa [v, V, Function.comp_def] using
      countableWovenNormalVectorSub_linearIndependent.map' V.toLinearMap hker
  · intro k
    exact ⟨countableWovenNormalVectorSub k, rfl⟩

theorem dense_orthogonal_image_of_le_countableWovenNormalSpace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : G →L[ℂ] H) (hDense : DenseRange T)
    {u : CountableWildIndex → G} (hu : Orthonormal ℂ u)
    (hAvoid : countableWovenNormalSpace hu ⊓
      LinearMap.range T.adjoint.toLinearMap = ⊥)
    (L : Submodule ℂ G) (hLclosed : IsClosed (L : Set G))
    (hLD : L ≤ countableWovenNormalSpace hu) :
    Dense (Lᗮ.map T.toLinearMap : Set H) := by
  apply (dense_image_orthogonal_iff_inf_adjointRange_eq_bot
    T hDense L hLclosed).mpr
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxD : x ∈ countableWovenNormalSpace hu ⊓
      LinearMap.range T.adjoint.toLinearMap := ⟨hLD hx.1, hx.2⟩
  rw [hAvoid] at hxD
  exact hxD

theorem countable_singular_observer_wild_lattice
    {H : ℕ → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (T : ∀ i, G →L[ℂ] H i)
    (hTsing : ∀ i, HilbertRangeSingular (T i))
    (hTdense : ∀ i, DenseRange (T i)) :
    ∃ u : CountableWildIndex → G, ∃ hu : Orthonormal ℂ u,
      IsClosed (countableWovenNormalSpace hu : Set G) ∧
      (∀ i, countableWovenNormalSpace hu ⊓
        LinearMap.range (T i).adjoint.toLinearMap = ⊥) ∧
      (∃ v : ℕ → G, LinearIndependent ℂ v ∧
        ∀ k, v k ∈ countableWovenNormalSpace hu) ∧
      ∀ L : Submodule ℂ G, IsClosed (L : Set G) →
        L ≤ countableWovenNormalSpace hu →
          ∀ i, Dense (Lᗮ.map (T i).toLinearMap : Set (H i)) := by
  obtain ⟨u, hu, hsmall⟩ := exists_countable_singular_orthonormalArray T hTsing
  have hAvoid : ∀ i, countableWovenNormalSpace hu ⊓
      LinearMap.range (T i).adjoint.toLinearMap = ⊥ := fun i =>
    countableWovenNormalSpace_inf_adjointRange_eq_bot (T i) i hu (hsmall i)
  refine ⟨u, hu, countableWovenNormalSpace_isClosed hu, hAvoid,
    countableWovenNormalSpace_has_countable_independent_family hu, ?_⟩
  intro L hLclosed hLD i
  exact dense_orthogonal_image_of_le_countableWovenNormalSpace
    (T i) (hTdense i) hu (hAvoid i) L hLclosed hLD

theorem countable_noncoercive_observer_wild_lattice
    {H : ℕ → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (T : ∀ i, G →L[ℂ] H i)
    (hTinj : ∀ i, Function.Injective (T i))
    (hTdense : ∀ i, DenseRange (T i))
    (hnoncoercive : ∀ i, ¬ ∃ K : NNReal, AntilipschitzWith K (T i)) :
    ∃ u : CountableWildIndex → G, ∃ hu : Orthonormal ℂ u,
      IsClosed (countableWovenNormalSpace hu : Set G) ∧
      (∀ i, countableWovenNormalSpace hu ⊓
        LinearMap.range (T i).adjoint.toLinearMap = ⊥) ∧
      (∃ v : ℕ → G, LinearIndependent ℂ v ∧
        ∀ k, v k ∈ countableWovenNormalSpace hu) ∧
      ∀ L : Submodule ℂ G, IsClosed (L : Set G) →
        L ≤ countableWovenNormalSpace hu →
          ∀ i, Dense (Lᗮ.map (T i).toLinearMap : Set (H i)) := by
  apply countable_singular_observer_wild_lattice T
  · intro i
    exact (hilbertRangeSingular_iff_no_antilipschitz (T i) (hTinj i)).mpr
      (hnoncoercive i)
  · exact hTdense

theorem countable_coercive_observer_forces_trivial_common_defect
    {H : ℕ → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    (T : ∀ i, G →L[ℂ] H i) (hTinj : ∀ i, Function.Injective (T i))
    (M : Submodule ℂ G) (hMclosed : IsClosed (M : Set G))
    (hMdense : ∀ i, Dense (M.map (T i).toLinearMap : Set (H i)))
    (hcoercive : ∃ i, ∃ K : NNReal, AntilipschitzWith K (T i)) :
    M = ⊤ := by
  obtain ⟨i, K, hK⟩ := hcoercive
  exact closed_biDense_eq_top_of_antilipschitz
    (T i) (hTinj i) M hMclosed (hMdense i) hK

omit [CompleteSpace G] in
theorem countable_coercive_or_all_noncoercive
    {H : ℕ → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℂ (H i)]
    (T : ∀ i, G →L[ℂ] H i) :
    (∃ i, ∃ K : NNReal, AntilipschitzWith K (T i)) ∨
      ∀ i, ¬ ∃ K : NNReal, AntilipschitzWith K (T i) := by
  by_cases h : ∃ i, ∃ K : NNReal, AntilipschitzWith K (T i)
  · exact Or.inl h
  · exact Or.inr fun i hi => h ⟨i, hi⟩

theorem countable_observer_coercivity_wildness_law
    {H : ℕ → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (T : ∀ i, G →L[ℂ] H i)
    (hTinj : ∀ i, Function.Injective (T i))
    (hTdense : ∀ i, DenseRange (T i)) :
    ((∃ i, ∃ K : NNReal, AntilipschitzWith K (T i)) ∧
      ∀ M : Submodule ℂ G, IsClosed (M : Set G) →
        (∀ i, Dense (M.map (T i).toLinearMap : Set (H i))) → M = ⊤) ∨
    ((∀ i, ¬ ∃ K : NNReal, AntilipschitzWith K (T i)) ∧
      ∃ u : CountableWildIndex → G, ∃ hu : Orthonormal ℂ u,
        IsClosed (countableWovenNormalSpace hu : Set G) ∧
        (∀ i, countableWovenNormalSpace hu ⊓
          LinearMap.range (T i).adjoint.toLinearMap = ⊥) ∧
        (∃ v : ℕ → G, LinearIndependent ℂ v ∧
          ∀ k, v k ∈ countableWovenNormalSpace hu) ∧
        ∀ L : Submodule ℂ G, IsClosed (L : Set G) →
          L ≤ countableWovenNormalSpace hu →
            ∀ i, Dense (Lᗮ.map (T i).toLinearMap : Set (H i))) := by
  rcases countable_coercive_or_all_noncoercive T with hcoercive | hnoncoercive
  · refine Or.inl ⟨hcoercive, ?_⟩
    intro M hMclosed hMdense
    exact countable_coercive_observer_forces_trivial_common_defect
      T hTinj M hMclosed hMdense hcoercive
  · exact Or.inr ⟨hnoncoercive,
      countable_noncoercive_observer_wild_lattice
        T hTinj hTdense hnoncoercive⟩

theorem not_every_hilbertPreQuasiPair_is_quasi :
    ¬ ∀ plus minus : PQHilbert →ₗ.[ℂ] PQHilbert,
      HilbertPreQuasiPair plus minus → HilbertQuasiCompatibility plus minus := by
  intro h
  obtain ⟨plus, minus, hpre, hnquasi⟩ := exists_hilbertPreQuasiPair_not_quasi
  exact hnquasi (h plus minus hpre)

end RHTower
