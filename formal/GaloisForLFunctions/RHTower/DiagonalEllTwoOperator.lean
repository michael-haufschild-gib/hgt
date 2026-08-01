import GaloisForLFunctions.RHTower.FiniteRankOperatorAlgebra

/-!
# Diagonal operators on the square-summable sequence space

The approximation-number sandwich needs a concrete operator whose approximation numbers can be
read off.  The canonical one is diagonal on `ℓ²(ℕ)`, and the corpus had no such operator: nothing
constructed a bounded operator on that space at all.

Here the diagonal multiplication by a bounded sequence is built end to end: square-summability is
preserved by comparison with the multiplier bound, the map is linear, its operator norm is at most
the multiplier bound, and it is therefore a bounded operator on the space.
-/

open scoped ENNReal

noncomputable section

namespace RHTower

/-- The square-summable complex sequence space. -/
abbrev EllTwo := lp (fun _ : ℕ => ℂ) 2

/-- Multiplying a square-summable sequence by a bounded sequence keeps it square summable. -/
theorem memℓp_diagonal {lam : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) (f : EllTwo) :
    Memℓp (fun n => lam n * f n) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun n => ‖f n‖ ^ (2 : ℝ) := (lp.memℓp f).summable (by norm_num)
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (C ^ (2 : ℝ)))
  intro n
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) (hC n) (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) 2)

/-- Diagonal multiplication by a bounded sequence, as a linear map. -/
def diagonalLinearMap (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) :
    EllTwo →ₗ[ℂ] EllTwo where
  toFun f := ⟨fun n => lam n * f n, memℓp_diagonal hC f⟩
  map_add' := by
    intro f g
    ext n
    simp [mul_add]
  map_smul' := by
    intro c f
    ext n
    simp [mul_left_comm]

@[simp] theorem diagonalLinearMap_apply (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C)
    (f : EllTwo) (n : ℕ) :
    (diagonalLinearMap lam hC f : ℕ → ℂ) n = lam n * f n := rfl

/-- The diagonal map is bounded by the multiplier bound. -/
theorem norm_diagonalLinearMap_le (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) (f : EllTwo) :
    ‖diagonalLinearMap lam hC f‖ ≤ C * ‖f‖ := by
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hnn : (0 : ℝ) ≤ ‖diagonalLinearMap lam hC f‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ C * ‖f‖ := mul_nonneg hCnn (norm_nonneg _)
  have htsumD : ‖diagonalLinearMap lam hC f‖ ^ (2 : ℝ)
      = ∑' n, ‖(diagonalLinearMap lam hC f) n‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ => ℂ) (by norm_num)
      (diagonalLinearMap lam hC f)
  have htsumf : ‖f‖ ^ (2 : ℝ) = ∑' n, ‖f n‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ => ℂ) (by norm_num) f
  have hsumf : Summable fun n => ‖f n‖ ^ (2 : ℝ) := (lp.memℓp f).summable (by norm_num)
  have hsumD : Summable fun n => ‖(diagonalLinearMap lam hC f) n‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ n, ‖(diagonalLinearMap lam hC f) n‖ ^ (2 : ℝ)
      ≤ C ^ (2 : ℝ) * ‖f n‖ ^ (2 : ℝ) := by
    intro n
    rw [diagonalLinearMap_apply, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (hC n) (by norm_num))
      (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow : ‖diagonalLinearMap lam hC f‖ ^ (2 : ℝ) ≤ (C * ‖f‖) ^ (2 : ℝ) := by
    rw [htsumD, Real.mul_rpow hCnn (norm_nonneg _), htsumf, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumD (hsumf.mul_left (C ^ (2 : ℝ)))
  have hx2 : ‖diagonalLinearMap lam hC f‖ ^ (2 : ℝ)
      = ‖diagonalLinearMap lam hC f‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hy2 : (C * ‖f‖) ^ (2 : ℝ) = (C * ‖f‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs] at hs

/-- Diagonal multiplication by a bounded sequence, as a bounded operator. -/
def diagonalOperator (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) :
    EllTwo →L[ℂ] EllTwo :=
  LinearMap.mkContinuous (diagonalLinearMap lam hC) C (norm_diagonalLinearMap_le lam hC)

@[simp] theorem diagonalOperator_apply (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C)
    (f : EllTwo) (n : ℕ) :
    (diagonalOperator lam hC f) n = lam n * f n := rfl

theorem norm_diagonalOperator_le (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) :
    ‖diagonalOperator lam hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (le_trans (norm_nonneg _) (hC 0)) _

/-- The diagonal operator acts on a coordinate vector by its multiplier. -/
@[simp] theorem diagonalOperator_single (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) (m : ℕ) :
    diagonalOperator lam hC (lp.single 2 m (1 : ℂ)) = lp.single 2 m (lam m) := by
  ext n
  rw [diagonalOperator_apply]
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h
    rw [mul_one]
  · rw [mul_zero]

/-- Every multiplier value is bounded by the operator norm. -/
theorem le_norm_diagonalOperator (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) (m : ℕ) :
    ‖lam m‖ ≤ ‖diagonalOperator lam hC‖ := by
  have hone : ‖(lp.single 2 m (1 : ℂ) : EllTwo)‖ = 1 := by
    rw [lp.norm_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) m (1 : ℂ)]
    simp
  have hval : ‖diagonalOperator lam hC (lp.single 2 m (1 : ℂ))‖ = ‖lam m‖ := by
    rw [diagonalOperator_single,
      lp.norm_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) m (lam m)]
  have hop := (diagonalOperator lam hC).le_opNorm (lp.single 2 m (1 : ℂ))
  rw [hval, hone, mul_one] at hop
  exact hop

/-- **The operator norm of a diagonal operator is the supremum of its multipliers**, whenever that
supremum is attained. -/
theorem norm_diagonalOperator_eq (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) {m : ℕ}
    (hm : ‖lam m‖ = C) :
    ‖diagonalOperator lam hC‖ = C :=
  le_antisymm (norm_diagonalOperator_le lam hC) (hm ▸ le_norm_diagonalOperator lam hC m)

/-! ## Coordinate truncation -/

/-- The span of finitely many vectors has dimension at most their number. -/
theorem finrank_span_range_le (n : ℕ) (v : Fin n → EllTwo) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range v)) ≤ n := by
  classical
  refine le_trans (finrank_span_le_card (R := ℂ) (Set.range v)) ?_
  rw [Set.toFinset_range]
  exact le_trans Finset.card_image_le (by simp)

/-- The `n`-th coordinate truncation of a multiplier sequence. -/
def truncMultiplier (lam : ℕ → ℂ) (n : ℕ) : ℕ → ℂ :=
  fun k => if k < n then lam k else 0

theorem norm_truncMultiplier_le {lam : ℕ → ℂ} {C : ℝ} (hC : ∀ k, ‖lam k‖ ≤ C) (n k : ℕ) :
    ‖truncMultiplier lam n k‖ ≤ C := by
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  rw [truncMultiplier]
  split_ifs with h
  · exact hC k
  · simpa using hCnn

/-- The truncated diagonal operator is the finite combination of the first `n` coordinate
vectors, hence has rank at most `n`. -/
theorem hasRankLE_diagonalOperator_trunc (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ k, ‖lam k‖ ≤ C) (n : ℕ) :
    HasRankLE (diagonalOperator (truncMultiplier lam n) (norm_truncMultiplier_le hC n)) n := by
  classical
  refine ⟨Submodule.span ℂ (Set.range fun k : Fin n => (lp.single 2 (k : ℕ) (1 : ℂ) : EllTwo)),
    ?_, finrank_span_range_le n _, ?_⟩
  · exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  · intro f
    have hsum :
        diagonalOperator (truncMultiplier lam n) (norm_truncMultiplier_le hC n) f
          = ∑ k : Fin n,
              (lam (k : ℕ) * f (k : ℕ)) • (lp.single 2 (k : ℕ) (1 : ℂ) : EllTwo) := by
      ext m
      rw [diagonalOperator_apply, lp.coeFn_sum, Finset.sum_apply]
      simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
      by_cases hm : m < n
      · rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin n)]
        · simp [truncMultiplier, hm]
        · intro b _ hb
          have : m ≠ (b : ℕ) := by
            intro h
            exact hb (Fin.ext h.symm)
          simp [this]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · have hzero : ∀ b : Fin n, (m = (b : ℕ)) = False := by
          intro b
          simp only [eq_iff_iff, iff_false]
          intro h
          exact hm (h ▸ b.isLt)
        simp [truncMultiplier, hm, hzero]
    rw [hsum]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-! ## Uniform expansion on the truncated coordinates -/

/-- **The multiplier expands the low coordinates.**  For an antitone nonnegative real multiplier, a
vector supported on the first `n + 1` coordinates is expanded by at least `r n`. -/
theorem le_norm_diagonalOperator_of_support
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) {C : ℝ}
    (hC : ∀ k, ‖((r k : ℝ) : ℂ)‖ ≤ C) (n : ℕ) (w : EllTwo) (hw : ∀ k, n < k → w k = 0) :
    r n * ‖w‖ ≤ ‖diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w‖ := by
  have hlhs : (0 : ℝ) ≤ r n * ‖w‖ := mul_nonneg (hr n) (norm_nonneg _)
  have hrhs : (0 : ℝ) ≤ ‖diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w‖ := norm_nonneg _
  have htsumT : ‖diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w‖ ^ (2 : ℝ)
      = ∑' k, ‖(diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w) k‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ => ℂ) (by norm_num)
      (diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w)
  have htsumw : ‖w‖ ^ (2 : ℝ) = ∑' k, ‖w k‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ => ℂ) (by norm_num) w
  have hsumw : Summable fun k => ‖w k‖ ^ (2 : ℝ) := (lp.memℓp w).summable (by norm_num)
  have hsumT : Summable fun k =>
      ‖(diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w) k‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ k, r n ^ (2 : ℝ) * ‖w k‖ ^ (2 : ℝ)
      ≤ ‖(diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w) k‖ ^ (2 : ℝ) := by
    intro k
    by_cases hk : n < k
    · rw [diagonalOperator_apply, hw k hk, mul_zero, norm_zero]
      simp
    · push Not at hk
      have hrk : r n ≤ r k := hanti hk
      have hval : ‖(diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w) k‖ = r k * ‖w k‖ := by
        rw [diagonalOperator_apply, norm_mul]
        congr 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr k)]
      rw [hval, Real.mul_rpow (hr k) (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hr n) hrk (by norm_num))
        (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow : (r n * ‖w‖) ^ (2 : ℝ)
      ≤ ‖diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w‖ ^ (2 : ℝ) := by
    rw [Real.mul_rpow (hr n) (norm_nonneg _), htsumw, htsumT, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm (hsumw.mul_left _) hsumT
  have hx2 : (r n * ‖w‖) ^ (2 : ℝ) = (r n * ‖w‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hy2 : ‖diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w‖ ^ (2 : ℝ)
      = ‖diagonalOperator (fun k => ((r k : ℝ) : ℂ)) hC w‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hlhs, Real.sqrt_sq hrhs] at hs

/-! ## Exact approximation numbers -/

/-- Subspace spanned by the first `n` coordinate vectors. -/
def lowCoordinateSubspace (n : ℕ) : Submodule ℂ EllTwo :=
  Submodule.span ℂ (Set.range fun k : Fin n => (lp.single 2 (k : ℕ) (1 : ℂ) : EllTwo))

/-- Coordinate vectors with distinct indices are linearly independent. -/
theorem lowCoordinateSingles_linearIndependent (n : ℕ) :
    LinearIndependent ℂ
      (fun k : Fin n => (lp.single 2 (k : ℕ) (1 : ℂ) : EllTwo)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hi := congrArg (fun w : EllTwo => w (i : ℕ)) hc
  rw [lp.coeFn_sum, Finset.sum_apply] at hi
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply,
    smul_eq_mul] at hi
  simpa [Fin.val_inj] using hi

/-- The first `n` coordinate vectors span an exactly `n`-dimensional subspace. -/
theorem finrank_lowCoordinateSubspace (n : ℕ) :
    Module.finrank ℂ (lowCoordinateSubspace n) = n := by
  rw [lowCoordinateSubspace, finrank_span_eq_card (lowCoordinateSingles_linearIndependent n),
    Fintype.card_fin]

/-- A vector in the first `n + 1` coordinate span vanishes above coordinate `n`. -/
theorem lowCoordinateSubspace_support {n k : ℕ} {w : EllTwo}
    (hw : w ∈ lowCoordinateSubspace (n + 1)) (hk : n < k) : w k = 0 := by
  rw [lowCoordinateSubspace] at hw
  refine Submodule.span_induction (p := fun w _ => w k = 0) ?_ rfl ?_ ?_ hw
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    simp [lp.single_apply, show k ≠ (i : ℕ) by omega]
  · intro x y _ _ hx hy
    simp [hx, hy]
  · intro c x _ hx
    simp [hx]

/-- Tail left after truncating the first `n` coordinates. -/
def tailMultiplier (r : ℕ → ℝ) (n : ℕ) (k : ℕ) : ℂ :=
  if n ≤ k then (r k : ℂ) else 0

theorem norm_tailMultiplier_le {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) (n k : ℕ) :
    ‖tailMultiplier r n k‖ ≤ r n := by
  rw [tailMultiplier]
  split_ifs with h
  · simpa [Real.norm_eq_abs, abs_of_nonneg (hr k)] using hanti h
  · simpa using hr n

/-- Subtracting the first-`n` coordinate truncation leaves exactly the tail multiplier. -/
theorem diagonalOperator_sub_trunc_eq_tail
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) (n : ℕ) :
    diagonalOperator (fun k => ((r k : ℝ) : ℂ))
        (fun k => by simpa [Real.norm_eq_abs, abs_of_nonneg (hr k)] using hanti (Nat.zero_le k)) -
      diagonalOperator (truncMultiplier (fun k => ((r k : ℝ) : ℂ)) n)
        (norm_truncMultiplier_le
          (fun k => by simpa [Real.norm_eq_abs, abs_of_nonneg (hr k)] using hanti (Nat.zero_le k)) n) =
      diagonalOperator (tailMultiplier r n) (norm_tailMultiplier_le hr hanti n) := by
  apply ContinuousLinearMap.ext
  intro f
  ext k
  simp only [sub_apply, diagonalOperator_apply]
  by_cases hk : k < n
  · simp [truncMultiplier, tailMultiplier, hk, Nat.not_le.mpr hk]
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    simp [truncMultiplier, tailMultiplier, hk, hnk]

/-- The distance from a nonnegative antitone diagonal to its first-`n` truncation is `r n`. -/
theorem norm_diagonalOperator_sub_trunc
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) (n : ℕ) :
    ‖diagonalOperator (fun k => ((r k : ℝ) : ℂ))
        (fun k => by simpa [Real.norm_eq_abs, abs_of_nonneg (hr k)] using hanti (Nat.zero_le k)) -
      diagonalOperator (truncMultiplier (fun k => ((r k : ℝ) : ℂ)) n)
        (norm_truncMultiplier_le
          (fun k => by simpa [Real.norm_eq_abs, abs_of_nonneg (hr k)] using hanti (Nat.zero_le k)) n)‖ =
      r n := by
  rw [diagonalOperator_sub_trunc_eq_tail hr hanti n]
  apply norm_diagonalOperator_eq (m := n)
  simp [tailMultiplier, hr n, Real.norm_eq_abs]

/-- **Exact diagonal approximation-number law.**  For a nonnegative antitone diagonal multiplier,
the `n`-th approximation number is exactly its `n`-th diagonal value. -/
theorem approxNumber_diagonalOperator_eq
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) (n : ℕ) :
    approxNumber
      (diagonalOperator (fun k => ((r k : ℝ) : ℂ))
        (fun k => by simpa [Real.norm_eq_abs, abs_of_nonneg (hr k)] using hanti (Nat.zero_le k))) n =
      r n := by
  let W := lowCoordinateSubspace (n + 1)
  letI : FiniteDimensional ℂ W :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let hC : ∀ k, ‖(((r k : ℝ) : ℂ))‖ ≤ r 0 := fun k => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hr k)] using hanti (Nat.zero_le k)
  let F := diagonalOperator (truncMultiplier (fun k => ((r k : ℝ) : ℂ)) n)
    (norm_truncMultiplier_le hC n)
  refine approxNumber_eq_of_subspace_of_hasRankLE W ?_ ?_ F ?_ ?_
  · rw [show Module.finrank ℂ W = n + 1 by
      simpa [W] using finrank_lowCoordinateSubspace (n + 1)]
  · intro w hw
    exact le_norm_diagonalOperator_of_support hr hanti _ n w
      (fun k hk => lowCoordinateSubspace_support hw hk)
  · simpa [F] using
      (hasRankLE_diagonalOperator_trunc (fun k => ((r k : ℝ) : ℂ)) hC n)
  · simpa [F] using norm_diagonalOperator_sub_trunc hr hanti n

/-- Canonical diagonal operator attached to a nonnegative antitone real sequence. -/
def antitoneDiagonalOperator (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) : EllTwo →L[ℂ] EllTwo :=
  diagonalOperator (fun k => ((r k : ℝ) : ℂ))
    (fun k => by simpa [Real.norm_eq_abs, abs_of_nonneg (hr k)] using hanti (Nat.zero_le k))

theorem approxNumber_antitoneDiagonalOperator_eq
    (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) (n : ℕ) :
    approxNumber (antitoneDiagonalOperator r hr hanti) n = r n := by
  simpa [antitoneDiagonalOperator] using approxNumber_diagonalOperator_eq hr hanti n

/-! ## Canonical critical-residue model -/

/-- Critical diagonal scale with exponent `p` and prescribed positive residue `c`. -/
def criticalDiagonalMultiplier (p c : ℝ) (n : ℕ) : ℝ :=
  (c / ((n : ℝ) + 1)) ^ (1 / p)

theorem criticalDiagonalMultiplier_nonneg (p c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ criticalDiagonalMultiplier p c n :=
  Real.rpow_nonneg (div_nonneg hc (by positivity)) _

theorem criticalDiagonalMultiplier_antitone {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) :
    ∀ {i j : ℕ}, i ≤ j →
      criticalDiagonalMultiplier p c j ≤ criticalDiagonalMultiplier p c i := by
  intro i j hij
  apply Real.rpow_le_rpow
  · positivity
  · apply div_le_div_of_nonneg_left hc
    · positivity
    · exact_mod_cast Nat.add_le_add_right hij 1
  · positivity

theorem criticalDiagonalMultiplier_rpow_mul_succ {p c : ℝ} (hp : 0 < p) (hc : 0 < c)
    (n : ℕ) :
    criticalDiagonalMultiplier p c n ^ p * ((n : ℝ) + 1) = c := by
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbase : 0 ≤ c / ((n : ℝ) + 1) := div_nonneg hc.le hnpos.le
  rw [criticalDiagonalMultiplier, ← Real.rpow_mul hbase]
  have hexp : 1 / p * p = 1 := by field_simp
  rw [hexp, Real.rpow_one, div_mul_cancel₀ c hnpos.ne']

/-- Canonical operator with approximation numbers `(c/(n+1))^(1/p)`. -/
def criticalDiagonalOperator (p c : ℝ) (hp : 0 < p) (hc : 0 < c) : EllTwo →L[ℂ] EllTwo :=
  antitoneDiagonalOperator (criticalDiagonalMultiplier p c)
    (criticalDiagonalMultiplier_nonneg p c hc.le)
    (criticalDiagonalMultiplier_antitone hp hc.le)

theorem approxNumber_criticalDiagonalOperator_eq (p c : ℝ) (hp : 0 < p) (hc : 0 < c)
    (n : ℕ) :
    approxNumber (criticalDiagonalOperator p c hp hc) n = criticalDiagonalMultiplier p c n := by
  simpa [criticalDiagonalOperator] using
    approxNumber_antitoneDiagonalOperator_eq (criticalDiagonalMultiplier p c)
      (criticalDiagonalMultiplier_nonneg p c hc.le)
      (criticalDiagonalMultiplier_antitone hp hc.le) n

/-- **Universal positive-residue realization.**  Every positive exponent and positive constant are
realized exactly by approximation numbers of one diagonal `ℓ²` operator. -/
theorem tendsto_criticalDiagonalOperator_approxNumber_rpow_mul_succ
    (p c : ℝ) (hp : 0 < p) (hc : 0 < c) :
    Filter.Tendsto
      (fun n : ℕ => approxNumber (criticalDiagonalOperator p c hp hc) n ^ p * ((n : ℝ) + 1))
      Filter.atTop (nhds c) := by
  have hfun :
      (fun n : ℕ => approxNumber (criticalDiagonalOperator p c hp hc) n ^ p * ((n : ℝ) + 1)) =
        fun _ : ℕ => c := by
    funext n
    rw [approxNumber_criticalDiagonalOperator_eq, criticalDiagonalMultiplier_rpow_mul_succ hp hc]
  rw [hfun]
  exact tendsto_const_nhds

end RHTower

end
