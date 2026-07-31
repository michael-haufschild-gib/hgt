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

end RHTower

end
