import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed

/-!
# Approximation numbers for enumerated indexed diagonals

An equivalence `ℕ ≃ κ` orders an arbitrary countable coordinate family.  Truncating the first
`n` coordinates gives a rank-at-most-`n` diagonal operator.  For a nonnegative antitone multiplier,
the omitted diagonal has norm at most its `n`-th entry, yielding the approximation-number upper
bound needed for Schatten membership on non-`ℕ` index types.
-/

namespace HTGeometry

noncomputable section

/-- Retain the first `n` coordinates of a multiplier ordered by `e : ℕ ≃ κ`. -/
def equivTruncMultiplier {κ : Type*} (e : ℕ ≃ κ) (lam : κ → ℂ)
    (n : ℕ) : κ → ℂ :=
  fun i => if e.symm i < n then lam i else 0

theorem norm_equivTruncMultiplier_le {κ : Type*} (e : ℕ ≃ κ)
    {lam : κ → ℂ} {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (n : ℕ) (i : κ) :
    ‖equivTruncMultiplier e lam n i‖ ≤ C := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC (e 0))
  rw [equivTruncMultiplier]
  split_ifs
  · exact hC i
  · simpa using hC0

/-- The first-`n` truncation of an enumerated diagonal has rank at most `n`. -/
theorem hasRankLE_ellTwoDiagonal_equivTrunc {κ : Type*} [DecidableEq κ]
    (e : ℕ ≃ κ) (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (n : ℕ) :
    RHTower.HasRankLE
      (ellTwoDiagonal (equivTruncMultiplier e lam n)
        (norm_equivTruncMultiplier_le e hC n)) n := by
  classical
  refine ⟨Submodule.span ℂ (Set.range fun k : Fin n =>
      (lp.single 2 (e k) (1 : ℂ) : IndexedEllTwo κ)),
    ?_, ?_, ?_⟩
  · exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  · refine le_trans (finrank_span_le_card (R := ℂ) (Set.range fun k : Fin n =>
        (lp.single 2 (e k) (1 : ℂ) : IndexedEllTwo κ))) ?_
    rw [Set.toFinset_range]
    exact le_trans Finset.card_image_le (by simp)
  · intro f
    have hsum :
        ellTwoDiagonal (equivTruncMultiplier e lam n)
            (norm_equivTruncMultiplier_le e hC n) f =
          ∑ k : Fin n, (lam (e k) * f (e k)) •
            (lp.single 2 (e k) (1 : ℂ) : IndexedEllTwo κ) := by
      ext i
      rw [ellTwoDiagonal_apply, lp.coeFn_sum, Finset.sum_apply]
      simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
        Pi.single_apply, smul_eq_mul]
      by_cases hi : e.symm i < n
      · rw [Finset.sum_eq_single (⟨e.symm i, hi⟩ : Fin n)]
        · simp [equivTruncMultiplier, hi]
        · intro b _ hb
          have hne : i ≠ e b := by
            intro h
            apply hb
            apply Fin.ext
            simpa using (congrArg e.symm h).symm
          simp [hne]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · have hzero : ∀ b : Fin n, (i = e b) = False := by
          intro b
          simp only [eq_iff_iff, iff_false]
          intro h
          apply hi
          rw [h, e.symm_apply_apply]
          exact b.isLt
        simp [equivTruncMultiplier, hi, hzero]
    rw [hsum]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- Approximation numbers of an enumerated nonnegative antitone diagonal are bounded by the
corresponding ordered multiplier. -/
theorem approxNumber_ellTwoDiagonal_reindex_le {κ : Type*} [DecidableEq κ]
    (e : ℕ ≃ κ) (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) (n : ℕ) :
    RHTower.approxNumber
      (ellTwoDiagonal (fun i => ((r (e.symm i) : ℝ) : ℂ))
        (fun i => by
          simpa [Real.norm_eq_abs, abs_of_nonneg (hr _)] using
            hanti (Nat.zero_le (e.symm i)))) n ≤ r n := by
  let lam : κ → ℂ := fun i => ((r (e.symm i) : ℝ) : ℂ)
  let hC : ∀ i, ‖lam i‖ ≤ r 0 := fun i => by
    simpa [lam, Real.norm_eq_abs, abs_of_nonneg (hr _)] using
      hanti (Nat.zero_le (e.symm i))
  let F := ellTwoDiagonal (equivTruncMultiplier e lam n)
    (norm_equivTruncMultiplier_le e hC n)
  let tail : κ → ℂ := fun i => if n ≤ e.symm i then lam i else 0
  have htail : ∀ i, ‖tail i‖ ≤ r n := by
    intro i
    dsimp [tail]
    split_ifs with hi
    · simpa [lam, Real.norm_eq_abs, abs_of_nonneg (hr _)] using hanti hi
    · simpa using hr n
  have hsub : ellTwoDiagonal lam hC - F = ellTwoDiagonal tail htail := by
    ext f i
    change lam i * f i - equivTruncMultiplier e lam n i * f i = tail i * f i
    dsimp [tail, equivTruncMultiplier]
    by_cases hi : e.symm i < n
    · simp [hi, Nat.not_le.mpr hi]
    · simp [hi, Nat.le_of_not_gt hi]
  calc
    RHTower.approxNumber (ellTwoDiagonal lam hC) n ≤
        ‖ellTwoDiagonal lam hC - F‖ :=
      RHTower.approxNumber_le _ n _
        (hasRankLE_ellTwoDiagonal_equivTrunc e lam hC n)
    _ = ‖ellTwoDiagonal tail htail‖ := by rw [hsub]
    _ ≤ r n := norm_ellTwoDiagonal_le tail htail (hr n)

def lowEquivCoordinateSubspace {κ : Type*} [DecidableEq κ]
    (e : ℕ ≃ κ) (n : ℕ) : Submodule ℂ (IndexedEllTwo κ) :=
  Submodule.span ℂ
    (Set.range fun k : Fin n => ellTwoCoordinateBasis κ (e k))

theorem lowEquivCoordinateBasis_linearIndependent {κ : Type*} [DecidableEq κ]
    (e : ℕ ≃ κ) (n : ℕ) :
    LinearIndependent ℂ
      (fun k : Fin n => ellTwoCoordinateBasis κ (e k)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hi := congrArg (fun w : IndexedEllTwo κ => w (e i)) hc
  rw [lp.coeFn_sum, Finset.sum_apply] at hi
  simp only [lp.coeFn_smul, Pi.smul_apply, ellTwoCoordinateBasis_apply,
    smul_eq_mul] at hi
  rw [Finset.sum_eq_single i] at hi
  · simpa using hi
  · intro b _ hbi
    have hne : e (b : ℕ) ≠ e (i : ℕ) := by
      intro h
      exact hbi (Fin.ext (e.injective h))
    simp [hne]
  · intro hiMem
    exact absurd (Finset.mem_univ i) hiMem

theorem finrank_lowEquivCoordinateSubspace {κ : Type*} [DecidableEq κ]
    (e : ℕ ≃ κ) (n : ℕ) :
    Module.finrank ℂ (lowEquivCoordinateSubspace e n) = n := by
  rw [lowEquivCoordinateSubspace,
    finrank_span_eq_card (lowEquivCoordinateBasis_linearIndependent e n),
    Fintype.card_fin]

theorem lowEquivCoordinateSubspace_support {κ : Type*} [DecidableEq κ]
    {e : ℕ ≃ κ} {n : ℕ} {i : κ} {w : IndexedEllTwo κ}
    (hw : w ∈ lowEquivCoordinateSubspace e (n + 1))
    (hi : n < e.symm i) : w i = 0 := by
  rw [lowEquivCoordinateSubspace] at hw
  refine Submodule.span_induction (p := fun w _ => w i = 0) ?_ rfl ?_ ?_ hw
  · intro x hx
    rcases hx with ⟨k, rfl⟩
    have hne : i ≠ e k := by
      intro h
      have := congrArg e.symm h
      simp only [e.symm_apply_apply] at this
      omega
    simp [ellTwoCoordinateBasis_apply, hne]
  · intro x y _ _ hx hy
    simp [hx, hy]
  · intro c x _ hx
    simp [hx]

theorem le_norm_ellTwoDiagonal_of_equiv_support
    {κ : Type*} [DecidableEq κ] (e : ℕ ≃ κ)
    {lam : κ → ℂ} {r : ℕ → ℝ}
    (hmod : ∀ i, ‖lam i‖ = r (e.symm i))
    (hr : ∀ n, 0 ≤ r n)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i)
    {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (n : ℕ)
    (w : IndexedEllTwo κ) (hw : ∀ i, n < e.symm i → w i = 0) :
    r n * ‖w‖ ≤ ‖ellTwoDiagonal lam hC w‖ := by
  have hlhs : (0 : ℝ) ≤ r n * ‖w‖ :=
    mul_nonneg (hr n) (norm_nonneg _)
  have hrhs : (0 : ℝ) ≤ ‖ellTwoDiagonal lam hC w‖ := norm_nonneg _
  have htsumT : ‖ellTwoDiagonal lam hC w‖ ^ (2 : ℝ) =
      ∑' i, ‖(ellTwoDiagonal lam hC w) i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : κ => ℂ)
      (by norm_num) (ellTwoDiagonal lam hC w)
  have htsumw : ‖w‖ ^ (2 : ℝ) = ∑' i, ‖w i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : κ => ℂ)
      (by norm_num) w
  have hsumw : Summable fun i => ‖w i‖ ^ (2 : ℝ) :=
    (lp.memℓp w).summable (by norm_num)
  have hsumT : Summable fun i =>
      ‖(ellTwoDiagonal lam hC w) i‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ i, r n ^ (2 : ℝ) * ‖w i‖ ^ (2 : ℝ) ≤
      ‖(ellTwoDiagonal lam hC w) i‖ ^ (2 : ℝ) := by
    intro i
    by_cases hi : n < e.symm i
    · rw [ellTwoDiagonal_apply, hw i hi, mul_zero, norm_zero]
      simp
    · push Not at hi
      have hri : r n ≤ r (e.symm i) := hanti hi
      have hval : ‖(ellTwoDiagonal lam hC w) i‖ =
          r (e.symm i) * ‖w i‖ := by
        rw [ellTwoDiagonal_apply, norm_mul, hmod]
      rw [hval, Real.mul_rpow (hr _) (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hr n) hri (by norm_num))
        (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow : (r n * ‖w‖) ^ (2 : ℝ) ≤
      ‖ellTwoDiagonal lam hC w‖ ^ (2 : ℝ) := by
    rw [Real.mul_rpow (hr n) (norm_nonneg _), htsumw, htsumT,
      ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm (hsumw.mul_left _) hsumT
  have hx2 : (r n * ‖w‖) ^ (2 : ℝ) = (r n * ‖w‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hy2 : ‖ellTwoDiagonal lam hC w‖ ^ (2 : ℝ) =
      ‖ellTwoDiagonal lam hC w‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hlhs, Real.sqrt_sq hrhs] at hs

def equivTailMultiplier {κ : Type*} (e : ℕ ≃ κ) (lam : κ → ℂ)
    (n : ℕ) : κ → ℂ :=
  fun i => if n ≤ e.symm i then lam i else 0

theorem norm_equivTailMultiplier_le {κ : Type*} (e : ℕ ≃ κ)
    {lam : κ → ℂ} {r : ℕ → ℝ}
    (hmod : ∀ i, ‖lam i‖ = r (e.symm i))
    (hr : ∀ n, 0 ≤ r n)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i)
    (n : ℕ) (i : κ) : ‖equivTailMultiplier e lam n i‖ ≤ r n := by
  rw [equivTailMultiplier]
  split_ifs with hi
  · rw [hmod]
    exact hanti hi
  · simpa using hr n

theorem ellTwoDiagonal_sub_equivTrunc_eq_tail
    {κ : Type*} [DecidableEq κ] (e : ℕ ≃ κ)
    {lam : κ → ℂ} {r : ℕ → ℝ}
    (hmod : ∀ i, ‖lam i‖ = r (e.symm i))
    (hr : ∀ n, 0 ≤ r n)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) :
    ellTwoDiagonal lam (fun i => (hmod i).trans_le (hanti (Nat.zero_le _))) -
      ellTwoDiagonal (equivTruncMultiplier e lam n)
        (norm_equivTruncMultiplier_le e
          (fun i => (hmod i).trans_le (hanti (Nat.zero_le _))) n) =
      ellTwoDiagonal (equivTailMultiplier e lam n)
        (norm_equivTailMultiplier_le e hmod hr hanti n) := by
  ext f i
  change lam i * f i - equivTruncMultiplier e lam n i * f i =
    equivTailMultiplier e lam n i * f i
  dsimp [equivTruncMultiplier, equivTailMultiplier]
  by_cases hi : e.symm i < n
  · simp [hi, Nat.not_le.mpr hi]
  · simp [hi, Nat.le_of_not_gt hi]

theorem norm_ellTwoDiagonal_sub_equivTrunc
    {κ : Type*} [DecidableEq κ] (e : ℕ ≃ κ)
    {lam : κ → ℂ} {r : ℕ → ℝ}
    (hmod : ∀ i, ‖lam i‖ = r (e.symm i))
    (hr : ∀ n, 0 ≤ r n)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) (n : ℕ) :
    ‖ellTwoDiagonal lam (fun i => (hmod i).trans_le (hanti (Nat.zero_le _))) -
      ellTwoDiagonal (equivTruncMultiplier e lam n)
        (norm_equivTruncMultiplier_le e
          (fun i => (hmod i).trans_le (hanti (Nat.zero_le _))) n)‖ = r n := by
  rw [ellTwoDiagonal_sub_equivTrunc_eq_tail e hmod hr hanti]
  apply le_antisymm
  · exact norm_ellTwoDiagonal_le _ _ (hr n)
  · have hpoint := le_norm_ellTwoDiagonal
      (equivTailMultiplier e lam n)
      (norm_equivTailMultiplier_le e hmod hr hanti n) (e n)
    simpa [equivTailMultiplier, hmod, hr n] using hpoint

theorem approxNumber_ellTwoDiagonal_reindex_eq
    {κ : Type*} [DecidableEq κ] (e : ℕ ≃ κ)
    {lam : κ → ℂ} {r : ℕ → ℝ}
    (hmod : ∀ i, ‖lam i‖ = r (e.symm i))
    (hr : ∀ n, 0 ≤ r n)
    (hanti : ∀ {i j : ℕ}, i ≤ j → r j ≤ r i) (n : ℕ) :
    RHTower.approxNumber
      (ellTwoDiagonal lam
        (fun i => (hmod i).trans_le (hanti (Nat.zero_le _)))) n = r n := by
  let W := lowEquivCoordinateSubspace e (n + 1)
  letI : FiniteDimensional ℂ W :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let hC : ∀ i, ‖lam i‖ ≤ r 0 :=
    fun i => (hmod i).trans_le (hanti (Nat.zero_le _))
  let F := ellTwoDiagonal (equivTruncMultiplier e lam n)
    (norm_equivTruncMultiplier_le e hC n)
  refine RHTower.approxNumber_eq_of_subspace_of_hasRankLE W ?_ ?_ F ?_ ?_
  · rw [show Module.finrank ℂ W = n + 1 by
      simpa [W] using finrank_lowEquivCoordinateSubspace e (n + 1)]
  · intro w hw
    exact le_norm_ellTwoDiagonal_of_equiv_support e hmod hr hanti hC n w
      (fun i hi => lowEquivCoordinateSubspace_support hw hi)
  · simpa [F] using hasRankLE_ellTwoDiagonal_equivTrunc e lam hC n
  · simpa [F, hC] using norm_ellTwoDiagonal_sub_equivTrunc e hmod hr hanti n

theorem ellTwoDiagonal_equivTrunc_apply_eq_sum
    {κ : Type*} [DecidableEq κ] (e : ℕ ≃ κ) (lam : κ → ℂ)
    {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (n : ℕ) (f : IndexedEllTwo κ) :
    ellTwoDiagonal (equivTruncMultiplier e lam n)
        (norm_equivTruncMultiplier_le e hC n) f =
      ∑ k : Fin n, (lam (e k) * f (e k)) •
        ellTwoCoordinateBasis κ (e k) := by
  ext i
  rw [ellTwoDiagonal_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, ellTwoCoordinateBasis_apply,
    smul_eq_mul]
  by_cases hi : e.symm i < n
  · rw [Finset.sum_eq_single (⟨e.symm i, hi⟩ : Fin n)]
    · simp [equivTruncMultiplier, hi]
    · intro b _ hb
      have hne : i ≠ e b := by
        intro h
        apply hb
        apply Fin.ext
        simpa using (congrArg e.symm h).symm
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hzero : ∀ b : Fin n, (i = e b) = False := by
      intro b
      simp only [eq_iff_iff, iff_false]
      intro h
      apply hi
      rw [h, e.symm_apply_apply]
      exact b.isLt
    simp [equivTruncMultiplier, hi, hzero]

theorem range_ellTwoDiagonal_equivTrunc
    {κ : Type*} [DecidableEq κ] (e : ℕ ≃ κ) (lam : κ → ℂ)
    {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (n : ℕ)
    (hne : ∀ k : Fin n, lam (e k) ≠ 0) :
    LinearMap.range
        (ellTwoDiagonal (equivTruncMultiplier e lam n)
          (norm_equivTruncMultiplier_le e hC n)).toLinearMap =
      lowEquivCoordinateSubspace e n := by
  apply le_antisymm
  · rintro y ⟨f, rfl⟩
    change ellTwoDiagonal (equivTruncMultiplier e lam n)
        (norm_equivTruncMultiplier_le e hC n) f ∈
      lowEquivCoordinateSubspace e n
    rw [ellTwoDiagonal_equivTrunc_apply_eq_sum e lam hC n f]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [lowEquivCoordinateSubspace]
    refine Submodule.span_le.2 ?_
    rintro y ⟨k, rfl⟩
    refine ⟨(lam (e k))⁻¹ • ellTwoCoordinateBasis κ (e k), ?_⟩
    rw [map_smul]
    change (lam (e k))⁻¹ •
        (ellTwoDiagonal (equivTruncMultiplier e lam n)
          (norm_equivTruncMultiplier_le e hC n)
          (ellTwoCoordinateBasis κ (e k))) =
      ellTwoCoordinateBasis κ (e k)
    rw [ellTwoDiagonal_coordinateBasis]
    change (lam (e k))⁻¹ •
        (equivTruncMultiplier e lam n (e k) •
          ellTwoCoordinateBasis κ (e k)) =
      ellTwoCoordinateBasis κ (e k)
    simp [equivTruncMultiplier, e.symm_apply_apply, k.isLt, hne k]

theorem finrank_range_ellTwoDiagonal_equivTrunc
    {κ : Type*} [DecidableEq κ] (e : ℕ ≃ κ) (lam : κ → ℂ)
    {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (n : ℕ)
    (hne : ∀ k : Fin n, lam (e k) ≠ 0) :
    Module.finrank ℂ
      (LinearMap.range
        (ellTwoDiagonal (equivTruncMultiplier e lam n)
          (norm_equivTruncMultiplier_le e hC n)).toLinearMap) = n := by
  rw [range_ellTwoDiagonal_equivTrunc e lam hC n hne,
    finrank_lowEquivCoordinateSubspace]

end

end HTGeometry
