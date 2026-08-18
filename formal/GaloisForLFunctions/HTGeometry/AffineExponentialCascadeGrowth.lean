/-
# The growth of an affine-exponential cascade

Each layer of the cascade multiplies the previous bound by a constant and exponentiates it, so a
length-`n` cascade of maps `w ↦ exp(α w + β)` has maximum modulus at most `exp_n(r^C)`.  The
bookkeeping is carried by two arithmetic facts about the iterated-exponential scale: raising the
exponent by one absorbs any additive constant (`eventually_iterExp_add_le`) and, once one
exponential is present, any multiplicative constant as well (`eventually_iterExp_mul_add_le`).

Consequently a length-`n` cascade cannot have growth height `n + 1`, which is the upper half of the
composition-depth statement for the affine-exponential family.
-/
import GaloisForLFunctions.HTGeometry.IteratedExponentialGrowthHeight
import GaloisForLFunctions.HTGeometry.AffineExponentialCascadeOrder

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

theorem iterExp_ge_self (m : ℕ) (x : ℝ) : x ≤ iterExp m x := by
  have := iterExp_mono_index (Nat.zero_le m) x
  rwa [iterExp_zero] at this

theorem tendsto_iterExp_rpow (m : ℕ) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun r : ℝ => iterExp m (r ^ C)) atTop atTop :=
  tendsto_atTop_mono (fun r => iterExp_ge_self m (r ^ C)) (tendsto_rpow_atTop hC)

/-- Raising the exponent by one absorbs any additive constant inside `k` exponentials. -/
theorem eventually_iterExp_add_le (m : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ K : ℝ, ∀ᶠ r : ℝ in atTop, iterExp m (r ^ C) + K ≤ iterExp m (r ^ (C + 1)) := by
  induction m with
  | zero =>
      intro K
      filter_upwards [eventually_ge_atTop (|K| + 1), eventually_ge_atTop (1 : ℝ),
        eventually_gt_atTop (0 : ℝ)] with r hrK hr1 hr0
      simp only [iterExp_zero]
      have hrc : (1 : ℝ) ≤ r ^ C := Real.one_le_rpow hr1 hC.le
      have hsplit : r ^ (C + 1) = r ^ C * r := by
        rw [Real.rpow_add hr0, Real.rpow_one]
      rw [hsplit]
      have h1 : r ^ C + K ≤ r ^ C + |K| * r ^ C := by
        have := le_abs_self K
        nlinarith [abs_nonneg K]
      have h2 : r ^ C + |K| * r ^ C = r ^ C * (1 + |K|) := by ring
      have h3 : r ^ C * (1 + |K|) ≤ r ^ C * r := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        linarith
      linarith [h1, h2.le, h3]
  | succ m ih =>
      intro K
      have h1 := ih 1
      have htend := tendsto_iterExp_rpow m hC
      have hK : ∀ᶠ r : ℝ in atTop,
          K ≤ Real.exp (iterExp m (r ^ C)) * (Real.exp 1 - 1) := by
        have hpos : (0 : ℝ) < Real.exp 1 - 1 := by
          have := Real.add_one_lt_exp (x := 1) (by norm_num)
          linarith
        have := (Real.tendsto_exp_atTop.comp htend).atTop_mul_const hpos
        exact this.eventually_ge_atTop K
      filter_upwards [h1, hK] with r hr hrK
      rw [iterExp_succ, iterExp_succ]
      calc Real.exp (iterExp m (r ^ C)) + K
          ≤ Real.exp (iterExp m (r ^ C))
            + Real.exp (iterExp m (r ^ C)) * (Real.exp 1 - 1) := by linarith
        _ = Real.exp (iterExp m (r ^ C) + 1) := by rw [Real.exp_add]; ring
        _ ≤ Real.exp (iterExp m (r ^ (C + 1))) := Real.exp_le_exp.mpr hr

/-- Raising the exponent by one absorbs any multiplicative constant inside `k` exponentials. -/
theorem eventually_iterExp_mul_add_le (m : ℕ) {C : ℝ} (hC : 0 < C) (A : ℝ) :
    ∀ᶠ r : ℝ in atTop, A * iterExp m (r ^ C) + A ≤ iterExp m (r ^ (C + 1)) := by
  induction m with
  | zero =>
      filter_upwards [eventually_ge_atTop (2 * |A| + 1), eventually_ge_atTop (1 : ℝ),
        eventually_gt_atTop (0 : ℝ)] with r hrA hr1 hr0
      simp only [iterExp_zero]
      have hrc : (1 : ℝ) ≤ r ^ C := Real.one_le_rpow hr1 hC.le
      have hsplit : r ^ (C + 1) = r ^ C * r := by
        rw [Real.rpow_add hr0, Real.rpow_one]
      rw [hsplit]
      have hA := le_abs_self A
      nlinarith [abs_nonneg A]
  | succ m ih =>
      have hlog : (0 : ℝ) ≤ Real.log (2 * |A| + 2) := by
        refine Real.log_nonneg ?_
        linarith [abs_nonneg A]
      have h1 := eventually_iterExp_add_le m hC (Real.log (2 * |A| + 2))
      have htend := tendsto_iterExp_rpow m hC
      have hX : ∀ᶠ r : ℝ in atTop, (0 : ℝ) ≤ iterExp m (r ^ C) := htend.eventually_ge_atTop 0
      filter_upwards [h1, hX] with r hr hX0
      rw [iterExp_succ, iterExp_succ]
      set X : ℝ := iterExp m (r ^ C) with hXdef
      have hexp1 : (1 : ℝ) ≤ Real.exp X := Real.one_le_exp hX0
      have hAbound : A * Real.exp X + A ≤ (2 * |A| + 2) * Real.exp X := by
        have h2 := le_abs_self A
        nlinarith [abs_nonneg A]
      have hfact : (2 * |A| + 2) * Real.exp X = Real.exp (X + Real.log (2 * |A| + 2)) := by
        rw [Real.exp_add, Real.exp_log (by linarith [abs_nonneg A])]
        ring
      calc A * Real.exp X + A ≤ (2 * |A| + 2) * Real.exp X := hAbound
        _ = Real.exp (X + Real.log (2 * |A| + 2)) := hfact
        _ ≤ Real.exp (iterExp m (r ^ (C + 1))) := Real.exp_le_exp.mpr hr


/-- **Growth bound for the exponential cascade.**  A length-`n` cascade of maps `w ↦ exp(α w + β)`
has maximum modulus at most an `n`-fold exponential of a power of the radius. -/
theorem exists_bound_entireCascade_expAffine (α β : ℕ → ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ r →
      ‖entireCascade (expAffine α β) n z‖ ≤ iterExp n (r ^ C) := by
  induction n with
  | zero =>
      refine ⟨1, one_pos, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr z hz
      rw [iterExp_zero, Real.rpow_one]
      simpa using hz
  | succ n ih =>
      obtain ⟨C, hC, hev⟩ := ih
      refine ⟨C + 1, by linarith, ?_⟩
      set A : ℝ := max ‖α n‖ ‖β n‖ with hA
      have hX0 : ∀ᶠ r : ℝ in atTop, (0 : ℝ) ≤ iterExp n (r ^ C) :=
        (tendsto_iterExp_rpow n hC).eventually_ge_atTop 0
      filter_upwards [hev, eventually_iterExp_mul_add_le n hC A, hX0] with r hr hmul hX0r z hz
      have hw : ‖entireCascade (expAffine α β) n z‖ ≤ iterExp n (r ^ C) := hr z hz
      have hstep : entireCascade (expAffine α β) (n + 1) z
          = Complex.exp (α n * entireCascade (expAffine α β) n z + β n) := rfl
      rw [hstep, Complex.norm_exp, iterExp_succ]
      refine Real.exp_le_exp.mpr (le_trans ?_ hmul)
      set w : ℂ := entireCascade (expAffine α β) n z with hwdef
      have h1 : (α n * w + β n).re ≤ ‖α n * w + β n‖ := Complex.re_le_norm _
      have h2 : ‖α n * w + β n‖ ≤ ‖α n‖ * ‖w‖ + ‖β n‖ := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul]
      have h3 : ‖α n‖ * ‖w‖ + ‖β n‖ ≤ A * iterExp n (r ^ C) + A := by
        have hαA : ‖α n‖ ≤ A := le_max_left _ _
        have hβA : ‖β n‖ ≤ A := le_max_right _ _
        have hA0 : 0 ≤ A := le_trans (norm_nonneg _) hαA
        have h4 : ‖α n‖ * ‖w‖ ≤ A * iterExp n (r ^ C) :=
          mul_le_mul hαA hw (norm_nonneg _) hA0
        linarith
      linarith

theorem growthHeightAtMost_entireCascade_expAffine (α β : ℕ → ℂ) (n : ℕ) :
    GrowthHeightAtMost (entireCascade (expAffine α β) n) n := by
  obtain ⟨C, _, hev⟩ := exists_bound_entireCascade_expAffine α β n
  exact ⟨C, hev⟩


/-- **Growth bound for the affine-exponential cascade.** -/
theorem growthHeightAtMost_affExpCascade (a b c : ℕ → ℂ) (m : ℕ) :
    GrowthHeightAtMost (entireCascade (affExp a b c) (m + 1)) (m + 1) := by
  obtain ⟨C, hC, hev⟩ :=
    exists_bound_entireCascade_expAffine (affExpAlpha b c) (affExpBeta a c) (m + 1)
  refine ⟨C + 1, ?_⟩
  set A : ℝ := max ‖a m‖ ‖b m‖ with hA
  have hX0 : ∀ᶠ r : ℝ in atTop, (0 : ℝ) ≤ iterExp (m + 1) (r ^ C) :=
    (tendsto_iterExp_rpow (m + 1) hC).eventually_ge_atTop 0
  filter_upwards [hev, eventually_iterExp_mul_add_le (m + 1) hC A, hX0] with r hr hmul hX0r z hz
  rw [entireCascade_affExp]
  set W : ℂ := entireCascade (expAffine (affExpAlpha b c) (affExpBeta a c)) (m + 1) z with hW
  have hWle : ‖W‖ ≤ iterExp (m + 1) (r ^ C) := hr z hz
  have hαA : ‖a m‖ ≤ A := le_max_left _ _
  have hβA : ‖b m‖ ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) hαA
  calc ‖a m + b m * W‖ ≤ ‖a m‖ + ‖b m‖ * ‖W‖ := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul]
    _ ≤ A * iterExp (m + 1) (r ^ C) + A := by
        have h4 : ‖b m‖ * ‖W‖ ≤ A * iterExp (m + 1) (r ^ C) :=
          mul_le_mul hβA hWle (norm_nonneg _) hA0
        linarith
    _ ≤ iterExp (m + 1) (r ^ (C + 1)) := hmul

/-- **No `(n+1)`-fold exponential growth for a length-`n` affine-exponential cascade.** -/
theorem not_growthHeightAtLeast_affExpCascade (a b c : ℕ → ℂ) (m : ℕ) :
    ¬ GrowthHeightAtLeast (entireCascade (affExp a b c) (m + 1)) (m + 2) :=
  not_growthHeightAtLeast_succ_of_atMost (growthHeightAtMost_affExpCascade a b c m)

end GaloisForLFunctions.HTGeometry
