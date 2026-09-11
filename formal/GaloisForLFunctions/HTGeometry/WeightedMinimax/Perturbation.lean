import GaloisForLFunctions.HTGeometry.WeightedMinimax.SignRealization

/-!
# The improving perturbation

If a polynomial `g` has, at every extreme point of `T`, the same sign as `T`, then subtracting a
small multiple of `g` strictly decreases the weighted supremum. Consequently a monic minimizer
admits no such `g` of degree below its own: this is the analytic half of the weighted alternation
theorem.
-/

namespace GaloisForLFunctions.HTGeometry.WeightedMinimax

noncomputable section
open Set Polynomial

variable {v : ℝ → ℝ} {a b : ℝ}

/-- The points of `Icc a b` at which the weighted supremum of `R` is attained. -/
def extremeSet (v : ℝ → ℝ) (a b : ℝ) (R : Polynomial ℝ) : Set ℝ :=
  Set.Icc a b ∩ {x | v x * |R.eval x| = wsup v a b R}

theorem extremeSet_subset (R : Polynomial ℝ) : extremeSet v a b R ⊆ Set.Icc a b :=
  Set.inter_subset_left

theorem extremeSet_nonempty (hw : IsWeight v a b) (R : Polynomial ℝ) :
    (extremeSet v a b R).Nonempty := by
  obtain ⟨x, hx, he⟩ := wsup_attained hw R
  exact ⟨x, hx, he.symm⟩

theorem extremeSet_isCompact (hw : IsWeight v a b) (R : Polynomial ℝ) :
    IsCompact (extremeSet v a b R) :=
  isCompact_Icc.inter_right
    (isClosed_eq (hw.cont.mul (Polynomial.continuous R).abs) continuous_const)

theorem pos_of_mem_extremeSet (hw : IsWeight v a b) {R : Polynomial ℝ} (hR : R ≠ 0)
    {x : ℝ} (hx : x ∈ extremeSet v a b R) : 0 < v x ∧ R.eval x ≠ 0 := by
  have hpos : 0 < wsup v a b R := wsup_pos hw hR
  have he : v x * |R.eval x| = wsup v a b R := hx.2
  have hne : v x * |R.eval x| ≠ 0 := by rw [he]; exact ne_of_gt hpos
  constructor
  · rcases lt_or_eq_of_le (hw.nonneg x hx.1) with h | h
    · exact h
    · exact absurd (by rw [← h]; ring) hne
  · intro h
    rw [h] at hne
    simp at hne

theorem abs_sub_lt_of_bounds {A B t ε M m : ℝ} (hA0 : 0 ≤ A) (hAt : A ≤ t)
    (hBm : m / 2 < B) (hBM : B ≤ M) (hε : 0 < ε) (hm : 0 < m) (hεM : ε * M ≤ t / 2)
    (_ht : 0 < t) : |A - ε * B| < t := by
  rcases abs_cases (A - ε * B) with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]; nlinarith
  · rw [h1]; nlinarith

/-- A sign-matching correction of lower degree strictly improves the weighted supremum. -/
theorem exists_wsup_lt_of_sign_match (hw : IsWeight v a b) {T g : Polynomial ℝ} (hT : T ≠ 0)
    (hsign : ∀ x ∈ extremeSet v a b T, 0 < T.eval x * g.eval x) :
    ∃ ε : ℝ, 0 < ε ∧ wsup v a b (T - Polynomial.C ε * g) < wsup v a b T := by
  have ht : 0 < wsup v a b T := wsup_pos hw hT
  have hM : 0 ≤ wsup v a b g := wsup_nonneg hw g
  have hcontg : ContinuousOn (fun x => v x * |g.eval x|) (extremeSet v a b T) :=
    (hw.cont.mul (Polynomial.continuous g).abs).continuousOn
  obtain ⟨x0, hx0, hmin0⟩ := (extremeSet_isCompact hw T).exists_isMinOn
    (extremeSet_nonempty hw T) hcontg
  have hm : 0 < v x0 * |g.eval x0| := by
    obtain ⟨hv0, _⟩ := pos_of_mem_extremeSet hw hT hx0
    have hg0 : g.eval x0 ≠ 0 := by
      intro h
      have := hsign x0 hx0
      rw [h, mul_zero] at this
      exact absurd this (lt_irrefl 0)
    exact mul_pos hv0 (abs_pos.mpr hg0)
  set m := v x0 * |g.eval x0| with hms
  set t := wsup v a b T with hts
  set M := wsup v a b g with hMs
  set Cset : Set ℝ := Set.Icc a b ∩
    ({x | v x * |g.eval x| ≤ m / 2} ∪ {x | T.eval x * g.eval x ≤ 0}) with hCs
  have hCcpt : IsCompact Cset := by
    refine isCompact_Icc.inter_right (IsClosed.union ?_ ?_)
    · exact isClosed_le (hw.cont.mul (Polynomial.continuous g).abs) continuous_const
    · exact isClosed_le ((Polynomial.continuous T).mul (Polynomial.continuous g))
        continuous_const
  have hdisj : ∀ x ∈ extremeSet v a b T, x ∉ Cset := by
    intro x hx hxC
    rcases hxC.2 with h | h
    · have h1 : m ≤ v x * |g.eval x| := hmin0 hx
      simp only [Set.mem_setOf_eq] at h
      linarith
    · exact absurd (hsign x hx) (not_lt.mpr h)
  have hcontT : ContinuousOn (fun x => v x * |T.eval x|) Cset :=
    (hw.cont.mul (Polynomial.continuous T).abs).continuousOn
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Cset, v x * |T.eval x| ≤ t - δ := by
    rcases Set.eq_empty_or_nonempty Cset with hC | hC
    · refine ⟨t, ht, ?_⟩
      intro x hx
      rw [hC] at hx
      simp at hx
    · obtain ⟨y, hy, hmax⟩ := hCcpt.exists_isMaxOn hC hcontT
      have hle : v y * |T.eval y| ≤ t := le_wsup hw T hy.1
      have hlt : v y * |T.eval y| < t := by
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd hy (hdisj y ⟨hy.1, h⟩)
      refine ⟨t - v y * |T.eval y|, by linarith, ?_⟩
      intro x hx
      have h6 : v x * |T.eval x| ≤ v y * |T.eval y| := hmax hx
      linarith
  obtain ⟨δ, hδ0, hδle⟩ := hδ
  have hMpos : (0:ℝ) < 2 * (M + 1) := by linarith
  refine ⟨min (δ / (2 * (M + 1))) (t / (2 * (M + 1))),
    lt_min (by positivity) (by positivity), ?_⟩
  set ε := min (δ / (2 * (M + 1))) (t / (2 * (M + 1))) with hεs
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hM1 : M + 1 ≠ 0 := by positivity
  have hεM1 : ε * M ≤ δ / 2 := by
    have h1 : ε ≤ δ / (2 * (M + 1)) := min_le_left _ _
    have h2 : ε * M ≤ (δ / (2 * (M + 1))) * M := mul_le_mul_of_nonneg_right h1 hM
    have key : δ / 2 - (δ / (2 * (M + 1))) * M = δ / (2 * (M + 1)) := by
      field_simp
      ring
    have h4 : 0 < δ / (2 * (M + 1)) := div_pos hδ0 hMpos
    linarith
  have hεM2 : ε * M ≤ t / 2 := by
    have h1 : ε ≤ t / (2 * (M + 1)) := min_le_right _ _
    have h2 : ε * M ≤ (t / (2 * (M + 1))) * M := mul_le_mul_of_nonneg_right h1 hM
    have key : t / 2 - (t / (2 * (M + 1))) * M = t / (2 * (M + 1)) := by
      field_simp
      ring
    have h4 : 0 < t / (2 * (M + 1)) := div_pos ht hMpos
    linarith
  obtain ⟨x1, hx1, he1⟩ := wsup_attained hw (T - Polynomial.C ε * g)
  rw [he1]
  have heval : (T - Polynomial.C ε * g).eval x1 = T.eval x1 - ε * g.eval x1 := by simp
  rw [heval]
  have hv1 : 0 ≤ v x1 := hw.nonneg x1 hx1
  have hA : v x1 * |T.eval x1| ≤ t := le_wsup hw T hx1
  have hB : v x1 * |g.eval x1| ≤ M := le_wsup hw g hx1
  by_cases hx1C : x1 ∈ Cset
  · have h1 : v x1 * |T.eval x1| ≤ t - δ := hδle x1 hx1C
    have habs : |T.eval x1 - ε * g.eval x1| ≤ |T.eval x1| + ε * |g.eval x1| := by
      have h2 := abs_add_le (T.eval x1) (-(ε * g.eval x1))
      rw [← sub_eq_add_neg, abs_neg, abs_mul, abs_of_pos hε0] at h2
      exact h2
    have h3 : v x1 * |T.eval x1 - ε * g.eval x1| ≤
        v x1 * |T.eval x1| + ε * (v x1 * |g.eval x1|) := by
      nlinarith [mul_le_mul_of_nonneg_left habs hv1]
    nlinarith [mul_le_mul_of_nonneg_left hB (le_of_lt hε0)]
  · have hBm : m / 2 < v x1 * |g.eval x1| := by
      by_contra hcon
      exact hx1C ⟨hx1, Or.inl (not_lt.mp hcon)⟩
    have hTg : 0 < T.eval x1 * g.eval x1 := by
      by_contra hcon
      exact hx1C ⟨hx1, Or.inr (not_lt.mp hcon)⟩
    have hkey : v x1 * |T.eval x1 - ε * g.eval x1| =
        |v x1 * |T.eval x1| - ε * (v x1 * |g.eval x1|)| := by
      rcases lt_trichotomy (T.eval x1) 0 with hT1 | hT1 | hT1
      · have hg1 : g.eval x1 < 0 := by nlinarith
        rw [abs_of_neg hT1, abs_of_neg hg1]
        rw [show v x1 * -T.eval x1 - ε * (v x1 * -g.eval x1)
          = -(v x1 * (T.eval x1 - ε * g.eval x1)) by ring, abs_neg, abs_mul,
          abs_of_nonneg hv1]
      · exact absurd hTg (by rw [hT1]; simp)
      · have hg1 : 0 < g.eval x1 := by nlinarith
        rw [abs_of_pos hT1, abs_of_pos hg1]
        rw [show v x1 * T.eval x1 - ε * (v x1 * g.eval x1)
          = v x1 * (T.eval x1 - ε * g.eval x1) by ring, abs_mul, abs_of_nonneg hv1]
    rw [hkey]
    exact abs_sub_lt_of_bounds (mul_nonneg hv1 (abs_nonneg _)) hA hBm hB hε0 hm hεM2 ht

/-- A monic minimizer admits no lower-degree sign-matching correction. -/
theorem exists_sign_mismatch_of_minimizer (hw : IsWeight v a b) {n : ℕ} {T : Polynomial ℝ}
    (hT : T ∈ monicDeg n) (hmin : ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p)
    {g : Polynomial ℝ} (hgd : ∀ i, n ≤ i → g.coeff i = 0) :
    ∃ x ∈ extremeSet v a b T, T.eval x * g.eval x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hTne : T ≠ 0 := by
    intro h
    have := hT.2
    rw [h] at this
    simp at this
  obtain ⟨ε, hε, hlt⟩ := exists_wsup_lt_of_sign_match hw hTne hcon
  have hgdeg : g.natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    exact hgd i (le_of_lt hi)
  have hmem : T - Polynomial.C ε * g ∈ monicDeg n := by
    constructor
    · refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      refine max_le hT.1 ?_
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) hgdeg
    · rw [Polynomial.coeff_sub, hT.2, Polynomial.coeff_C_mul, hgd n le_rfl]
      ring
  exact absurd (hmin _ hmem) (not_le.mpr hlt)

end
end GaloisForLFunctions.HTGeometry.WeightedMinimax
