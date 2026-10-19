import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStatePlateauPositivity

/-!
# A uniformly Lipschitz family of smooth plateaus

With `τ` the smooth transition function (`τ = 0` on `(−∞, 0]`, `τ = 1` on `[1, ∞)`, `0 ≤ τ ≤ 1`),
the profile

    u_L(x) = τ(L + 1 − x) τ(L + 1 + x)

is even, smooth, equal to `1` on `[−L, L]`, supported in `[−L−1, L+1]`, with values in `[0, 1]`,
and Lipschitz with a constant independent of `L`. The constant comes from a Lipschitz bound of
`τ` on `[−1, 2]`, extended to the line by clamping to `[0, 1]`, on which `τ` is constant outside.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The smooth plateau `u_L(x) = τ(L + 1 − x) τ(L + 1 + x)`. -/
def smoothPlateau (L x : ℝ) : ℝ :=
  Real.smoothTransition (L + 1 - x) * Real.smoothTransition (L + 1 + x)

theorem smoothPlateau_neg (L x : ℝ) : smoothPlateau L (-x) = smoothPlateau L x := by
  unfold smoothPlateau
  rw [show L + 1 - -x = L + 1 + x by ring, show L + 1 + -x = L + 1 - x by ring]
  ring

theorem smoothPlateau_nonneg (L x : ℝ) : 0 ≤ smoothPlateau L x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem smoothPlateau_le_one (L x : ℝ) : smoothPlateau L x ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem smoothPlateau_eq_one {L x : ℝ} (h : |x| ≤ L) : smoothPlateau L x = 1 := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  unfold smoothPlateau
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem smoothPlateau_eq_zero {L x : ℝ} (h : L + 1 ≤ |x|) : smoothPlateau L x = 0 := by
  unfold smoothPlateau
  rcases le_abs.mp h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : L + 1 + x ≤ 0), mul_zero]

theorem contDiff_smoothPlateau (L : ℝ) : ContDiff ℝ 2 (smoothPlateau L) := by
  unfold smoothPlateau
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id))

theorem hasCompactSupport_smoothPlateau (L : ℝ) : HasCompactSupport (smoothPlateau L) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(L + 1)) (b := L + 1)) fun x hx => ?_
  apply smoothPlateau_eq_zero
  rw [mem_Icc, not_and_or] at hx
  rcases hx with h | h
  · rw [not_le] at h
    exact le_trans (by linarith) (neg_le_abs x)
  · rw [not_le] at h
    exact le_trans h.le (le_abs_self x)

/-- A clamped point lies in `[0, 1]` and the smooth transition does not see the clamping. -/
theorem smoothTransition_eq_clamp (z : ℝ) :
    Real.smoothTransition z = Real.smoothTransition (max 0 (min 1 z)) := by
  rcases le_or_gt z 0 with h | h
  · rw [max_eq_left (min_le_of_right_le h), Real.smoothTransition.zero_of_nonpos h,
      Real.smoothTransition.zero_of_nonpos le_rfl]
  · rcases le_or_gt 1 z with h1 | h1
    · rw [min_eq_left h1, max_eq_right zero_le_one, Real.smoothTransition.one_of_one_le h1,
        Real.smoothTransition.one_of_one_le le_rfl]
    · rw [min_eq_right h1.le, max_eq_right h.le]

theorem lipschitzWith_clamp : LipschitzWith 1 fun z : ℝ => max 0 (min 1 z) :=
  (LipschitzWith.id.const_min 1).const_max 0

/-- The smooth transition is Lipschitz on the whole line. -/
theorem exists_smoothTransition_lipschitz :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x y : ℝ,
      |Real.smoothTransition y - Real.smoothTransition x| ≤ Λ * |y - x| := by
  obtain ⟨Λ, hΛ0, hΛ⟩ :=
    exists_lipschitz_bound_on_Icc (Real.smoothTransition.contDiff (n := 1)) (-1) 2
  refine ⟨Λ, hΛ0, fun x y => ?_⟩
  have hmem : ∀ z : ℝ, max 0 (min 1 z) ∈ Icc (-1 : ℝ) 2 := fun z =>
    ⟨by linarith [le_max_left (0 : ℝ) (min 1 z)],
      by linarith [max_le (zero_le_one' ℝ) (min_le_left 1 z) ]⟩
  rw [smoothTransition_eq_clamp x, smoothTransition_eq_clamp y]
  refine (hΛ _ (hmem x) _ (hmem y)).trans (mul_le_mul_of_nonneg_left ?_ hΛ0)
  have h := lipschitzWith_clamp.dist_le_mul y x
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
  exact h

/-- The plateaus are Lipschitz with a constant independent of `L`. -/
theorem exists_smoothPlateau_lipschitz :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ L x y : ℝ, |smoothPlateau L y - smoothPlateau L x| ≤ Λ * |y - x| := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothTransition_lipschitz
  refine ⟨2 * Λ, by positivity, fun L x y => ?_⟩
  unfold smoothPlateau
  set A := Real.smoothTransition (L + 1 - x)
  set A' := Real.smoothTransition (L + 1 - y)
  set B := Real.smoothTransition (L + 1 + x)
  set B' := Real.smoothTransition (L + 1 + y)
  have hA : |A' - A| ≤ Λ * |y - x| := by
    have := hΛ (L + 1 - x) (L + 1 - y)
    rwa [show L + 1 - y - (L + 1 - x) = -(y - x) by ring, abs_neg] at this
  have hB : |B' - B| ≤ Λ * |y - x| := by
    have := hΛ (L + 1 + x) (L + 1 + y)
    rwa [show L + 1 + y - (L + 1 + x) = y - x by ring] at this
  have hB'0 : 0 ≤ B' := Real.smoothTransition.nonneg _
  have hB'1 : B' ≤ 1 := Real.smoothTransition.le_one _
  have hA0 : 0 ≤ A := Real.smoothTransition.nonneg _
  have hA1 : A ≤ 1 := Real.smoothTransition.le_one _
  calc |A' * B' - A * B| = |(A' - A) * B' + A * (B' - B)| := by ring_nf
    _ ≤ |(A' - A) * B'| + |A * (B' - B)| := abs_add_le _ _
    _ = |A' - A| * B' + A * |B' - B| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hB'0, abs_of_nonneg hA0]
    _ ≤ Λ * |y - x| * 1 + 1 * (Λ * |y - x|) := by
        gcongr
    _ = 2 * Λ * |y - x| := by ring

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
