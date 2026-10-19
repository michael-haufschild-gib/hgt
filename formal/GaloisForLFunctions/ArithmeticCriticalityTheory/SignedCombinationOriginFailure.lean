import GaloisForLFunctions.ArithmeticCriticalityTheory.OddProfileOriginFailure

/-!
# Signed combinations of shifted ground states fail at the origin

Any combination `c₁ ω_a + c₂ ω_b` that is nonnegative on the half line and positive at `log 2` is a
strict folded subsolution near `0`: it is odd, continuous, Lipschitz on `[−1, 1]`, and its test
coordinate `c₁ m_a + c₂ m_b` is dominated by `(|c₁| + |c₂|) Φ(0)/Φ(M) · Φ(· − M)` with
`M = max a b`, because `Φ(y − a) ≤ (Φ(0)/Φ(b)) Φ(y − b)` for `0 ≤ a ≤ b` and `y ≥ 0`. The shifted
ground states themselves are the special case `c₂ = 0`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- A shifted kernel is dominated by a further shifted one on the half line. -/
theorem riemannKernelReal_sub_le_mul_sub_of_le {a b y : ℝ} (hab : a ≤ b) (hy : 0 ≤ y) :
    riemannKernelReal (y - a) ≤
      riemannKernelReal 0 / riemannKernelReal b * riemannKernelReal (y - b) := by
  have hΘ0 := riemannKernelReal_pos 0
  have hb := riemannKernelReal_pos b
  have hK := (riemannKernelReal_pos (y - b)).le
  rcases le_or_gt b y with h | h
  · have h1 : riemannKernelReal (y - a) ≤ riemannKernelReal (y - b) :=
      riemannKernelReal_antitone_of_nonneg (by linarith) (by linarith)
    have hratio : 1 ≤ riemannKernelReal 0 / riemannKernelReal b := by
      rw [le_div_iff₀ hb, one_mul]
      exact riemannKernelReal_le_zero_point b
    calc riemannKernelReal (y - a) ≤ riemannKernelReal (y - b) := h1
      _ = 1 * riemannKernelReal (y - b) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio hK
  · have h1 : riemannKernelReal (y - a) ≤ riemannKernelReal 0 := riemannKernelReal_le_zero_point _
    have h2 : riemannKernelReal b ≤ riemannKernelReal (y - b) :=
      riemannKernelReal_sub_ge_of_le hy h.le
    calc riemannKernelReal (y - a) ≤ riemannKernelReal 0 := h1
      _ = riemannKernelReal 0 / riemannKernelReal b * riemannKernelReal b := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (div_nonneg hΘ0.le hb.le)

/-- The shifted ground state is dominated: `Φ ω_a = m_a ≤ Φ(· − a)`. -/
theorem riemannKernelReal_mul_shiftedGroundState_le (a y : ℝ) :
    riemannKernelReal y * shiftedGroundState a y ≤ 1 * riemannKernelReal (y - a) := by
  rw [riemannKernelReal_mul_shiftedGroundState, one_mul]
  exact shiftDifference_le_kernel a y

/-- The general origin failure applied to a single shifted ground state. -/
theorem shiftedGroundState_origin_failure_of_profile {a : ℝ} (ha : 0 < a) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x, 0 < x → x < x₀ →
      foldedGenerator (shiftedGroundState a) x <
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x := by
  obtain ⟨L, -, hL⟩ :=
    exists_lipschitz_bound_on_Icc ((contDiff_shiftedGroundState a).of_le (by norm_num)) (-1) 1
  refine exists_origin_window_foldedGenerator_lt_potential_of_profile
    (contDiff_shiftedGroundState a).continuous (shiftedGroundState_neg a) ?_
    (shiftedGroundState_pos ha (Real.log_pos one_lt_two)) hL zero_le_one
    fun y _ => riemannKernelReal_mul_shiftedGroundState_le a y
  intro y hy
  rcases hy.lt_or_eq with hy | hy
  · exact (shiftedGroundState_pos ha hy).le
  · rw [← hy, odd_apply_zero (shiftedGroundState_neg a)]

/-- **Signed combinations.** A combination `c₁ ω_a + c₂ ω_b` that is nonnegative on `(0, ∞)` and
positive at `log 2` is a strict folded subsolution on a right neighbourhood of `0`. -/
theorem exists_origin_window_signedCombination_foldedGenerator_lt_potential {a b c₁ c₂ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hpos : ∀ x, 0 < x → 0 ≤ c₁ * shiftedGroundState a x + c₂ * shiftedGroundState b x)
    (h2 : 0 < c₁ * shiftedGroundState a (Real.log 2) + c₂ * shiftedGroundState b (Real.log 2)) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x, 0 < x → x < x₀ →
      foldedGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) x <
        riemannKernelReal x * Real.cosh (x / 2) *
          (c₁ * shiftedGroundState a x + c₂ * shiftedGroundState b x) := by
  have hcd : ContDiff ℝ 1 fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y :=
    (contDiff_const.mul ((contDiff_shiftedGroundState a).of_le (by norm_num))).add
      (contDiff_const.mul ((contDiff_shiftedGroundState b).of_le (by norm_num)))
  obtain ⟨L, -, hL⟩ := exists_lipschitz_bound_on_Icc hcd (-1) 1
  have hodd : ∀ x, (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) (-x) =
      -(fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) x := fun x => by
    simp only
    rw [shiftedGroundState_neg, shiftedGroundState_neg]
    ring
  have hnn : ∀ y, 0 ≤ y →
      0 ≤ (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) y := by
    intro y hy
    rcases hy.lt_or_eq with hy | hy
    · exact hpos y hy
    · simp only
      rw [← hy, odd_apply_zero (shiftedGroundState_neg a), odd_apply_zero (shiftedGroundState_neg b)]
      simp
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max a b := ⟨_, rfl⟩
  have haM : a ≤ M := hM ▸ le_max_left _ _
  have hbM : b ≤ M := hM ▸ le_max_right _ _
  have hM0 : 0 < M := lt_of_lt_of_le ha haM
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (|c₁| + |c₂|) * (riemannKernelReal 0 / riemannKernelReal M) :=
    ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (div_nonneg (riemannKernelReal_pos 0).le (riemannKernelReal_pos M).le)
  have hdom : ∀ y, 0 ≤ y → riemannKernelReal y *
      (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) y ≤
      C * riemannKernelReal (y - M) := by
    intro y hy
    simp only
    have e : riemannKernelReal y * (c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) =
        c₁ * shiftDifference a y + c₂ * shiftDifference b y := by
      rw [← riemannKernelReal_mul_shiftedGroundState a y, ← riemannKernelReal_mul_shiftedGroundState b y]
      ring
    rw [e, hC]
    have hK := (riemannKernelReal_pos (y - M)).le
    have ha' : c₁ * shiftDifference a y ≤ |c₁| * (riemannKernelReal 0 / riemannKernelReal M *
        riemannKernelReal (y - M)) := by
      calc c₁ * shiftDifference a y ≤ |c₁ * shiftDifference a y| := le_abs_self _
        _ = |c₁| * |shiftDifference a y| := abs_mul _ _
        _ ≤ |c₁| * riemannKernelReal (y - a) :=
          mul_le_mul_of_nonneg_left (abs_shiftDifference_le_kernel_of_nonneg ha.le hy) (abs_nonneg _)
        _ ≤ |c₁| * (riemannKernelReal 0 / riemannKernelReal M * riemannKernelReal (y - M)) :=
          mul_le_mul_of_nonneg_left (riemannKernelReal_sub_le_mul_sub_of_le haM hy)
            (abs_nonneg _)
    have hb' : c₂ * shiftDifference b y ≤ |c₂| * (riemannKernelReal 0 / riemannKernelReal M *
        riemannKernelReal (y - M)) := by
      calc c₂ * shiftDifference b y ≤ |c₂ * shiftDifference b y| := le_abs_self _
        _ = |c₂| * |shiftDifference b y| := abs_mul _ _
        _ ≤ |c₂| * riemannKernelReal (y - b) :=
          mul_le_mul_of_nonneg_left (abs_shiftDifference_le_kernel_of_nonneg hb.le hy) (abs_nonneg _)
        _ ≤ |c₂| * (riemannKernelReal 0 / riemannKernelReal M * riemannKernelReal (y - M)) :=
          mul_le_mul_of_nonneg_left (riemannKernelReal_sub_le_mul_sub_of_le hbM hy)
            (abs_nonneg _)
    linarith
  exact exists_origin_window_foldedGenerator_lt_potential_of_profile hcd.continuous hodd hnn h2 hL
    hC0 hdom

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
