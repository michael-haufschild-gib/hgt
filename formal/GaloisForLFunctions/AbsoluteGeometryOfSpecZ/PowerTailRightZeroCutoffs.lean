import GaloisForLFunctions.ZeroConfigurationGeometry.TheRightSubstripTraceCanBeIntegrated
import GaloisForLFunctions.ZeroConfigurationGeometry.RightSubstripCutoffsHavePowerTails

/-!
# Complete tails of the shifted right-substrip trace

A real shift of size at most one changes reciprocal zero norms by at
most a factor of two. Thus the same subunit ordinate moment controls the
complete shifted trace outside its actual finite height cutoff.
-/

noncomputable section

open Complex Set
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ZeroConfigurationGeometry

/-- A bounded nonnegative real shift preserves the reciprocal zero scale. -/
theorem norm_zero_le_two_norm_sub_real {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (q : XiZeroCopy) : ‖(q.1 : ℂ)‖ ≤ 2 * ‖(q.1 : ℂ) - (a : ℂ)‖ := by
  have ht := norm_add_le ((q.1 : ℂ) - (a : ℂ)) (a : ℂ)
  rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] at ht
  have hγ := four_lt_abs_xiCopyOrdinate q
  have hd := abs_ordinate_le_norm_zero_sub_real q a
  linarith only [ht, hγ, hd, ha1]

/-- The shifted term keeps its actual boundary exponent, with a reciprocal
majorant independent of the cutoff and argument. -/
theorem norm_rightShiftedZeroTerm_le_boundary {σ β a x : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hx : 1 ≤ x)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) (q : XiZeroCopy) :
    ‖rightShiftedZeroTerm σ a a x q‖ ≤
      (2 * x ^ (β - a)) * rightSubstripTailWeight σ ∅ q := by
  classical
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hd : 0 < ‖(q.1 : ℂ) - (a : ℂ)‖ :=
      norm_pos_iff.mpr (zero_sub_real_ne_zero q a)
    have hρ : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr (xiZeroCopy_ne_zero q)
    have hinv : 1 / ‖(q.1 : ℂ) - (a : ℂ)‖ ≤ 2 / ‖(q.1 : ℂ)‖ := by
      apply (div_le_div_iff₀ hd hρ).mpr
      simpa only [one_mul] using norm_zero_le_two_norm_sub_real ha ha1 q
    simp only [rightShiftedZeroTerm, rightSubstripTailWeight, hq,
      Finset.notMem_empty, not_false_eq_true, and_self, if_true]
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.ofReal_re]
    calc
      _ ≤ x ^ (β - a) / ‖(q.1 : ℂ) - (a : ℂ)‖ :=
        div_le_div_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hx (sub_le_sub_right (hβ q) a)) hd.le
      _ = x ^ (β - a) * (1 / ‖(q.1 : ℂ) - (a : ℂ)‖) := by ring
      _ ≤ x ^ (β - a) * (2 / ‖(q.1 : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [div_eq_mul_inv]; ring
  · simp only [rightShiftedZeroTerm, rightSubstripTailWeight, hq, false_and,
      if_false, norm_zero, mul_zero, le_refl]

/-- The complete shifted trace outside any finite core is controlled by
the same reciprocal exterior mass as the unshifted prime trace. -/
theorem norm_rightShiftedZeroTrace_sub_sum_le {σ β a x : ℝ}
    (hσ : 1 / 2 < σ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hx : 1 ≤ x)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) (F : Finset XiZeroCopy) :
    ‖rightShiftedZeroTrace σ a a x - ∑ q ∈ F, rightShiftedZeroTerm σ a a x q‖ ≤
      (2 * x ^ (β - a)) * ∑' q, rightSubstripTailWeight σ F q := by
  classical
  have hs := summable_rightShiftedZeroTerm (a := a) (b := a) hσ hx
  have hsplit := hs.sum_add_tsum_compl (s := F)
  have heq : rightShiftedZeroTrace σ a a x - ∑ q ∈ F, rightShiftedZeroTerm σ a a x q =
      ∑' q : ((F : Set XiZeroCopy)ᶜ : Set XiZeroCopy), rightShiftedZeroTerm σ a a x q := by
    rw [rightShiftedZeroTrace, ← hsplit]
    ring
  have htail : (∑' q : ((F : Set XiZeroCopy)ᶜ : Set XiZeroCopy), rightSubstripTailWeight σ ∅ q) =
      ∑' q, rightSubstripTailWeight σ F q := by
    rw [tsum_subtype]
    apply tsum_congr
    intro q
    by_cases hq : q ∈ F <;> by_cases hr : σ ≤ (q.1 : ℂ).re <;>
      simp [Set.indicator, rightSubstripTailWeight, hq, hr]
  rw [heq, ← htail, ← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm (hs.norm.subtype _)).trans ?_
  exact (hs.norm.subtype _).tsum_le_tsum
    (fun q => norm_rightShiftedZeroTerm_le_boundary ha ha1 hx hβ q)
    (((summable_rightSubstripTailWeight hσ ∅).subtype _).mul_left _)

/-- The exact finite height cutoff, retaining all multiplicity copies. -/
def powerTailRightZeroCutoff (σ Y : ℝ) : Finset XiZeroCopy := by
  classical
  exact (finite_abs_im_le Y).toFinset.filter (fun q => σ ≤ (q.1 : ℂ).re)

theorem mem_powerTailRightZeroCutoff (σ Y : ℝ) (q : XiZeroCopy) :
    q ∈ powerTailRightZeroCutoff σ Y ↔ σ ≤ (q.1 : ℂ).re ∧ |xiCopyOrdinate q| ≤ Y := by
  classical
  simp only [powerTailRightZeroCutoff, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq, xiCopyOrdinate, and_comm]

/-- Canonical height cutoffs have a sublinear count and power-decaying
complete exterior mass, with the same constants at every height. -/
theorem exists_powerTailRightZeroCutoff_bounds {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y →
      ((powerTailRightZeroCutoff σ Y).card : ℝ) ≤ C * Y ^ p ∧
      (∑' q, rightSubstripTailWeight σ (powerTailRightZeroCutoff σ Y) q) ≤ C * Y ^ (p - 1) := by
  obtain ⟨p, C, hp, hp1, hC, hcuts⟩ := exists_rightSubstrip_cutoff_bounds hσ
  refine ⟨p, C, hp, hp1, hC, ?_⟩
  intro Y hY
  obtain ⟨F, hmem, hcard, htail⟩ := hcuts Y hY
  have hF : F = powerTailRightZeroCutoff σ Y := by
    ext q
    exact (hmem q).trans (mem_powerTailRightZeroCutoff σ Y q).symm
  simpa only [hF] using And.intro hcard htail

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
