import GaloisForLFunctions.ZeroConfigurationGeometry.TheRightSubstripsHaveSubunitMoments
import GaloisForLFunctions.ZeroConfigurationGeometry.ThePrimeErrorKeepsItsBoundaryTrace

/-!
# Height cutoffs in a right substrip have power tails

One subunit moment simultaneously controls the size of the retained zero
set and the full reciprocal mass omitted from it. The cutoff contains
every right-substrip zero below its height, with all multiplicity copies.
-/

noncomputable section

open Complex Set
open _root_.RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Actual finite height cutoffs have sublinear cardinality and a
power-saving full reciprocal tail, with one constant for every height. -/
theorem exists_rightSubstrip_cutoff_bounds {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y →
      ∃ F : Finset XiZeroCopy,
        (∀ q, q ∈ F ↔ σ ≤ (q.1 : ℂ).re ∧ |xiCopyOrdinate q| ≤ Y) ∧
        (F.card : ℝ) ≤ C * Y ^ p ∧
        (∑' q, rightSubstripTailWeight σ F q) ≤ C * Y ^ (p - 1) := by
  classical
  obtain ⟨p, hp, hp1, hs⟩ := exists_summable_rightSubstrip_subunit_moment hσ
  let w : XiZeroCopy → ℝ := fun q =>
    if σ ≤ (q.1 : ℂ).re then |xiCopyOrdinate q| ^ (-p) else 0
  have hw (q : XiZeroCopy) : 0 ≤ w q := by
    dsimp only [w]
    split_ifs <;> positivity
  have hws : Summable w := by
    change Summable ({q : XiZeroCopy | σ ≤ (q.1 : ℂ).re}.indicator
      (fun q => |xiCopyOrdinate q| ^ (-p)))
    exact summable_subtype_iff_indicator.mp hs
  let C := ∑' q, w q
  have hC : 0 ≤ C := tsum_nonneg hw
  refine ⟨p, C, hp, hp1, hC, ?_⟩
  intro Y hY
  let F := (finite_abs_im_le Y).toFinset.filter (fun q => σ ≤ (q.1 : ℂ).re)
  have hmem (q : XiZeroCopy) : q ∈ F ↔
      σ ≤ (q.1 : ℂ).re ∧ |xiCopyOrdinate q| ≤ Y := by
    simp only [F, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      xiCopyOrdinate, and_comm]
  have hcard : (F.card : ℝ) ≤ C * Y ^ p := by
    have hterm (q : XiZeroCopy) (hq : q ∈ F) : (1 : ℝ) ≤ Y ^ p * w q := by
      obtain ⟨hσq, hqY⟩ := (hmem q).mp hq
      have hx : 0 < |xiCopyOrdinate q| := by
        have hh := four_lt_abs_xiCopyOrdinate q
        linarith only [hh]
      rw [show w q = |xiCopyOrdinate q| ^ (-p) from if_pos hσq]
      calc
        _ = |xiCopyOrdinate q| ^ p * |xiCopyOrdinate q| ^ (-p) := by
          rw [← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hx.le hqY hp.le) (Real.rpow_nonneg hx.le _)
    calc
      _ = ∑ _q ∈ F, (1 : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ q ∈ F, Y ^ p * w q := Finset.sum_le_sum hterm
      _ = Y ^ p * ∑ q ∈ F, w q := (Finset.mul_sum _ _ _).symm
      _ ≤ Y ^ p * C := mul_le_mul_of_nonneg_left
        (hws.sum_le_tsum F (fun q _ => hw q)) (Real.rpow_nonneg hY.le _)
      _ = _ := mul_comm _ _
  have htail (q : XiZeroCopy) :
      rightSubstripTailWeight σ F q ≤ Y ^ (p - 1) * w q := by
    by_cases hq : σ ≤ (q.1 : ℂ).re ∧ q ∉ F
    · have hqY : Y ≤ |xiCopyOrdinate q| := by
        by_contra hn
        exact hq.2 ((hmem q).mpr ⟨hq.1, (not_le.mp hn).le⟩)
      have hx : 0 < |xiCopyOrdinate q| := hY.trans_le hqY
      have he : |xiCopyOrdinate q| ^ (p - 1) * |xiCopyOrdinate q| ^ (-p) =
          |xiCopyOrdinate q|⁻¹ := by
        rw [← Real.rpow_add hx, show p - 1 + -p = -(1 : ℝ) by ring,
          Real.rpow_neg hx.le, Real.rpow_one]
      rw [rightSubstripTailWeight, if_pos hq,
        show w q = |xiCopyOrdinate q| ^ (-p) from if_pos hq.1]
      calc
        _ ≤ |xiCopyOrdinate q|⁻¹ := inv_anti₀ hx (Complex.abs_im_le_norm _)
        _ = |xiCopyOrdinate q| ^ (p - 1) * |xiCopyOrdinate q| ^ (-p) := he.symm
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hY hqY (sub_nonpos.mpr hp1.le))
          (Real.rpow_nonneg hx.le _)
    · rw [rightSubstripTailWeight, if_neg hq]
      exact mul_nonneg (Real.rpow_nonneg hY.le _) (hw q)
  refine ⟨F, hmem, hcard, ?_⟩
  calc
    _ ≤ ∑' q, Y ^ (p - 1) * w q :=
      (summable_rightSubstripTailWeight hσ F).tsum_le_tsum htail (hws.mul_left _)
    _ = C * Y ^ (p - 1) := by rw [tsum_mul_left]; exact mul_comm _ _

end GaloisForLFunctions.ZeroConfigurationGeometry
