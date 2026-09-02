import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# Unconditional positive density of horizontal-singleton Xi fibers

The finite reflection-charging law for horizontal Xi fibers was already formalized in
`HorizontalSingletonFiberCharging`.  Alpöge--Furman's stronger two-thirds theorem, transported to
the completed-Xi census in `Zeta23SimpleCriticalDensity`, now supplies both analytic proportions
needed by that law.  This closes the exact decimal lower-density statement of the
`horizontal-singleton-zero-fibers` card without a density hypothesis.
-/

open Filter

namespace RHTower

noncomputable section

/-- Every simple critical Xi zero counted by `N₀,s(T)` contributes one copy to `N₀(T)`. -/
theorem xiSimpleCriticalZeroCount_le_xiPosCriticalZeroCount (T : ℝ) :
    xiSimpleCriticalZeroCount T ≤ xiPosCriticalZeroCount T := by
  classical
  rw [xiSimpleCriticalZeroCount, xiPosCriticalZeroCount]
  calc
    ((stripFinsetPos T).filter
        (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)).card =
        ∑ z ∈ (stripFinsetPos T).filter
          (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1),
            (analyticOrderAt xi z).toNat := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro z hz
      exact ((Finset.mem_filter.mp hz).2.2).symm
    _ ≤ ∑ z ∈ (stripFinsetPos T).filter (fun z => z.re = 1 / 2),
          (analyticOrderAt xi z).toNat := by
      apply Finset.sum_le_sum_of_subset
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.1⟩

/-- The simple-critical proportion is pointwise bounded by the full critical proportion. -/
theorem xiSimpleCriticalRatio_le_xiCriticalRatio (T : ℝ) :
    xiSimpleCriticalRatio T ≤ xiCriticalRatio T := by
  unfold xiSimpleCriticalRatio xiCriticalRatio
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast xiSimpleCriticalZeroCount_le_xiPosCriticalZeroCount T)
    (Nat.cast_nonneg _)

/-- Alpöge--Furman's two-thirds simple-critical density also gives two-thirds critical density. -/
theorem two_thirds_le_liminf_xiCriticalRatio :
    (2 / 3 : ℝ) ≤ liminf xiCriticalRatio atTop := by
  have hbdd : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop xiSimpleCriticalRatio :=
    isBoundedUnder_of ⟨0, fun T => xiSimpleCriticalRatio_nonneg T⟩
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop xiCriticalRatio :=
    (isBoundedUnder_of ⟨1, fun T => xiCriticalRatio_le_one T⟩).isCoboundedUnder_ge
  refine le_trans two_thirds_le_liminf_xiSimpleCriticalRatio ?_
  exact Filter.liminf_le_liminf
    (Filter.Eventually.of_forall xiSimpleCriticalRatio_le_xiCriticalRatio) hbdd hcob

/-- **Unconditional positive density of horizontal-singleton Xi fibers.**

At least `0.116158438` of all positive-ordinate nontrivial-zero copies lie in horizontal fibers of
total multiplicity one, in lower density.  Each such fiber consists of one simple critical-line
zero by `xiHorizontalSingletonZero_re_eq_half` and `xiHorizontalSingletonZero_order_eq_one`.
-/
theorem zeta23_horizontalSingleton_density :
    (0.116158438 : ℝ) ≤ liminf xiSingletonFiberRatio atTop := by
  apply prattRoblesZaharescuZeindler_singleton_density
  · exact le_trans (by norm_num : (0.417293962 : ℝ) ≤ 2 / 3)
      two_thirds_le_liminf_xiCriticalRatio
  · exact le_trans (by norm_num : (0.407511457 : ℝ) ≤ 2 / 3)
      two_thirds_le_liminf_xiSimpleCriticalRatio

end

end RHTower
