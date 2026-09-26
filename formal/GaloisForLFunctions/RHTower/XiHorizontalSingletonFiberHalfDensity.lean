import GaloisForLFunctions.RHTower.Zeta23HorizontalSingletonDensity
import GaloisForLFunctions.RHTower.LamzouriMontgomeryTaylorXiDensity

/-!
# More than half of the zeta zeros are alone on their horizontal line

A horizontal fibre of total multiplicity one consists of one simple critical-line zero, so it
carries no ordinate collision.  The charging law `le_liminf_xiSingletonFiberRatio` gives the
singleton-fibre density at least `κ_s − (1 − κ)/2`, where `κ` and `κ_s` bound the critical and the
simple-critical densities: every off-line fibre holds at least two copies and spoils at most one
simple critical zero.

With the unconditional two-thirds theorem (`κ = κ_s = 2/3`) this is `1/2`.  With the
Montgomery--Taylor window constant `HD 1 = 2 − 1/c₁*` it is `(3·HD 1 − 1)/2`, numerically
`0.5087…`.  So in lower density more than half of all zero copies lie on horizontal lines that
carry no other zero.
-/

open Filter

namespace RHTower

noncomputable section

/-- An eventual cumulative lower bound `(c − ε)·N(T) ≤ N₀,s(T)` for every `ε > 0` gives `c` as a
lower bound for the liminf of the simple-critical ratio. -/
theorem le_liminf_xiSimpleCriticalRatio_of_epsilon (c : ℝ)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (c - ε) * (xiPosZeroCount T : ℝ) ≤ xiSimpleCriticalZeroCount T) :
    c ≤ liminf xiSimpleCriticalRatio atTop := by
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop xiSimpleCriticalRatio :=
    (isBoundedUnder_of ⟨1, fun T => xiSimpleCriticalRatio_le_one T⟩).isCoboundedUnder_ge
  refine le_of_forall_sub_le fun ε hε => ?_
  obtain ⟨T₀, hT₀⟩ := h ε hε
  refine le_liminf_of_le hcob ?_
  filter_upwards [eventually_ge_atTop T₀, eventually_pos_xiPosZeroCount_of_zeta23]
    with T hT hN
  rw [xiSimpleCriticalRatio, le_div_iff₀ hN]
  exact hT₀ T hT

/-- A simple-critical density bound is also a critical density bound. -/
theorem le_liminf_xiCriticalRatio_of_simple {c : ℝ}
    (h : c ≤ liminf xiSimpleCriticalRatio atTop) :
    c ≤ liminf xiCriticalRatio atTop := by
  have hbdd : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop xiSimpleCriticalRatio :=
    isBoundedUnder_of ⟨0, fun T => xiSimpleCriticalRatio_nonneg T⟩
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop xiCriticalRatio :=
    (isBoundedUnder_of ⟨1, fun T => xiCriticalRatio_le_one T⟩).isCoboundedUnder_ge
  refine le_trans h ?_
  exact Filter.liminf_le_liminf
    (Filter.Eventually.of_forall xiSimpleCriticalRatio_le_xiCriticalRatio) hbdd hcob

/-- A simple-critical density `c` forces singleton-fibre density `(3c − 1)/2`. -/
theorem le_liminf_xiSingletonFiberRatio_of_simple {c : ℝ}
    (h : c ≤ liminf xiSimpleCriticalRatio atTop) :
    (3 * c - 1) / 2 ≤ liminf xiSingletonFiberRatio atTop := by
  have hs := le_liminf_xiSingletonFiberRatio c c (le_liminf_xiCriticalRatio_of_simple h) h
  linarith

/-- **Half of all zeros are alone on their horizontal line.**  In lower density at least one half
of the positive-ordinate zero copies lie in horizontal fibres of total multiplicity one. -/
theorem zeta23_horizontalSingleton_density_half :
    (1 / 2 : ℝ) ≤ liminf xiSingletonFiberRatio atTop := by
  have h := le_liminf_xiSingletonFiberRatio_of_simple two_thirds_le_liminf_xiSimpleCriticalRatio
  norm_num at h ⊢
  linarith

/-- **Montgomery--Taylor singleton density.**  With the optimal-window constant `HD 1 = 2 − 1/c₁*`
the singleton-fibre density is at least `(3·HD 1 − 1)/2 = 0.5087…`. -/
theorem montgomeryTaylor_horizontalSingleton_density :
    (3 * Zeta23.ThmD.HD 1 - 1) / 2 ≤ liminf xiSingletonFiberRatio atTop :=
  le_liminf_xiSingletonFiberRatio_of_simple
    (le_liminf_xiSimpleCriticalRatio_of_epsilon _ lamzouri_montgomeryTaylor_simpleCritical_epsilon)

end

end RHTower
