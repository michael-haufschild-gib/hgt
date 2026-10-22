import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedSignedControlProducer
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFixedScaleDressedTransitionCoreNoGo

/-!
# Matched CCM currents cannot renormalize the Suzuki transition core

The coefficient-faithful matched actual-head current is an exact signed Suzuki wall current, but
its quadratic prime-aperture gain makes its complete series summable.  The surviving positive
Suzuki reporter transition core grows linearly on the cofinal aperture subsequence `8n`.

This module closes the tempting CCM-to-SP-E compensation route at its exact source scale.  Partial
sums of every fixed actual-head matched current have one common upper bound, so subtracting them
from the transition core still makes the rectangular Ward defect tend to negative infinity.  In
particular, no such matched actual-head source can supply the lower-semibounded Ward premise used
by the RH receiver.

The positive survivor is sharp: any viable CCM/Suzuki weld must retain an unsummable signed
atomic--continuous relative channel before quadratic matched damping.  No RH premise, zero data,
or numerical estimate is used.
-/

open Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every finite-range partial sum of one matched actual-head Suzuki current is bounded above by
one constant.  This is the cofinal consequence of the corpus's absolute summability theorem. -/
theorem exists_uniform_upper_ccmActualHeadMatchedSuzukiRangeBlock
    (f : SoninL2) :
    ∃ B : ℝ, ∀ N : ℕ,
      ccmActualHeadMatchedSuzukiFiniteBlock (Finset.range N) f ≤ B := by
  have hsum : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        ccmActualHeadMatchedSuzukiCurrent n f)
      atTop
      (nhds (∑' n : ℕ, ccmActualHeadMatchedSuzukiCurrent n f)) :=
    (summable_ccmActualHeadMatchedSuzukiCurrent f).hasSum.tendsto_sum_nat
  rcases hsum.bddAbove_range with ⟨B, hB⟩
  refine ⟨B, fun N => ?_⟩
  rw [ccmActualHeadMatchedSuzukiFiniteBlock]
  exact hB (Set.mem_range_self N)

/-- The exact positive transition core remains in the wrong scaling class after subtraction of
any fixed matched actual-head CCM current. -/
theorem tendsto_suzukiRectangularWardDefect_transitionCore_sub_matchedCCM_atBot
    (L : ℝ) (f : SoninL2) :
    Tendsto (fun n : ℕ =>
      suzukiRectangularWardDefect L
        (fun N =>
          GaloisForLFunctions.RHTower.suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            ccmActualHeadMatchedSuzukiFiniteBlock (Finset.range N) f)
        (8 * n)) atTop atBot := by
  obtain ⟨B, hB⟩ := exists_uniform_upper_ccmActualHeadMatchedSuzukiRangeBlock f
  exact tendsto_suzukiRectangularWardDefect_transitionCore_sub_bounded_atBot L hB

/-- No fixed matched actual-head source can make the corrected transition-core Ward defect
eventually lower-semibounded. -/
theorem not_exists_eventually_bddBelow_suzukiRectangularWardDefect_transitionCore_sub_matchedCCM
    (L : ℝ) (f : SoninL2) :
    ¬ ∃ lower : ℝ, ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        (fun N =>
          GaloisForLFunctions.RHTower.suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            ccmActualHeadMatchedSuzukiFiniteBlock (Finset.range N) f)
        (8 * n) := by
  rintro ⟨lower, hlower⟩
  have hfall :=
    tendsto_suzukiRectangularWardDefect_transitionCore_sub_matchedCCM_atBot L f
  have hbelow : ∀ᶠ n : ℕ in atTop,
      suzukiRectangularWardDefect L
        (fun N =>
          GaloisForLFunctions.RHTower.suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            ccmActualHeadMatchedSuzukiFiniteBlock (Finset.range N) f)
        (8 * n) ≤ lower - 1 :=
    (tendsto_atBot.1 hfall) (lower - 1)
  rcases (hlower.and hbelow).exists with ⟨n, hlow, hhigh⟩
  linarith

end


end RHTower
