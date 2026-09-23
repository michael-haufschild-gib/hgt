import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicResidualNegativeOrientation
import GaloisForLFunctions.RHTower.SourceHorizontalEulerGammaCubicNegativeRenormalizedChannel

/-!
# Canonical negative cubic source orientation at the prime/Gamma Stokes wall

The first unresolved wall--Xi Malgrange jet is strictly negative. This module tests the existing
source-horizontal Euler/Wold cubic current against that newly determined chamber without choosing a
scale from the target.

The prime-clock-normalized defect vanishes, so it cannot equal the nonzero Xi residual. Before that
collapsing normalization, however, every natural cutoff containing the prime `2` is strictly
negative, its summable limit remains strictly negative, and both lie in the same open Stokes chamber
as the Xi residual. This is the strongest source-natural landing surviving the normalization no-go.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The natural-number Euler/Wold defect is nonnegative at every source label. -/
theorem sourceHorizontalEulerGammaWoldCubicNaturalDefect_nonneg (n : ℕ) :
    0 ≤ sourceHorizontalEulerGammaWoldCubicNaturalDefect n := by
  by_cases hn : n.Prime
  · rw [sourceHorizontalEulerGammaWoldCubicNaturalDefect, dif_pos hn]
    exact (sourceHorizontalEulerGammaWoldCubicDefect_pos ⟨n, hn⟩).le
  · rw [sourceHorizontalEulerGammaWoldCubicNaturalDefect, dif_neg hn]

private theorem sourceHorizontalEulerGammaWoldCubicNaturalDefect_two_pos :
    0 < sourceHorizontalEulerGammaWoldCubicNaturalDefect 2 := by
  rw [sourceHorizontalEulerGammaWoldCubicNaturalDefect, dif_pos Nat.prime_two]
  exact sourceHorizontalEulerGammaWoldCubicDefect_pos ⟨2, Nat.prime_two⟩

/-- Every natural cutoff containing the first prime has the canonical negative Euler-log
orientation. -/
theorem sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent_neg
    {X : ℕ} (hX : 3 ≤ X) :
    sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent X < 0 := by
  have hsum : 0 < ∑ n ∈ Finset.range X,
      sourceHorizontalEulerGammaWoldCubicNaturalDefect n := by
    apply Finset.sum_pos'
    · intro n hn
      exact sourceHorizontalEulerGammaWoldCubicNaturalDefect_nonneg n
    · exact ⟨2, Finset.mem_range.mpr (by omega),
        sourceHorizontalEulerGammaWoldCubicNaturalDefect_two_pos⟩
  rw [sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent_eq]
  simpa only [Finset.sum_neg_distrib] using (neg_lt_zero.mpr hsum)

/-- The unnormalized source-renormalized cubic charge remains strictly negative in the summable
limit; the positive prime-`2` defect prevents collapse. -/
theorem sourceHorizontalEulerGammaCubicNaturalRenormalizedLimit_neg :
    -(∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n) < 0 := by
  exact neg_lt_zero.mpr
    (summable_sourceHorizontalEulerGammaWoldCubicNaturalDefect.tsum_pos
      sourceHorizontalEulerGammaWoldCubicNaturalDefect_nonneg 2
      sourceHorizontalEulerGammaWoldCubicNaturalDefect_two_pos)

private theorem tendsto_sourceHorizontalEulerWoldNormalizedCubicDefect_zero :
    Tendsto (fun N : ℕ =>
      (-2 : ℝ) * sourceHorizontalEulerGammaWoldCubicDefectMoment N /
        xiMassNthPrimeLogHeight N ^ (3 : ℕ)) atTop (nhds 0) := by
  have h :=
    tendsto_sourceHorizontalEulerGammaWoldCubicDefectMoment_normalized_zero.const_mul (-2)
  convert h using 1
  · funext N
    ring
  · norm_num

/-- The completed-residue grade-forgetting normalization collapses to zero and therefore cannot
land the nonzero wall--Xi cubic Malgrange residual. -/
theorem not_tendsto_sourceHorizontalEulerWoldNormalizedCubicDefect_to_xiResidual :
    ¬ Tendsto (fun N : ℕ =>
      (-2 : ℝ) * sourceHorizontalEulerGammaWoldCubicDefectMoment N /
        xiMassNthPrimeLogHeight N ^ (3 : ℕ)) atTop
      (nhds (normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 0 ^ (3 : ℕ) / 4)) := by
  intro hbad
  have heq : (0 : ℝ) = normalizedPrimeArchMoment 2 -
      normalizedPrimeArchMoment 0 ^ (3 : ℕ) / 4 :=
    tendsto_nhds_unique tendsto_sourceHorizontalEulerWoldNormalizedCubicDefect_zero hbad
  have hneg := normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg
  linarith

/-- Canonical odd Stokes orientation landing. The normalized completed-residue channel is ruled
out, while every unnormalized source cutoff and its nonzero limit occupy the same strict negative
chamber as the wall--Xi cubic residual. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallCanonicalNegativeCubicOrientationLanding
    {X : ℕ} (hX : 3 ≤ X) :
    sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent X < 0 ∧
      -(∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n) < 0 ∧
      Tendsto sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent atTop
        (nhds (-∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n)) ∧
      0 < (normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ (3 : ℕ) / 4) *
        sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent X ∧
      0 < (normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ (3 : ℕ) / 4) *
        (-(∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n)) := by
  have hresidual := normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg
  have hfinite :=
    sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent_neg hX
  have hlimit := sourceHorizontalEulerGammaCubicNaturalRenormalizedLimit_neg
  exact ⟨hfinite, hlimit,
    tendsto_sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent,
    mul_pos_of_neg_of_neg hresidual hfinite,
    mul_pos_of_neg_of_neg hresidual hlimit⟩

end

end RHTower
