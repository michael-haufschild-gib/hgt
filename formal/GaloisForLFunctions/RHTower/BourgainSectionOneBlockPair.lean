/-
# Unconditional Section-1 block-pair geometry

Bourgain's multiplicative bootstrap partitions two separated arcs into
shorter consecutive blocks and applies the sharp normalized exact-curve
estimate to every block pair.  This module makes the scale choice literal.

For `J` coarse blocks of `H` samples, take denominator `D = 4 J H`.
The left blocks start at `i/(4J)` and the right blocks at `1/2+j/(4J)`.
Thus every block stays in `[0,1]`, every pair is separated by at least
`1/4`, and the sole Taylor condition follows from
`J >= 6 * C_Taylor * H^2`.
-/
import GaloisForLFunctions.RHTower.BourgainNormalizedCellDecoupling
import GaloisForLFunctions.RHTower.BourgainSectionOneScaleSelection

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Common sample denominator for the explicit Section-1 two-arc block
partition. -/
def bourgainSectionOneBlockDenominator (J H : ℕ) : ℝ :=
  4 * (J : ℝ) * (H : ℝ)

/-- Base of left coarse block `i`. -/
def bourgainSectionOneLeftBlockBase (J : ℕ) (i : Fin J) : ℝ :=
  (i : ℝ) / (4 * (J : ℝ))

/-- Base of right coarse block `j`. -/
def bourgainSectionOneRightBlockBase (J : ℕ) (j : Fin J) : ℝ :=
  1 / 2 + (j : ℝ) / (4 * (J : ℝ))

/-- Explicit coarse-block count saturating the normalized Taylor threshold.
The numeral is `6 * 50331648000`. -/
def bourgainSectionOneCoarseBlockCount (H : ℕ) : ℕ :=
  301989888000 * H ^ (2 : ℕ)

theorem bourgainSectionOneCoarseBlockCount_pos
    {H : ℕ} (hH : 0 < H) :
    0 < bourgainSectionOneCoarseBlockCount H := by
  unfold bourgainSectionOneCoarseBlockCount
  positivity

theorem bourgainSectionOneCoarseBlockCount_cast
    (H : ℕ) :
    (bourgainSectionOneCoarseBlockCount H : ℝ) =
      6 * bourgainSectionOneTaylorConstant * (H : ℝ) ^ (2 : ℕ) := by
  norm_num [bourgainSectionOneCoarseBlockCount,
    bourgainSectionOneTaylorConstant]

theorem bourgainSectionOneBlockDenominator_pos
    {J H : ℕ} (hJ : 0 < J) (hH : 0 < H) :
    0 < bourgainSectionOneBlockDenominator J H := by
  unfold bourgainSectionOneBlockDenominator
  positivity

theorem bourgainSectionOneBlockLength_div_denominator
    {J H : ℕ} (hJ : 0 < J) (hH : 0 < H) :
    (H : ℝ) / bourgainSectionOneBlockDenominator J H =
      1 / (4 * (J : ℝ)) := by
  have hJ0 : (J : ℝ) ≠ 0 := by positivity
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  unfold bourgainSectionOneBlockDenominator
  field_simp

theorem bourgainSectionOneLeftBlockBase_nonneg
    {J : ℕ} (hJ : 0 < J) (i : Fin J) :
    0 ≤ bourgainSectionOneLeftBlockBase J i := by
  unfold bourgainSectionOneLeftBlockBase
  positivity

theorem bourgainSectionOneRightBlockBase_nonneg
    {J : ℕ} (hJ : 0 < J) (j : Fin J) :
    0 ≤ bourgainSectionOneRightBlockBase J j := by
  unfold bourgainSectionOneRightBlockBase
  positivity

/-- Every left block, including its full length, lies below `1/4`. -/
theorem bourgainSectionOneLeftBlock_end_le_quarter
    {J H : ℕ} (hJ : 0 < J) (hH : 0 < H) (i : Fin J) :
    bourgainSectionOneLeftBlockBase J i +
        (H : ℝ) / bourgainSectionOneBlockDenominator J H ≤ 1 / 4 := by
  rw [bourgainSectionOneBlockLength_div_denominator hJ hH]
  unfold bourgainSectionOneLeftBlockBase
  have hi : (i : ℕ) + 1 ≤ J := i.isLt
  have hiR : (i : ℝ) + 1 ≤ (J : ℝ) := by exact_mod_cast hi
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  calc
    (i : ℝ) / (4 * (J : ℝ)) + 1 / (4 * (J : ℝ)) =
        ((i : ℝ) + 1) / (4 * (J : ℝ)) := by ring
    _ ≤ (J : ℝ) / (4 * (J : ℝ)) :=
      div_le_div_of_nonneg_right hiR (by positivity)
    _ = 1 / 4 := by field_simp

/-- Every right block, including its full length, lies below `3/4`. -/
theorem bourgainSectionOneRightBlock_end_le_threeQuarter
    {J H : ℕ} (hJ : 0 < J) (hH : 0 < H) (j : Fin J) :
    bourgainSectionOneRightBlockBase J j +
        (H : ℝ) / bourgainSectionOneBlockDenominator J H ≤ 3 / 4 := by
  rw [bourgainSectionOneBlockLength_div_denominator hJ hH]
  unfold bourgainSectionOneRightBlockBase
  have hj : (j : ℕ) + 1 ≤ J := j.isLt
  have hjR : (j : ℝ) + 1 ≤ (J : ℝ) := by exact_mod_cast hj
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  calc
    1 / 2 + (j : ℝ) / (4 * (J : ℝ)) + 1 / (4 * (J : ℝ)) =
        1 / 2 + ((j : ℝ) + 1) / (4 * (J : ℝ)) := by ring
    _ ≤ 1 / 2 + (J : ℝ) / (4 * (J : ℝ)) := by
      gcongr
    _ = 3 / 4 := by
      field_simp
      norm_num

/-- Left and right blocks retain the uniform `1/4` separation required by
the normalized exact-curve theorem. -/
theorem bourgainSectionOneBlockBases_separated
    {J : ℕ} (hJ : 0 < J) (i j : Fin J) :
    1 / 4 ≤
      bourgainSectionOneRightBlockBase J j -
        bourgainSectionOneLeftBlockBase J i := by
  unfold bourgainSectionOneRightBlockBase
    bourgainSectionOneLeftBlockBase
  have hi : (i : ℕ) ≤ J := i.isLt.le
  have hiR : (i : ℝ) ≤ (J : ℝ) := by exact_mod_cast hi
  have hjR : (0 : ℝ) ≤ j := by positivity
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hleft : (i : ℝ) / (4 * (J : ℝ)) ≤ 1 / 4 := by
    calc
      (i : ℝ) / (4 * (J : ℝ)) ≤
          (J : ℝ) / (4 * (J : ℝ)) :=
        div_le_div_of_nonneg_right hiR (by positivity)
      _ = 1 / 4 := by field_simp
  have hright : 1 / 2 ≤ 1 / 2 + (j : ℝ) / (4 * (J : ℝ)) := by
    have : 0 ≤ (j : ℝ) / (4 * (J : ℝ)) := by positivity
    linarith
  linarith

/-- Coarse-block count dominating `6 C_Taylor H^2` forces the exact cubic
Taylor smallness condition for every block pair. -/
theorem bourgainSectionOneBlock_taylor_small
    {J H : ℕ} (hJ : 0 < J) (hH : 0 < H)
    (hscale :
      6 * bourgainSectionOneTaylorConstant * (H : ℝ) ^ (2 : ℕ) ≤ J) :
    bourgainSectionOneTaylorConstant * (H : ℝ) ^ (3 : ℕ) /
        bourgainSectionOneBlockDenominator J H ≤ 1 / 24 := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  unfold bourgainSectionOneBlockDenominator
  apply (div_le_iff₀ (by positivity : 0 < 4 * (J : ℝ) * (H : ℝ))).2
  have hmul := mul_le_mul_of_nonneg_right hscale hHr.le
  nlinarith [sq_nonneg (H : ℝ)]

/-- **Unconditional sharp estimate for every Section-1 coarse block pair.**

All geometric premises of normalized exact-curve decoupling are discharged
by the explicit two-arc partition and one quantitative scale inequality. -/
theorem
    setLIntegral_bourgainSectionOneBlockPair_fundamentalCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J H : ℕ) (_hJ : 0 < J) (_hH : 0 < H)
        (_hscale :
          6 * bourgainSectionOneTaylorConstant *
              (H : ℝ) ^ (2 : ℕ) ≤ J)
        {q : ℝ} (_hq : 0 < q) (_hq1 : q ≤ 1 / 2)
        (i j : Fin J) (c₁ c₂ : Fin H → ℂ),
        let D := bourgainSectionOneBlockDenominator J H
        let a := bourgainSectionOneLeftBlockBase J i
        let b := bourgainSectionOneRightBlockBase J j
        let φ₃ := bourgainNormalizedCubicRemainder q
        let φ₄ := bourgainNormalizedQuarticRemainder q
        (∫⁻ x in bourgainGenericOsculatingFundamentalCell
            H φ₃ φ₄ ((H : ℝ) / D) a b,
          ENNReal.ofReal
            (‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
              ‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))) ≤
          ENNReal.ofReal
              |((((H : ℝ) / D) ^ (6 : ℕ)) *
                (bourgainGenericPhaseCoordinateMatrix
                  φ₃ φ₄ a b).det)⁻¹| *
            ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hcell⟩ :=
    setLIntegral_bourgainNormalizedExactLocalSum_fundamentalCell_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro J H hJ hH hscale q hq hq1 i j c₁ c₂
  dsimp only
  let D := bourgainSectionOneBlockDenominator J H
  let a := bourgainSectionOneLeftBlockBase J i
  let b := bourgainSectionOneRightBlockBase J j
  have hD : 0 < D := bourgainSectionOneBlockDenominator_pos hJ hH
  have hHD : (H : ℝ) ≤ D := by
    unfold D bourgainSectionOneBlockDenominator
    have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hHr : (0 : ℝ) ≤ H := by positivity
    nlinarith
  have ha0 : 0 ≤ a := bourgainSectionOneLeftBlockBase_nonneg hJ i
  have ha1 : a + (H : ℝ) / D ≤ 1 :=
    (bourgainSectionOneLeftBlock_end_le_quarter hJ hH i).trans
      (by norm_num)
  have hb0 : 0 ≤ b := bourgainSectionOneRightBlockBase_nonneg hJ j
  have hb1 : b + (H : ℝ) / D ≤ 1 :=
    (bourgainSectionOneRightBlock_end_le_threeQuarter hJ hH j).trans
      (by norm_num)
  have hab : 1 / 4 ≤ b - a :=
    bourgainSectionOneBlockBases_separated hJ i j
  have hsmall :
      bourgainSectionOneTaylorConstant * (H : ℝ) ^ (3 : ℕ) / D ≤
        1 / 24 :=
    bourgainSectionOneBlock_taylor_small hJ hH hscale
  exact hcell H hH hq hq1 hD hHD ha0 ha1 hb0 hb1 hab hsmall c₁ c₂

/-- **Closed explicit-scale Section-1 block-pair estimate.**

For every positive fine scale `H`, the canonical coarse count
`301989888000 H²` makes every left/right block pair admissible for the sharp
exact-curve cell theorem.  No analytic or geometric hypothesis remains
beyond positivity of the curve parameter and its fixed normalized range. -/
theorem
    setLIntegral_bourgainSectionOneCanonicalBlockPair_fundamentalCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (_hH : 0 < H)
        {q : ℝ} (_hq : 0 < q) (_hq1 : q ≤ 1 / 2)
        (i j : Fin (bourgainSectionOneCoarseBlockCount H))
        (c₁ c₂ : Fin H → ℂ),
        let J := bourgainSectionOneCoarseBlockCount H
        let D := bourgainSectionOneBlockDenominator J H
        let a := bourgainSectionOneLeftBlockBase J i
        let b := bourgainSectionOneRightBlockBase J j
        let φ₃ := bourgainNormalizedCubicRemainder q
        let φ₄ := bourgainNormalizedQuarticRemainder q
        (∫⁻ x in bourgainGenericOsculatingFundamentalCell
            H φ₃ φ₄ ((H : ℝ) / D) a b,
          ENNReal.ofReal
            (‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
              ‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))) ≤
          ENNReal.ofReal
              |((((H : ℝ) / D) ^ (6 : ℕ)) *
                (bourgainGenericPhaseCoordinateMatrix
                  φ₃ φ₄ a b).det)⁻¹| *
            ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hpair⟩ :=
    setLIntegral_bourgainSectionOneBlockPair_fundamentalCell_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H hH q hq hq1 i j c₁ c₂
  dsimp only
  let J := bourgainSectionOneCoarseBlockCount H
  have hJ : 0 < J := bourgainSectionOneCoarseBlockCount_pos hH
  have hscale :
      6 * bourgainSectionOneTaylorConstant * (H : ℝ) ^ (2 : ℕ) ≤ J := by
    rw [← bourgainSectionOneCoarseBlockCount_cast H]
  exact hpair J H hJ hH hscale hq hq1 i j c₁ c₂

end

end RHTower
