import GaloisForLFunctions.RHTower.BurnolCoPoissonIndicatorReciprocal
import GaloisForLFunctions.RHTower.BurnolCoPoissonIndicatorVector

/-!
# Unconditional inhabitation of Burnol's co-Poisson source layer

The indicator co-Poisson sum and the sum of its reciprocal seed are both real, measurable, bounded,
and square integrable.  Burnol's Schwartz-pairing intertwining therefore upgrades to an equality of
`L²` vectors.  Its restriction to the even carrier supplies the missing cosine-head condition and
produces an actual element of `BurnolCoPoissonSource b` for every `0 < b ≤ 1`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

private theorem norm_burnolCoPoissonRightSum_indicator_le_global
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (t : ℝ) :
    ‖burnolCoPoissonRightSum (coPoissonIndicatorSeed b) t‖ ≤
      2 * (4 * b + 4 / b) + (2 / b ^ 2 + 2 * Real.log b⁻¹) * (1 + 2 / b) := by
  have hprofile := norm_burnolCoPoissonRightSum_coPoissonIndicatorSeed_le_profile hb hb1 t
  have hC : 0 ≤
      2 * (4 * b + 4 / b) + (2 / b ^ 2 + 2 * Real.log b⁻¹) * (1 + 2 / b) := by
    have hlog := two_log_inv_nonneg hb hb1
    positivity
  have hinv : (1 + |t|)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by positivity : 0 < 1 + |t|)).2
      (by linarith [abs_nonneg t])
  exact hprofile.trans (mul_le_of_le_one_right hC hinv)

private theorem norm_burnolCoPoissonRightSum_reciprocalIndicator_le_global'
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (t : ℝ) :
    ‖burnolCoPoissonRightSum
        (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t‖ ≤
      4 + (2 / b + (b⁻¹ - b)) * (1 + 2 / b) := by
  have hprofile := norm_burnolCoPoissonRightSum_reciprocalIndicator_le_profile hb hb1 t
  have hgap : 0 ≤ b⁻¹ - b := sub_nonneg.mpr (le_inv_self_of_le_one hb hb1)
  have hC : 0 ≤ 4 + (2 / b + (b⁻¹ - b)) * (1 + 2 / b) := by positivity
  have hinv : (1 + |t|)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by positivity : 0 < 1 + |t|)).2
      (by linarith [abs_nonneg t])
  exact hprofile.trans (mul_le_of_le_one_right hC hinv)

/-- **The indicator co-Poisson vector satisfies Burnol's `L²` intertwining unconditionally.** -/
theorem fourierUnitary_coPoissonIndicatorEven
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    fourierUnitary
        ((memLp_two_burnolCoPoissonRightSum_coPoissonIndicatorSeed hb hb1).toLp _ : SoninL2) =
      (memLp_two_burnolCoPoissonRightSum_reciprocalIndicator hb hb1).toLp _ := by
  exact fourierUnitary_coPoissonVector hb
    (integrable_coPoissonIndicatorSeed b)
    (support_coPoissonIndicatorSeed b)
    (integrable_coPoissonReciprocalSeed_coPoissonIndicatorSeed hb)
    (support_coPoissonReciprocalSeed hb (support_coPoissonIndicatorSeed b))
    (measurable_burnolCoPoissonRightSum hb (measurable_coPoissonIndicatorSeed b)
      (support_coPoissonIndicatorSeed b))
    (norm_burnolCoPoissonRightSum_indicator_le_global hb hb1)
    (measurable_burnolCoPoissonRightSum hb
      (measurable_coPoissonReciprocalSeed_coPoissonIndicatorSeed hb)
      (support_coPoissonReciprocalSeed hb (support_coPoissonIndicatorSeed b)))
    (norm_burnolCoPoissonRightSum_reciprocalIndicator_le_global' hb hb1)
    (star_burnolCoPoissonRightSum_coPoissonIndicatorSeed hb hb1)
    (star_burnolCoPoissonRightSum_reciprocalIndicator hb hb1)
    (memLp_two_burnolCoPoissonRightSum_coPoissonIndicatorSeed hb hb1)
    (memLp_two_burnolCoPoissonRightSum_reciprocalIndicator hb hb1)

/-- The cosine transform of the indicator vector is represented almost everywhere by the
reciprocal-indicator co-Poisson sum. -/
theorem soninCosineUnitary_coPoissonIndicatorEven_ae
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ((((soninCosineUnitary (coPoissonIndicatorEven hb hb1) : evenSubspace) :
        SoninL2)) : ℝ → ℂ) =ᵐ[volume]
      burnolCoPoissonRightSum
        (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) := by
  have hvector :
      ((soninCosineUnitary (coPoissonIndicatorEven hb hb1) : evenSubspace) : SoninL2) =
        (memLp_two_burnolCoPoissonRightSum_reciprocalIndicator hb hb1).toLp _ := by
    change fourierUnitary
        ((memLp_two_burnolCoPoissonRightSum_coPoissonIndicatorSeed hb hb1).toLp _ : SoninL2) = _
    exact fourierUnitary_coPoissonIndicatorEven hb hb1
  rw [hvector]
  exact (memLp_two_burnolCoPoissonRightSum_reciprocalIndicator hb hb1).coeFn_toLp

/-- **The missing cosine head condition for the explicit indicator source.** -/
theorem soninHeadConstant_cosine_coPoissonIndicatorEven
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    SoninHeadConstant b
      (((soninCosineUnitary (coPoissonIndicatorEven hb hb1) : evenSubspace) : SoninL2) :
        ℝ → ℂ) :=
  soninHeadConstant_cosine_coPoissonIndicatorEven_of_intertwine hb hb1
    (soninCosineUnitary_coPoissonIndicatorEven_ae hb hb1)

/-- **An unconditional explicit inhabitant of Burnol's co-Poisson source layer.** -/
def coPoissonIndicatorSourceUnconditional
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : BurnolCoPoissonSource b :=
  coPoissonIndicatorSource hb hb1 (soninHeadConstant_cosine_coPoissonIndicatorEven hb hb1)

/-- **Burnol's co-Poisson source layer is nonempty for every `0 < b ≤ 1`.** -/
theorem nonempty_burnolCoPoissonSource
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : Nonempty (BurnolCoPoissonSource b) :=
  ⟨coPoissonIndicatorSourceUnconditional hb hb1⟩

end RHTower
