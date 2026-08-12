import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveArithmeticSurplus

/-!
# Projective arithmetic work lands in the next canonical admission

The literal adaptive mixed/completed source does not merely move one scalar projective clock.
Its drift-subtracted projective surplus splits before reflection aggregation into

* weighted variance of the two adjacent Jacobi traces;
* retained lower-edge inventory; and
* exactly `2(2n+1)(n+1)` copies of the next Christoffel edge.

Multiplication by the current monic norm converts that last edge into the next monic norm.  Thus
current arithmetic work capitalizes the next admission, with a strictly positive retained
inventory on every positive block.
-/

open Matrix Polynomial
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Weighted trace variance of the two adjacent monic Jacobi truncations. -/
def projectiveJacobiTraceVariance (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (2 * n + 1 : ℝ) *
      (2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ 2) +
        HTGeometry.monicOrthoAlpha s n ^ 2) -
    (2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
      HTGeometry.monicOrthoAlpha s n) ^ 2

/-- Variance of lower diagonal Jacobi coordinates around their own mean. -/
def projectiveJacobiLowerAlphaDispersion (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ 2) -
    (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) ^ 2 / (n : ℝ)

/-- Mismatch between lower diagonal mean and current diagonal coordinate. -/
def projectiveJacobiTerminalAlphaMismatch (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) -
    (n : ℝ) * HTGeometry.monicOrthoAlpha s n

/-- Projective inventory retained after the next Christoffel edge has been separated. -/
def projectiveJacobiRetainedInventory (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  projectiveJacobiTraceVariance s n +
    (2 * n + 1 : ℝ) *
      (4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
        2 * (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s n)

/-- Literal current-norm-scaled arithmetic work.  Source formation remains inside the projective
surplus; scaling only converts its next-edge quotient into an actual next admitted norm. -/
def xiShiftedCanonicalAdmissionProjectiveArithmeticWork (w : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n

/-- Current-norm-scaled Jacobi work retained after next admission has been capitalized. -/
def xiShiftedCanonicalAdmissionRetainedProjectiveArithmeticWork
    (w : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
    projectiveJacobiRetainedInventory (xiShiftedRealMomentSequence w) n

/-- Weighted Cauchy makes the adjacent-trace variance nonnegative. -/
theorem projectiveJacobiTraceVariance_nonneg
    (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    0 ≤ projectiveJacobiTraceVariance s n := by
  have hcs := cumulativeJacobiTrace_sq_le_mul_alphaEnergy
    (fun j => HTGeometry.monicOrthoAlpha s j)
    (HTGeometry.monicOrthoAlpha s n) hn
  unfold projectiveJacobiTraceVariance
  linarith

/-- Lower-coordinate dispersion is nonnegative by ordinary finite Cauchy. -/
theorem projectiveJacobiLowerAlphaDispersion_nonneg
    (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    0 ≤ projectiveJacobiLowerAlphaDispersion s n := by
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range n) (f := fun j => HTGeometry.monicOrthoAlpha s j)
  simp only [Finset.card_range] at hcs
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold projectiveJacobiLowerAlphaDispersion
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hnR).2
  simpa only [mul_comm] using hcs

/-- Exact two-scale decomposition of weighted trace variance.  Collapse requires both lower
diagonal dispersion and terminal-mean mismatch to collapse. -/
theorem projectiveJacobiTraceVariance_eq_dispersion_add_mismatch
    (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    projectiveJacobiTraceVariance s n =
      2 * (2 * n + 1 : ℝ) * projectiveJacobiLowerAlphaDispersion s n +
        2 / (n : ℝ) * projectiveJacobiTerminalAlphaMismatch s n ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold projectiveJacobiTraceVariance projectiveJacobiLowerAlphaDispersion
    projectiveJacobiTerminalAlphaMismatch
  field_simp [hn0]
  ring

theorem dispersion_part_le_projectiveJacobiTraceVariance
    (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    2 * (2 * n + 1 : ℝ) * projectiveJacobiLowerAlphaDispersion s n ≤
      projectiveJacobiTraceVariance s n := by
  rw [projectiveJacobiTraceVariance_eq_dispersion_add_mismatch s hn]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))

theorem mismatch_part_le_projectiveJacobiTraceVariance
    (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    2 / (n : ℝ) * projectiveJacobiTerminalAlphaMismatch s n ^ 2 ≤
      projectiveJacobiTraceVariance s n := by
  rw [projectiveJacobiTraceVariance_eq_dispersion_add_mismatch s hn]
  exact le_add_of_nonneg_left
    (mul_nonneg (by positivity)
      (projectiveJacobiLowerAlphaDispersion_nonneg s hn))

/-- **Exact next-edge split.**  The current literal arithmetic surplus contains the next
Christoffel edge with coefficient `2(2n+1)(n+1)`; everything else is retained Jacobi inventory. -/
theorem xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_nextEdge_add_retained
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n =
      2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
          HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) (n + 1) +
        projectiveJacobiRetainedInventory (xiShiftedRealMomentSequence w) n := by
  have hgap :=
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_cauchyGap hw hn hH
  have htrace := xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace hn hH
  rw [hgap, htrace]
  unfold xiShiftedCanonicalAdmissionCumulativeJacobiDissipation
    projectiveJacobiRetainedInventory projectiveJacobiTraceVariance
  have hs : xiShiftedRealMomentSequence w =
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) := rfl
  rw [hs]
  ring

/-- Retained inventory is strictly positive on every actual positive block.  The current edge
`beta_n` already gives strictness; no lower bound on the newborn next edge is assumed. -/
theorem projectiveJacobiRetainedInventory_pos
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    0 < projectiveJacobiRetainedInventory (xiShiftedRealMomentSequence w) n := by
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hvariance : 0 ≤ projectiveJacobiTraceVariance s n :=
    projectiveJacobiTraceVariance_nonneg s hn
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below hbelow (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hbeta : 0 < HTGeometry.monicOrthoBeta s n :=
    HTGeometry.monicOrthoBeta_pos_below hbelow hn (by omega)
  have hc : 0 < (2 * n + 1 : ℝ) := by positivity
  have hinterior : 0 <
      4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
        2 * (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s n := by
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hbetas)
      (mul_pos (mul_pos (by norm_num) (by positivity)) hbeta)
  unfold projectiveJacobiRetainedInventory
  simpa only [s] using add_pos_of_nonneg_of_pos hvariance (mul_pos hc hinterior)

/-- The next Christoffel edge consumes a strict proper part of current arithmetic surplus. -/
theorem nextEdge_lt_xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
        HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) (n + 1) <
      xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n := by
  rw [xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_nextEdge_add_retained
    hw hn hH]
  exact lt_add_of_pos_right _ (projectiveJacobiRetainedInventory_pos hn hH)

/-- **Source-first adjacent-admission law.**  Multiplying by current admitted norm converts the
newborn Christoffel quotient exactly into next admitted norm. -/
theorem xiShiftedCanonicalAdmissionProjectiveArithmeticWork_eq_nextNorm_add_retained
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionProjectiveArithmeticWork w n =
      2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
          HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n + 1) +
        xiShiftedCanonicalAdmissionRetainedProjectiveArithmeticWork w n := by
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : HTGeometry.monicOrthoNormSq s n ≠ 0 :=
    ne_of_gt (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega))
  have hedge :
      HTGeometry.monicOrthoNormSq s n * HTGeometry.monicOrthoBeta s (n + 1) =
        HTGeometry.monicOrthoNormSq s (n + 1) := by
    simp only [HTGeometry.monicOrthoBeta]
    exact mul_div_cancel₀ _ hnorm
  rw [xiShiftedCanonicalAdmissionProjectiveArithmeticWork,
    xiShiftedCanonicalAdmissionRetainedProjectiveArithmeticWork,
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_nextEdge_add_retained
      hw hn hH]
  change HTGeometry.monicOrthoNormSq s n *
      (2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
          HTGeometry.monicOrthoBeta s (n + 1) +
        projectiveJacobiRetainedInventory s n) = _
  rw [mul_add, show HTGeometry.monicOrthoNormSq s n *
      (2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
        HTGeometry.monicOrthoBeta s (n + 1)) =
      2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
        HTGeometry.monicOrthoNormSq s (n + 1) by
      calc
        HTGeometry.monicOrthoNormSq s n *
              (2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
                HTGeometry.monicOrthoBeta s (n + 1)) =
            2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
              (HTGeometry.monicOrthoNormSq s n *
                HTGeometry.monicOrthoBeta s (n + 1)) := by ring
        _ = 2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
              HTGeometry.monicOrthoNormSq s (n + 1) := by rw [hedge]]

/-- **Literal adaptive mixed/completed source landing.**  This is the adjacent-admission law with
the arithmetic producer exposed: admission, adaptive amplitude, and completion are formed before
Jacobi drift and projective transport are paid. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_projectiveWork_eq_nextNorm_add_retained
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    let s := xiShiftedRealMomentSequence w
    let alpha := HTGeometry.monicOrthoAlpha s n
    let F := xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n
    let h := HTGeometry.monicOrthoNormSq s n
    let source := xiShiftedAdaptiveMixedCompletedArithmeticSource w
      (HTGeometry.monicMomentAdmissionPolynomial s n)
    (2 * n + 1 : ℝ) *
        (source - h * (alpha * F + 2 * (n : ℝ) * alpha ^ 2)) - h * F ^ 2 =
      2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
          HTGeometry.monicOrthoNormSq s (n + 1) +
        xiShiftedCanonicalAdmissionRetainedProjectiveArithmeticWork w n := by
  dsimp only
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n ≠ 0 :=
    ne_of_gt (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega))
  rw [← xiShiftedCanonicalAdmissionProjectiveArithmeticWork_eq_nextNorm_add_retained
    hw hn hH]
  unfold xiShiftedCanonicalAdmissionProjectiveArithmeticWork
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus
  dsimp only
  field_simp [hnorm]
  ring

/-- Current literal arithmetic work strictly dominates the complete next monic admission norm. -/
theorem nextNorm_lt_xiShiftedCanonicalAdmissionProjectiveArithmeticWork
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
        HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n + 1) <
      xiShiftedCanonicalAdmissionProjectiveArithmeticWork w n := by
  rw [xiShiftedCanonicalAdmissionProjectiveArithmeticWork_eq_nextNorm_add_retained
    hw hn hH]
  apply lt_add_of_pos_right
  unfold xiShiftedCanonicalAdmissionRetainedProjectiveArithmeticWork
  exact mul_pos
    (HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega))
    (projectiveJacobiRetainedInventory_pos hn hH)

/-- Closed logical surface: every positive canonical block carries a strict source-capitalized
landing into its next admitted norm. -/
theorem all_positiveAdmissionBlocks_carry_nextAdmissionProjectiveArithmeticWork :
    ∀ w : ℝ, 1 / 2 < w → ∀ n : ℕ, 0 < n →
      (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (n + 2)).PosDef →
      2 * (2 * n + 1 : ℝ) * (n + 1 : ℝ) *
          HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n + 1) <
        xiShiftedCanonicalAdmissionProjectiveArithmeticWork w n := by
  intro w hw n hn hH
  exact nextNorm_lt_xiShiftedCanonicalAdmissionProjectiveArithmeticWork hw hn hH

end
end XiShiftedCanonicalAdmission
end RHTower
