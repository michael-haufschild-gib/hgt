import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceFifthRootCurvature

/-!
# Cumulative endpoint-flux balance for the completed theta C5 wall

Global log-convexity of the squared-variable normalized flux is impossible for the completed theta
source: its super-exponential tail forces eventual local log-concavity.  The C5 numerator can
nevertheless remain nonnegative because it sees cumulative earlier flux.

This module gives the exact two-coordinate survivor.  Put

`m = t D / (2 A)` and `e = (t J - D) / (2 D)`,

where `A` is accumulated product drop, `D` is endpoint decay flux, and `J = D'`.  Global angle
concavity puts `m` in `(0, 1]`.  The ordinary divided-drop log-convexity numerator is exactly

`4 A^(2 : ℕ) (1 + m e - m^(2 : ℕ))`,

while the fifth-root C5 numerator is exactly

`4 A^(2 : ℕ) (6 - 2m - 4m^(2 : ℕ) + 5me)`.

Thus negative terminal elasticity is not itself an obstruction: it is weighted by the bounded
cumulative endpoint ratio `m`, which tends to the small-mass chamber in the cofinal tail.  The
remaining global source problem is the displayed sharp joint balance, not pointwise log-convexity
of the local flux.
-/

open Set

namespace RHTower

noncomputable section

/-- Fraction of accumulated drop still carried by the current endpoint flux. -/
def thetaCuspReflectedSourceCumulativeEndpointFluxRatio (u t : ℝ) : ℝ :=
  t * thetaCuspReflectedSourceDecayFlux u t /
    (2 * thetaCuspReflectedSourceFirstDrop u t)

/-- Squared-coordinate logarithmic elasticity of the normalized endpoint flux. -/
def thetaCuspReflectedSourceNormalizedFluxElasticity (u t : ℝ) : ℝ :=
  (t * thetaCuspReflectedSourceDecayFluxCurvature u t -
    thetaCuspReflectedSourceDecayFlux u t) /
      (2 * thetaCuspReflectedSourceDecayFlux u t)

/-- Dimensionless cumulative balance whose sign is exactly the source C5 sign. -/
def thetaCuspReflectedSourceCumulativeFluxC5Balance (u t : ℝ) : ℝ :=
  let m := thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t
  let e := thetaCuspReflectedSourceNormalizedFluxElasticity u t
  6 - 2 * m - 4 * m ^ (2 : ℕ) + 5 * m * e

/-- The cumulative endpoint ratio is one minus half the existing projective decrease defect. -/
theorem thetaCuspReflectedSourceCumulativeEndpointFluxRatio_eq_one_sub_half_defect
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t =
      1 - thetaCuspReflectedSourceNormalizedProjectiveDecreaseDefect u t / 2 := by
  have hA := (thetaCuspReflectedSourceFirstDrop_pos u ht).ne'
  unfold thetaCuspReflectedSourceCumulativeEndpointFluxRatio
    thetaCuspReflectedSourceNormalizedProjectiveDecreaseDefect
  field_simp [hA]
  ring

/-- Global angle concavity confines cumulative endpoint mass to the exact chamber `(0, 1]`. -/
theorem thetaCuspReflectedSourceCumulativeEndpointFluxRatio_mem_Ioc
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t ∈ Ioc 0 1 := by
  have hA := thetaCuspReflectedSourceFirstDrop_pos u ht
  have hD := thetaCuspReflectedSourceDecayFlux_pos u ht
  have hdelta :=
    thetaCuspReflectedSourceNormalizedProjectiveDecreaseDefect_mem_Icc u ht
  constructor
  · unfold thetaCuspReflectedSourceCumulativeEndpointFluxRatio
    positivity
  · unfold thetaCuspReflectedSourceCumulativeEndpointFluxRatio
    unfold thetaCuspReflectedSourceNormalizedProjectiveDecreaseDefect at hdelta
    have hnum : 0 ≤ 2 * thetaCuspReflectedSourceFirstDrop u t -
        t * thetaCuspReflectedSourceDecayFlux u t := by
      have hraw := (le_div_iff₀ hA).mp hdelta.1
      simpa only [zero_mul] using hraw
    apply (div_le_iff₀
      (by positivity : 0 < 2 * thetaCuspReflectedSourceFirstDrop u t)).2
    nlinarith

/-- Exact cumulative/local decomposition of ordinary divided-drop log-convexity. -/
theorem thetaCuspReflectedSourceDividedDropLogConvexityNumerator_eq_cumulativeFluxBalance
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceDividedDropLogConvexityNumerator u t =
      4 * thetaCuspReflectedSourceFirstDrop u t ^ (2 : ℕ) *
        (1 + thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t *
            thetaCuspReflectedSourceNormalizedFluxElasticity u t -
          thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t ^ (2 : ℕ)) := by
  have hA := (thetaCuspReflectedSourceFirstDrop_pos u ht).ne'
  have hD := (thetaCuspReflectedSourceDecayFlux_pos u ht).ne'
  unfold thetaCuspReflectedSourceDividedDropLogConvexityNumerator
    thetaCuspReflectedSourceCumulativeEndpointFluxRatio
    thetaCuspReflectedSourceNormalizedFluxElasticity
  field_simp [hA, hD]
  ring

/-- Ordinary divided-drop log-convexity is exactly a cumulative-mass/elasticity barrier. -/
theorem thetaCuspReflectedSourceDividedDropLogConvexityNumerator_nonneg_iff_cumulativeFluxBalance
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ thetaCuspReflectedSourceDividedDropLogConvexityNumerator u t ↔
      thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t ^ (2 : ℕ) ≤
        1 + thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t *
          thetaCuspReflectedSourceNormalizedFluxElasticity u t := by
  rw [thetaCuspReflectedSourceDividedDropLogConvexityNumerator_eq_cumulativeFluxBalance
    u ht]
  have hfactor :
      0 < 4 * thetaCuspReflectedSourceFirstDrop u t ^ (2 : ℕ) :=
    mul_pos (by norm_num) (sq_pos_of_pos
      (thetaCuspReflectedSourceFirstDrop_pos u ht))
  constructor
  · intro h
    have hb := (mul_nonneg_iff_of_pos_left hfactor).mp h
    linarith
  · intro h
    exact (mul_nonneg_iff_of_pos_left hfactor).mpr (by linarith)

/-- **Sharp survivor identity.**  C5 is a positive accumulated-drop factor times one bounded
endpoint-mass/local-elasticity balance. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_cumulativeFluxC5Balance
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceFifthRootCurvatureNumerator u t =
      4 * thetaCuspReflectedSourceFirstDrop u t ^ (2 : ℕ) *
        thetaCuspReflectedSourceCumulativeFluxC5Balance u t := by
  have hA := (thetaCuspReflectedSourceFirstDrop_pos u ht).ne'
  have hD := (thetaCuspReflectedSourceDecayFlux_pos u ht).ne'
  unfold thetaCuspReflectedSourceFifthRootCurvatureNumerator
    thetaCuspReflectedSourceCumulativeFluxC5Balance
    thetaCuspReflectedSourceCumulativeEndpointFluxRatio
    thetaCuspReflectedSourceNormalizedFluxElasticity
  dsimp only
  field_simp [hA, hD]
  ring

/-- Global C5 at one positive scale is exactly nonnegativity of the cumulative flux balance. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_iff_cumulativeFluxC5Balance
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator u t ↔
      0 ≤ thetaCuspReflectedSourceCumulativeFluxC5Balance u t := by
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_cumulativeFluxC5Balance u ht]
  exact mul_nonneg_iff_of_pos_left
    (mul_pos (by norm_num) (sq_pos_of_pos
      (thetaCuspReflectedSourceFirstDrop_pos u ht)))

/-- The C5 condition is equivalently a sharp budget on negative local flux elasticity. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_iff_cumulativeFluxLossBudget
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator u t ↔
      5 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t *
          (-thetaCuspReflectedSourceNormalizedFluxElasticity u t) ≤
        2 * (1 - thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t) *
          (2 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t + 3) := by
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_iff_cumulativeFluxC5Balance
    u ht]
  unfold thetaCuspReflectedSourceCumulativeFluxC5Balance
  dsimp only
  constructor <;> intro h <;> nlinarith

/-- Nonnegative local normalized-flux elasticity is an unconditional safe chamber for C5. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_of_fluxElasticity_nonneg
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (he : 0 ≤ thetaCuspReflectedSourceNormalizedFluxElasticity u t) :
    0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator u t := by
  apply
    (thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_iff_cumulativeFluxLossBudget
      u ht).mpr
  have hm := thetaCuspReflectedSourceCumulativeEndpointFluxRatio_mem_Ioc u ht
  have hloss :
      5 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t *
          (-thetaCuspReflectedSourceNormalizedFluxElasticity u t) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num) hm.1.le) (neg_nonpos.mpr he)
  have hreserve :
      0 ≤ 2 * (1 - thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t) *
        (2 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t + 3) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hm.2))
      (by nlinarith [hm.1] :
        0 ≤ 2 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t + 3)
  linarith

/-- **Failure localization.**  Every negative C5 scale has negative local elasticity and
strictly overspends the exact cumulative reserve. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_neg_forces_fluxLossBudgetFailure
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator u t < 0) :
    thetaCuspReflectedSourceNormalizedFluxElasticity u t < 0 ∧
      2 * (1 - thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t) *
          (2 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t + 3) <
        5 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t *
          (-thetaCuspReflectedSourceNormalizedFluxElasticity u t) := by
  have he : thetaCuspReflectedSourceNormalizedFluxElasticity u t < 0 := by
    by_contra hnot
    have hsafe :=
      thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_of_fluxElasticity_nonneg
        u ht (le_of_not_gt hnot)
    linarith
  refine ⟨he, ?_⟩
  have hnotBudget : ¬
      5 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t *
          (-thetaCuspReflectedSourceNormalizedFluxElasticity u t) ≤
        2 * (1 - thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t) *
          (2 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t + 3) := by
    intro hbudget
    have hsafe :=
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_iff_cumulativeFluxLossBudget
        u ht).mpr hbudget
    linarith
  exact lt_of_not_ge hnotBudget

end

end RHTower
