import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionRelativeSourceCoercivity
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionTerminalCurvatureRecession

/-!
# Projective arithmetic surplus of canonical shifted-Xi admission

The literal adaptive mixed/completed `P^sharp` source has a stronger use than sign or a fixed
linear report.  After intrinsic admitted-norm normalization and subtraction of the endogenous
Jacobi drift, it leaves the strict weighted-Cauchy surplus

`(2n+1) D_n - F_n^(2 : ℕ)`.

Dividing by `F_n^(2 : ℕ)` gives the velocity of the reciprocal projective flux clock.  In the normalized
far-right gauge this arithmetic work rate tends exactly to one at every fixed positive degree.
Thus monic norm collapse and coordinate dilation do not erase the producer; only diagonal
degree/mass shape escape remains.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Dimensionless Jacobi dissipation in the reciprocal-mass recession gauge. -/
def dimensionlessCumulativeJacobiDissipation (w : ℝ) (n : ℕ) : ℝ :=
  let s := xiShiftedFarRightNormalizedMoment w
  2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
    HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ) +
    4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
    2 * (n + 1 : ℝ) *
      (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1))

/-- Literal source surplus after removing current Jacobi drift and squared-flux transport.
`relativeArithmeticSource` is the mass-scaled rational--Gamma-minus-von-Mangoldt aggregate divided
by the intrinsic admitted norm. -/
def dimensionlessProjectiveArithmeticSurplus (w : ℝ) (n : ℕ) : ℝ :=
  let s := xiShiftedFarRightNormalizedMoment w
  let alpha := HTGeometry.monicOrthoAlpha s n
  let F := dimensionlessCumulativeJacobiFlux w n
  (2 * n + 1 : ℝ) *
      (2 * relativeArithmeticSource w n - alpha * F - 2 * (n : ℝ) * alpha ^ (2 : ℕ)) -
    F ^ (2 : ℕ)

/-- Scale-free nonlinear arithmetic work per squared cumulative-flux amplitude. -/
def dimensionlessProjectiveArithmeticWorkRate (w : ℝ) (n : ℕ) : ℝ :=
  dimensionlessProjectiveArithmeticSurplus w n /
    dimensionlessCumulativeJacobiFlux w n ^ (2 : ℕ)

/-- Exact energy/dissipation decomposition in the normalized recession gauge. -/
theorem two_mul_adaptiveOrthoJacobiEnergy_eq_dimensionlessDissipation_add_riccatiDrift
    (w : ℝ) (n : ℕ) :
    2 * HTGeometry.adaptiveOrthoJacobiEnergy
        (xiShiftedFarRightNormalizedMoment w) n =
      dimensionlessCumulativeJacobiDissipation w n +
        HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) n *
          dimensionlessCumulativeJacobiFlux w n +
        2 * (n : ℝ) *
          HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) n ^ (2 : ℕ) := by
  let s := xiShiftedFarRightNormalizedMoment w
  let alpha := HTGeometry.monicOrthoAlpha s n
  have hsquares :
      (∑ j ∈ Finset.range n,
          (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ (2 : ℕ)) =
        (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
          alpha * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
          (n : ℝ) * alpha ^ (2 : ℕ) / 4 := by
    have hpoint (j : ℕ) :
        (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ (2 : ℕ) =
          HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ) +
            alpha * HTGeometry.monicOrthoAlpha s j + alpha ^ (2 : ℕ) / 4 := by
      ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  simp only [HTGeometry.adaptiveOrthoJacobiEnergy,
    dimensionlessCumulativeJacobiDissipation,
    dimensionlessCumulativeJacobiFlux]
  change 2 *
      ((∑ j ∈ Finset.range n,
          (HTGeometry.monicOrthoAlpha s j + alpha / 2) ^ (2 : ℕ)) +
        (3 * (n : ℝ) / 4 + 1) * alpha ^ (2 : ℕ) +
        2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
        (n + 1 : ℝ) *
          (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1))) = _
  rw [hsquares]
  dsimp only [alpha]
  ring

/-- Strict projective Cauchy gap in every normalized positive admission block. -/
theorem dimensionlessCumulativeJacobiFlux_sq_lt_mul_dissipation
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    dimensionlessCumulativeJacobiFlux w n ^ (2 : ℕ) <
      (2 * n + 1 : ℝ) * dimensionlessCumulativeJacobiDissipation w n := by
  let s := xiShiftedFarRightNormalizedMoment w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hcs := cumulativeJacobiTrace_sq_le_mul_alphaEnergy
    (fun j => HTGeometry.monicOrthoAlpha s j)
    (HTGeometry.monicOrthoAlpha s n) hn
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below hbelow (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hboundary : 0 < HTGeometry.monicOrthoBeta s n +
      HTGeometry.monicOrthoBeta s (n + 1) :=
    add_pos
      (HTGeometry.monicOrthoBeta_pos_below hbelow hn (by omega))
      (HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega))
  simp only [dimensionlessCumulativeJacobiFlux,
    dimensionlessCumulativeJacobiDissipation]
  change (2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
      HTGeometry.monicOrthoAlpha s n) ^ (2 : ℕ) < _
  have hweight : 0 < (2 * n + 1 : ℝ) := by positivity
  have hextra : 0 <
      4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
        2 * (n + 1 : ℝ) *
          (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1)) := by
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hbetas)
      (mul_pos (mul_pos (by norm_num) (by positivity)) hboundary)
  have henergyLt :
      2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
          HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ) <
        2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
          HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ) +
          4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
          2 * (n + 1 : ℝ) *
            (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1)) := by
    linarith
  exact lt_of_le_of_lt hcs (mul_lt_mul_of_pos_left henergyLt hweight)

/-- **Exact source law.** The nonlinear literal arithmetic surplus is exactly the strict
weighted-Cauchy gap of the current Jacobi flag. -/
theorem dimensionlessProjectiveArithmeticSurplus_eq_cauchyGap
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    dimensionlessProjectiveArithmeticSurplus w n =
      (2 * n + 1 : ℝ) * dimensionlessCumulativeJacobiDissipation w n -
        dimensionlessCumulativeJacobiFlux w n ^ (2 : ℕ) := by
  have hsource := relativeArithmeticSource_eq_adaptiveOrthoJacobiEnergy hw hn hH
  have henergy :=
    two_mul_adaptiveOrthoJacobiEnergy_eq_dimensionlessDissipation_add_riccatiDrift w n
  unfold dimensionlessProjectiveArithmeticSurplus
  dsimp only
  rw [hsource, henergy]
  ring

/-- The admission-sensitive arithmetic producer has strictly positive projective surplus in every
normalized positive block. -/
theorem dimensionlessProjectiveArithmeticSurplus_pos
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    0 < dimensionlessProjectiveArithmeticSurplus w n := by
  rw [dimensionlessProjectiveArithmeticSurplus_eq_cauchyGap hw hn hH]
  exact sub_pos.mpr (dimensionlessCumulativeJacobiFlux_sq_lt_mul_dissipation hn hH)

/-- Fixed-degree normalized arithmetic surplus has the exact arcsine boundary `c^(2 : ℕ)/4`. -/
theorem tendsto_dimensionlessProjectiveArithmeticSurplus
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ => dimensionlessProjectiveArithmeticSurplus w n) atTop
      (nhds ((((2 * n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4)) := by
  have hsource := tendsto_relativeArithmeticSource hn
  have halpha := tendsto_dimensionless_monicOrthoAlpha n
  have hflux := tendsto_dimensionlessCumulativeJacobiFlux n
  have hinner := ((hsource.const_mul 2).sub (halpha.mul hflux)).sub
    ((halpha.pow 2).const_mul (2 * (n : ℝ)))
  have h := (hinner.const_mul (2 * n + 1 : ℝ)).sub (hflux.pow 2)
  convert h using 1
  · funext w
    simp only [dimensionlessProjectiveArithmeticSurplus]
  · push_cast
    congr 1
    ring

/-- **One-unit recession law.** Arithmetic projective work per squared flux tends exactly to one,
independently of fixed positive degree. -/
theorem tendsto_dimensionlessProjectiveArithmeticWorkRate_one
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ => dimensionlessProjectiveArithmeticWorkRate w n)
      atTop (nhds 1) := by
  have hsurplus := tendsto_dimensionlessProjectiveArithmeticSurplus hn
  have hflux := (tendsto_dimensionlessCumulativeJacobiFlux n).pow 2
  have hden : ((((2 * n + 1 : ℕ) : ℝ) / 2) ^ (2 : ℕ)) ≠ 0 := by
    positivity
  have h := hsurplus.div hflux hden
  convert h using 1
  · funext w
    rfl
  · push_cast
    have hc : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hc]
    norm_num

/-- Raw literal arithmetic surplus in actual mass coordinates. -/
def xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus (w : ℝ) (n : ℕ) : ℝ :=
  let s := xiShiftedRealMomentSequence w
  let alpha := HTGeometry.monicOrthoAlpha s n
  let F := xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n
  let h := HTGeometry.monicOrthoNormSq s n
  let source := xiShiftedAdaptiveMixedCompletedArithmeticSource w
    (HTGeometry.monicMomentAdmissionPolynomial s n)
  (2 * n + 1 : ℝ) *
      (source / h - alpha * F - 2 * (n : ℝ) * alpha ^ (2 : ℕ)) - F ^ (2 : ℕ)

/-- Actual-mass literal source surplus is exactly `(2n+1)D-F^(2 : ℕ)`. -/
theorem xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_cauchyGap
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n =
      (2 * n + 1 : ℝ) *
          xiShiftedCanonicalAdmissionCumulativeJacobiDissipation (w ^ (2 : ℕ)) n -
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n ^ (2 : ℕ) := by
  have hsource :=
    xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy
      hw hn hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : 0 < HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n :=
    HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hratio :
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n) /
          HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n =
        2 * HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n := by
    rw [hsource]
    field_simp [ne_of_gt hnorm]
  have henergy := two_mul_adaptiveOrthoJacobiEnergy_eq_cumulativeDissipation_add_riccatiDrift
    hn hH
  have henergy' :
      2 * HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n =
        xiShiftedCanonicalAdmissionCumulativeJacobiDissipation (w ^ (2 : ℕ)) n +
          HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n *
            xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n +
          2 * (n : ℝ) *
            HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n ^ (2 : ℕ) := by
    change 2 * HTGeometry.adaptiveOrthoJacobiEnergy
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n = _
    exact henergy
  unfold xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus
  dsimp only
  rw [hratio, henergy']
  ring

/-- Actual adaptive mixed/completed arithmetic source has strict positive projective surplus in
every positive admission block. -/
theorem xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n := by
  rw [xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_cauchyGap hw hn hH]
  exact sub_pos.mpr
    (xiShiftedCanonicalAdmissionCumulativeJacobiFlux_sq_lt_mul_dissipation hn hH)

/-- **Drift-free arithmetic coercivity.** Completing the current-alpha square removes the
endogenous Riccati drift: literal completed source divided by admitted norm controls squared
cumulative flux with an explicit positive degree factor. -/
theorem mul_flux_sq_lt_mul_relativeCompletedSource
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    let s := xiShiftedRealMomentSequence w
    let F := xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n
    let source := xiShiftedAdaptiveMixedCompletedArithmeticSource w
      (HTGeometry.monicMomentAdmissionPolynomial s n)
    (6 * n - 1 : ℝ) * F ^ (2 : ℕ) <
      8 * (n : ℝ) * (2 * n + 1 : ℝ) *
        (source / HTGeometry.monicOrthoNormSq s n) := by
  let s := xiShiftedRealMomentSequence w
  let F := xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n
  let alpha := HTGeometry.monicOrthoAlpha s n
  let source := xiShiftedAdaptiveMixedCompletedArithmeticSource w
    (HTGeometry.monicMomentAdmissionPolynomial s n)
  let c : ℝ := (2 * n + 1 : ℝ)
  let R : ℝ := source / HTGeometry.monicOrthoNormSq s n
  have hsurplus := xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_pos hw hn hH
  have hbase : F ^ (2 : ℕ) < c * (R - alpha * F - 2 * (n : ℝ) * alpha ^ (2 : ℕ)) := by
    unfold xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus at hsurplus
    simpa only [s, F, alpha, source, c, R] using sub_pos.mp hsurplus
  have hnR : 0 < 8 * (n : ℝ) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hbase hnR
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hsquare : 0 ≤ c * (4 * (n : ℝ) * alpha + F) ^ (2 : ℕ) :=
    mul_nonneg hc (sq_nonneg _)
  dsimp only
  change (6 * (n : ℝ) - 1) * F ^ (2 : ℕ) < 8 * (n : ℝ) * c * R
  nlinarith

/-- Reciprocal projective clock of the degree-normalized cumulative Jacobi flux. -/
def xiShiftedCanonicalAdmissionArithmeticProjectiveClock (y : ℝ) (n : ℕ) : ℝ :=
  (xiShiftedCanonicalAdmissionRenormalizedJacobiFlux y n)⁻¹ - y

/-- **Dynamic arithmetic landing.** Wherever current flux is nonzero, literal arithmetic surplus
divided by squared flux is exactly velocity of the reciprocal projective clock. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionArithmeticProjectiveClock_eq_sourceWorkRate
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hF : xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n ≠ 0) :
    HasDerivAt
      (fun y => xiShiftedCanonicalAdmissionArithmeticProjectiveClock y n)
      (xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n /
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n ^ (2 : ℕ))
      (w ^ (2 : ℕ)) := by
  let c : ℝ := (2 * n + 1 : ℝ)
  have hc : 0 < c := by positivity
  have hflux := hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux
    (sq_pos_of_pos (lt_trans (by norm_num) hw)) hn hH
  have hU := hflux.div_const c
  have hUne : xiShiftedCanonicalAdmissionRenormalizedJacobiFlux (w ^ (2 : ℕ)) n ≠ 0 := by
    unfold xiShiftedCanonicalAdmissionRenormalizedJacobiFlux
    exact div_ne_zero hF (ne_of_gt hc)
  have hclock := (hU.inv hUne).sub (hasDerivAt_id (w ^ (2 : ℕ)))
  have hsurplus :=
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_cauchyGap hw hn hH
  apply hclock.congr_deriv
  rw [hsurplus]
  dsimp only [c] at hc ⊢
  field_simp [hF, ne_of_gt hc]

/-- Nonzero current flux converts strict literal source surplus into strictly forward projective
clock motion. -/
theorem deriv_xiShiftedCanonicalAdmissionArithmeticProjectiveClock_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hF : xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n ≠ 0) :
    0 < deriv
      (fun y => xiShiftedCanonicalAdmissionArithmeticProjectiveClock y n) (w ^ (2 : ℕ)) := by
  rw [(hasDerivAt_xiShiftedCanonicalAdmissionArithmeticProjectiveClock_eq_sourceWorkRate
    hw hn hH hF).deriv]
  exact div_pos (xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_pos hw hn hH)
    (sq_pos_of_ne_zero hF)

/-- Closed logical surface: every actual normalized positive admission block carries strict
literal projective arithmetic surplus. -/
theorem all_positiveAdmissionBlocks_carry_projectiveArithmeticSurplus :
    ∀ w : ℝ, 1 / 2 < w → ∀ n : ℕ, 0 < n →
      (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (n + 2)).PosDef →
      0 < xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n := by
  intro w hw n hn hH
  exact xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_pos hw hn hH

end
end XiShiftedCanonicalAdmission
end RHTower
