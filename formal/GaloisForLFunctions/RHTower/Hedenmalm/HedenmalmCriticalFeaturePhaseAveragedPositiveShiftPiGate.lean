import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeaturePhaseAveragedPositiveShiftRenderer
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureBoundaryCapacityAsymptotic

/-!
# Sharp single-scale positive-shift gate for 75% on the critical line

The phase-averaged renderer has a boundary limit at each canonical height.  Choose one positive
submicroscopic shift where its error is below `1 / (n + 1)`.  This choice is made entirely from
the zero-independent source renderer.  The selected finite-shift sequence converges to zero and
differs from exact HCF phase covariance by `o(N)`.

Consequently the explicit pole--Gamma--von-Mangoldt renderer has asymptotic ceiling `π` if and
only if at least three quarters of canonical Xi multiplicity lies on the critical line.  This
removes nested boundary limits, phasewise limits, and any divisor-selected displacement from the
remaining quantitative problem.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem eventually_abs_sub_lt_of_tendsto_phaseRenderer
    {alpha : Type*} {l : Filter alpha} {f : alpha → ℝ} {a eps : ℝ}
    (h : Tendsto f l (𝓝 a)) (heps : 0 < eps) :
    ∀ᶠ x in l, |f x - a| < eps := by
  have hlo : ∀ᶠ x in l, a - eps < f x :=
    (tendsto_order.1 h).1 _ (by linarith)
  have hhi : ∀ᶠ x in l, f x < a + eps :=
    (tendsto_order.1 h).2 _ (by linarith)
  filter_upwards [hlo, hhi] with x hxlo hxhi
  rw [abs_lt]
  constructor <;> linarith

/-- One positive submicroscopic source evaluation approximating exact phase covariance. -/
structure CriticalFeaturePhaseAveragedPositiveShiftData (n : ℕ) where
  shift : ℝ
  shift_pos : 0 < shift
  shift_lt_half : shift < 1 / 2
  shift_lt_reciprocal : shift < 1 / ((n : ℝ) + 1)
  error_lt :
    |criticalFeaturePhaseAveragedPoleGammaCovarianceAtShift n shift -
      criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n| <
        1 / ((n : ℝ) + 1)

theorem exists_criticalFeaturePhaseAveragedPositiveShiftData (n : ℕ) :
    Nonempty (CriticalFeaturePhaseAveragedPositiveShiftData n) := by
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have heps : 0 < eps := by positivity
  have hnear : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ),
      |criticalFeaturePhaseAveragedPoleGammaCovarianceAtShift n eta -
        criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n| < eps :=
    eventually_abs_sub_lt_of_tendsto_phaseRenderer
      (tendsto_criticalFeaturePhaseAveragedPoleGammaCovarianceAtShift n) heps
  have hpos : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), 0 < eta := self_mem_nhdsWithin
  have hhalf : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  have hepsNear : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta < eps :=
    (eventually_lt_nhds heps).filter_mono inf_le_left
  obtain ⟨eta, hetaPos, hetaHalf, hetaEps, hetaNear⟩ :=
    (hpos.and (hhalf.and (hepsNear.and hnear))).exists
  exact ⟨{
    shift := eta
    shift_pos := hetaPos
    shift_lt_half := hetaHalf
    shift_lt_reciprocal := by simpa only [eps] using hetaEps
    error_lt := by simpa only [eps] using hetaNear }⟩

/-- Canonical source-defined positive-shift datum at height `n`. -/
def criticalFeaturePhaseAveragedPositiveShiftData (n : ℕ) :
    CriticalFeaturePhaseAveragedPositiveShiftData n :=
  Classical.choice (exists_criticalFeaturePhaseAveragedPositiveShiftData n)

/-- Single-scale source statistic: one explicit positive-shift evaluation per height. -/
def criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance (n : ℕ) : ℝ :=
  criticalFeaturePhaseAveragedPoleGammaCovarianceAtShift n
    (criticalFeaturePhaseAveragedPositiveShiftData n).shift

theorem tendsto_criticalFeaturePhaseAveragedPositiveShiftData_shift :
    Tendsto (fun n : ℕ =>
      (criticalFeaturePhaseAveragedPositiveShiftData n).shift)
      atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    have h := tendsto_atTop_add_const_left atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop
    convert h using 1
    funext n
    ring
  have hrecip : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    rw [show (fun n : ℕ => 1 / ((n : ℝ) + 1)) =
        (fun r : ℝ => r⁻¹) ∘ (fun n : ℕ => (n : ℝ) + 1) by
      funext n
      simp only [Function.comp_apply, one_div]]
    exact tendsto_inv_atTop_zero.comp hden
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      (criticalFeaturePhaseAveragedPositiveShiftData n).shift_pos.le)
    (Filter.Eventually.of_forall fun n =>
      (criticalFeaturePhaseAveragedPositiveShiftData n).shift_lt_reciprocal.le)
    hrecip

theorem criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance_error_lt
    (n : ℕ) :
    |criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance n -
      criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n| <
        1 / ((n : ℝ) + 1) :=
  (criticalFeaturePhaseAveragedPositiveShiftData n).error_lt

/-- Positive-shift boundary integral selected at the same canonical source scale. -/
def criticalFeatureCanonicalPhaseAveragedPositiveShiftBoundary (n : ℕ) : ℝ :=
  criticalFeaturePhaseAveragedCompactPoleGammaObservable n
    (criticalFeaturePhaseAveragedPositiveShiftData n).shift

/-- Canonical single-shift renderer and exact phase covariance differ by `o(N)`. -/
theorem tendsto_canonicalPhaseAveragedPositiveShiftCovariance_sub_phaseCovariance_div :
    Tendsto
      (fun n : ℕ =>
        (criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance n -
          criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n) /
            criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  have hlow : Tendsto
      (fun n : ℕ => -(1 / criticalFeatureCanonicalZeroCount n))
      atTop (𝓝 0) := by
    simpa using tendsto_one_div_criticalFeatureCanonicalZeroCount.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow
      tendsto_one_div_criticalFeatureCanonicalZeroCount
  · intro n
    by_cases hN : criticalFeatureCanonicalZeroCount n = 0
    · simp [hN]
    have hNnonneg : (0 : ℝ) ≤ criticalFeatureCanonicalZeroCount n := by
      unfold criticalFeatureCanonicalZeroCount
      exact_mod_cast xiZeroCount_nonneg (n : ℝ)
    have hNpos : 0 < criticalFeatureCanonicalZeroCount n :=
      lt_of_le_of_ne hNnonneg (Ne.symm hN)
    have herr := criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance_error_lt n
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num
    have habs :
        |criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance n -
          criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n| ≤ 1 :=
      (le_of_lt herr).trans hone
    have habsdiv :
        |(criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance n -
          criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n) /
            criticalFeatureCanonicalZeroCount n| ≤
          1 / criticalFeatureCanonicalZeroCount n := by
      rw [abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right habs hNpos.le
    exact neg_le_of_abs_le habsdiv
  · intro n
    by_cases hN : criticalFeatureCanonicalZeroCount n = 0
    · simp [hN]
    have hNnonneg : (0 : ℝ) ≤ criticalFeatureCanonicalZeroCount n := by
      unfold criticalFeatureCanonicalZeroCount
      exact_mod_cast xiZeroCount_nonneg (n : ℝ)
    have hNpos : 0 < criticalFeatureCanonicalZeroCount n :=
      lt_of_le_of_ne hNnonneg (Ne.symm hN)
    have herr := criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance_error_lt n
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num
    have habs :
        |criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance n -
          criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n| ≤ 1 :=
      (le_of_lt herr).trans hone
    have habsdiv :
        |(criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance n -
          criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n) /
            criticalFeatureCanonicalZeroCount n| ≤
          1 / criticalFeatureCanonicalZeroCount n := by
      rw [abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right habs hNpos.le
    exact le_of_abs_le habsdiv

/-- Selected positive-shift boundary integral differs from exact source boundary by `o(N)`. -/
theorem tendsto_canonicalPositiveShiftBoundary_sub_sourceBoundary_div :
    Tendsto
      (fun n : ℕ =>
        (criticalFeatureCanonicalPhaseAveragedPositiveShiftBoundary n -
          criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n) /
            criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  have h :=
    tendsto_canonicalPhaseAveragedPositiveShiftCovariance_sub_phaseCovariance_div.neg
  have hzero : Tendsto
      (fun n : ℕ =>
        -((criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance n -
          criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n) /
            criticalFeatureCanonicalZeroCount n))
      atTop (𝓝 0) := by simpa using h
  convert hzero using 1
  funext n
  rw [criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance,
    criticalFeatureCanonicalPhaseAveragedPositiveShiftBoundary,
    criticalFeaturePhaseAveragedPoleGammaCovarianceAtShift,
    criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage_eq_heightCells]
  ring

/-- Canonical asymptotic lower bounds transfer across an `o(N)` perturbation. -/
theorem criticalFeatureCanonicalAsymptoticLower_iff_of_sub_div_tendsto_zero
    {B C : ℕ → ℝ} {c : ℝ}
    (hdiff : Tendsto
      (fun n => (B n - C n) / criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0)) :
    CriticalFeatureCanonicalAsymptoticLower B c ↔
      CriticalFeatureCanonicalAsymptoticLower C c := by
  have htransfer (X Y : ℕ → ℝ)
      (hXY : Tendsto
        (fun n => (X n - Y n) / criticalFeatureCanonicalZeroCount n)
        atTop (𝓝 0))
      (hY : CriticalFeatureCanonicalAsymptoticLower Y c) :
      CriticalFeatureCanonicalAsymptoticLower X c := by
    intro eps heps
    have hY' := hY (eps / 2) (by linarith)
    have herr : ∀ᶠ n : ℕ in atTop,
        -eps / 2 < (X n - Y n) / criticalFeatureCanonicalZeroCount n :=
      (tendsto_order.1 hXY).1 _ (by linarith)
    filter_upwards [hY', herr, eventually_criticalFeatureCanonicalZeroCount_pos]
      with n hYn heren hN
    have hdiffn : (-eps / 2) * criticalFeatureCanonicalZeroCount n <
        X n - Y n :=
      (lt_div_iff₀ hN).mp heren
    nlinarith
  constructor
  · intro hB
    apply htransfer C B
    · have hneg := hdiff.neg
      simpa only [neg_zero] using hneg.congr' (Filter.Eventually.of_forall fun n => by ring)
    · exact hB
  · exact htransfer B C hdiff

/-- Remaining 75% problem as one explicit positive-shift source-integral floor. -/
theorem criticalFeatureCanonicalPositiveShiftBoundary_threePi_lower_iff_threeQuarters :
    CriticalFeatureCanonicalAsymptoticLower
        criticalFeatureCanonicalPhaseAveragedPositiveShiftBoundary (3 * Real.pi) ↔
      CriticalFeatureCanonicalAsymptoticLower
        criticalFeatureCanonicalCriticalLineCount (3 / 4) := by
  rw [criticalFeatureCanonicalAsymptoticLower_iff_of_sub_div_tendsto_zero
    tendsto_canonicalPositiveShiftBoundary_sub_sourceBoundary_div]
  rw [show 3 * Real.pi = 4 * Real.pi - Real.pi by ring]
  rw [← criticalFeaturePhaseCovariance_upper_iff_sourceBoundary_lower Real.pi]
  exact criticalFeaturePhaseCovariance_pi_upper_iff_threeQuarters_criticalLine

/-- Sharp 75% gate stated only through one positive-shift source evaluation at each height. -/
theorem criticalFeatureCanonicalPhaseAveragedPositiveShift_pi_upper_iff_threeQuarters :
    CriticalFeatureCanonicalAsymptoticUpper
        criticalFeatureCanonicalPhaseAveragedPositiveShiftCovariance Real.pi ↔
      CriticalFeatureCanonicalAsymptoticLower
        criticalFeatureCanonicalCriticalLineCount (3 / 4) := by
  rw [criticalFeatureCanonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero
    tendsto_canonicalPhaseAveragedPositiveShiftCovariance_sub_phaseCovariance_div]
  exact criticalFeaturePhaseCovariance_pi_upper_iff_threeQuarters_criticalLine

end

end RHTower
