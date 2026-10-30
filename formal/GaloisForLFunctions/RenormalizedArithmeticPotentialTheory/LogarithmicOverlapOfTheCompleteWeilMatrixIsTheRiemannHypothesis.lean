import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixHasAnExactErrorDecomposition
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilEnergyControlsThePrimeDefect
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSecondOrderSynthesis
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineKeepsAGammaReserveAtEveryOverlap
import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds

/-!
# Logarithmic overlap of the complete Weil matrix is the Riemann hypothesis

The complete Weil matrix of a profile `φ` at overlap ratio `c` is Weil's form on the atoms
`φ((u − log n)/w)`, `w = c/N`. Recentred and normalized, `φ_S(s) = φ((s + 1)/2)/(2∫φ)` is a unit-mass
profile on `[−1, 1]` whose dilate by `κ = 2/w` is the same atom up to a common shift and the factor
`1/(w∫φ)` (`dilate_profile_eq_atomDilate`). Weil's form is translation invariant, so the second-order
overlap law transfers verbatim (`riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`):
whenever `c_N^4/log N → ∞` and `c_N = o(N)`, the complete Weil matrices are eventually positive
semidefinite iff RH. For `c_N = 2(log N)^α`, `α > 1/4`, this holds for the tilted unit spline
(`riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

variable {φ : ℝ → ℝ}

/-- The unit-mass recentring of a profile on `[0, 1]` to `[−1, 1]`. -/
def recentredProfile (φ : ℝ → ℝ) (s : ℝ) : ℝ := φ ((s + 1) / 2) / (2 * ∫ u, φ u)

theorem contDiff_recentredProfile (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 2 (recentredProfile φ) := by
  unfold recentredProfile
  exact (hφ.comp ((contDiff_id.add contDiff_const).div_const _)).div_const _

theorem vanishesOff_recentredProfile (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    VanishesOff (recentredProfile φ) := by
  intro s hs
  unfold recentredProfile
  rw [hsupp _ fun h => ?_, zero_div]
  obtain ⟨h0, h1⟩ := h
  rcases lt_abs.mp hs with hs | hs <;> linarith

theorem integral_recentredProfile (hint : (∫ u, φ u) ≠ 0) : ∫ s, recentredProfile φ s = 1 := by
  unfold recentredProfile
  rw [integral_div]
  have h : ∫ s, φ ((s + 1) / 2) = 2 * ∫ u, φ u := by
    have h1 : (fun s => φ ((s + 1) / 2)) = fun s => (fun t => φ (t + 1 / 2)) (s / 2) := by
      funext s; congr 1; ring
    rw [h1, Measure.integral_comp_div (fun t => φ (t + 1 / 2)) (2 : ℝ),
      integral_add_right_eq_self (fun t => φ t) (1 / 2 : ℝ)]
    simp
  rw [h, div_self (mul_ne_zero two_ne_zero hint)]

/-- The dilated recentred profile is the atom of width `w` shifted by `w/2`, scaled by
`1/(w∫φ)`. -/
theorem dilate_profile_eq_atomDilate {w : ℝ} (hw : 0 < w) (s : ℝ) :
    dilate (2 / w) (recentredProfile φ) s =
      atomDilate φ w (s + w / 2) / (w * ∫ u, φ u) := by
  unfold dilate recentredProfile atomDilate
  have harg : (2 / w * s + 1) / 2 = (s + w / 2) / w := by field_simp
  rw [harg]
  field_simp

/-- The atomic test of the dilated recentred profile is a shifted atomic test of the atoms. -/
theorem weilQuad_atomicTest_dilate_recentred {w : ℝ} (hw : 0 < w) (N : ℕ) (x : ℕ → ℝ) :
    weilQuad (atomicTest N x (dilate (2 / w) (recentredProfile φ))) =
      weilQuad (atomicTest N (fun n => x n / (w * ∫ u, φ u)) (atomDilate φ w)) := by
  have h : atomicTest N x (dilate (2 / w) (recentredProfile φ)) =
      fun u => atomicTest N (fun n => x n / (w * ∫ u, φ u)) (atomDilate φ w) (u - -(w / 2)) := by
    funext u
    unfold atomicTest
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [dilate_profile_eq_atomDilate hw, show u - -(w / 2) - Real.log n = u - Real.log n + w / 2 by
      ring]
    ring
  rw [h, weilQuad_comp_sub]

/-- A coefficient sequence on the horizon is the extension of its restriction. -/
theorem atomicTest_restrict (N : ℕ) (y : ℕ → ℝ) (g : ℝ → ℝ) :
    atomicTest N y g =
      atomicTest N (primeHorizonExtension (WithLp.toLp 2 (fun n : PrimeHorizonIndex N => y n)))
        g := by
  funext u
  unfold atomicTest
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [primeHorizonExtension, dif_pos hn]

/-- At a fixed horizon, nonnegativity of the complete Weil energy is nonnegativity of Weil's form
on every atomic test of the recentred dilate. -/
theorem forall_completeWeilEnergy_nonneg_iff (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hint : (∫ u, φ u) ≠ 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    (∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), 0 ≤ completeWeilEnergy φ c N x) ↔
      ∀ y : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N y (dilate (2 / (c / N)) (recentredProfile φ))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]; exact mul_pos hw hM
  have hk : (c / N * ∫ u, φ u) ≠ 0 := mul_ne_zero hw.ne' hint
  constructor
  · intro H y
    rw [weilQuad_atomicTest_dilate_recentred hw, atomicTest_restrict]
    have h := H (WithLp.toLp 2 (fun n : PrimeHorizonIndex N => y n / (c / N * ∫ u, φ u)))
    rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN] at h
    exact (div_nonneg_iff.mp h).elim (fun h' => h'.1) fun h' => absurd h'.2 (not_le.mpr hG)
  · intro H x
    rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN]
    refine div_nonneg ?_ hG.le
    have h := H (fun n => primeHorizonExtension x n * (c / N * ∫ u, φ u))
    rw [weilQuad_atomicTest_dilate_recentred hw] at h
    simpa only [mul_div_cancel_right₀ _ hk] using h

/-- **Logarithmic overlap is the Riemann hypothesis.** If the overlap ratios grow with
`c_N^4/log N → ∞` and `c_N = o(N)` (`OverlapGrowthTwo` for `κ_N = 2N/c_N`), the complete Weil
matrices are eventually positive semidefinite iff RH. -/
theorem riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hint : (∫ u, φ u) ≠ 0)
    {c : ℕ → ℝ} (hc : ∀ᶠ N in atTop, 0 < c N) (hκ : OverlapGrowthTwo fun N => 2 / (c N / N)) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop,
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), 0 ≤ completeWeilEnergy φ (c N) N x := by
  rw [riemannHypothesis_iff_atomicFamilies_nonneg_of_growthTwo hκ (contDiff_recentredProfile hφ)
    (vanishesOff_recentredProfile hsupp) (integral_recentredProfile hint)]
  constructor
  · intro H
    filter_upwards [H, eventually_ge_atTop 1, hc] with N hN h1 hcN
    exact (forall_completeWeilEnergy_nonneg_iff hφ hsupp hM hint hcN h1).mpr hN
  · intro H
    filter_upwards [H, eventually_ge_atTop 1, hc] with N hN h1 hcN
    exact (forall_completeWeilEnergy_nonneg_iff hφ hsupp hM hint hcN h1).mp hN

theorem integral_tiltedUnitSpline_ne_zero : (∫ u, tiltedUnitSpline u) ≠ 0 := by
  intro h0
  have hnn : 0 ≤ tiltedUnitSpline := fun u => by
    unfold tiltedUnitSpline atomDilate
    exact BiScaleUncertainty.ChebyshevGauge.splineProbe_nonneg _
  have hcont := contDiff_tiltedUnitSpline.continuous
  have hi : Integrable tiltedUnitSpline :=
    hcont.integrable_of_hasCompactSupport hasCompactSupport_tiltedUnitSpline
  have hae := (integral_eq_zero_iff_of_nonneg hnn hi).mp h0
  have hsq : (∫ u, tiltedUnitSpline u ^ 2) = 0 := by
    rw [integral_congr_ae (hae.mono fun u hu => by simp [hu] : (fun u => tiltedUnitSpline u ^ 2)
      =ᵐ[volume] fun _ => (0 : ℝ))]
    simp
  exact integral_tiltedUnitSpline_sq_pos.ne' hsq

/-- For the tilted unit spline at overlap `2(log N)^α`, `α > 1/4`, eventual positivity of the
complete Weil matrices is the Riemann hypothesis. -/
theorem riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log {α : ℝ}
    (hα : 1 / 4 < α) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      0 ≤ completeWeilEnergy tiltedUnitSpline (2 * Real.log N ^ α) N x := by
  have hκ : (fun N : ℕ => 2 / (2 * Real.log N ^ α / N)) = fun N : ℕ => (N : ℝ) / Real.log N ^ α := by
    funext N
    rw [div_div_eq_mul_div, mul_div_mul_left _ _ two_ne_zero]
  have hc : ∀ᶠ N : ℕ in atTop, 0 < 2 * Real.log N ^ α := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    positivity
  refine riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos integral_tiltedUnitSpline_ne_zero hc ?_
  rw [hκ]
  exact overlapGrowthTwo_log hα

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
