import GaloisForLFunctions.RHTower.PaperCircleEnergyLocalization
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Quadratic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Localization survives arbitrary changes of native energy

At full grid resolution the spatially localized Gibbs measures converge weakly to the
unit point mass. The native symbols, their finite index types, and their nonnegative
couplings may all change at every resolution without any convergence requirement.
-/

open MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section

private theorem localized_lipschitz_error {ι : Type*} [Fintype ι]
    (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (f : Circle → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) :
    |(∫ z, f z ∂(paperCircleLocalizedMeasure a M k t : Measure Circle)) - f 1| ≤
      20 * (L : ℝ) / paperCircleLocalizationWidth M k := by
  let P := paperCircleLocalizedLaw a M k t
  let R := paperCircleLocalizationWidth M k
  have hR : 0 < R := paperCircleLocalizationWidth_pos M k
  have hpoint (x : Grid M) :
      (f (paperGridCirclePoint x) - f 1) ^ 2 ≤ (L : ℝ) ^ 2 * ‖chi 1 x - 1‖ ^ 2 := by
    have H := hf.dist_le_mul (paperGridCirclePoint x) 1
    rw [Real.dist_eq] at H
    change |f (paperGridCirclePoint x) - f 1| ≤ (L : ℝ) * dist (chi 1 x) (1 : ℂ) at H
    rw [dist_eq_norm] at H
    simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) H 2
  have hvar := paperCircleLocalizedMeasure_distance_sq a M k t
  rw [integral_paperCircleLocalizedMeasure] at hvar
  change P.Ex (fun x => ‖chi 1 x - 1‖ ^ 2) ≤ 200 / R ^ 2 at hvar
  have hsq : (P.Ex (fun x => f (paperGridCirclePoint x) - f 1)) ^ 2 ≤
      (L : ℝ) ^ 2 * (200 / R ^ 2) := calc
    _ ≤ P.Ex (fun x => (f (paperGridCirclePoint x) - f 1) ^ 2) := Law.sq_Ex _ _
    _ ≤ P.Ex (fun x => (L : ℝ) ^ 2 * ‖chi 1 x - 1‖ ^ 2) := P.Ex_mono hpoint
    _ = (L : ℝ) ^ 2 * P.Ex (fun x => ‖chi 1 x - 1‖ ^ 2) := Law.Ex_lmul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
  rw [Law.Ex_sub, Law.Ex_const] at hsq
  rw [integral_paperCircleLocalizedMeasure]
  apply (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ 20 * (L : ℝ) / R by positivity)).mp
  rw [sq_abs]
  apply hsq.trans
  convert mul_le_mul_of_nonneg_right (show (200 : ℝ) ≤ 400 by norm_num)
    (sq_nonneg ((L : ℝ) / R)) using 1 <;> ring

/-- Full-resolution localization converges to a point despite arbitrary changing native energy. -/
theorem paperCircleLocalizedMeasure_tendsto_dirac {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (a : (n : ℕ) → ι n → CCMCircleBoundedSymbol) (t : ℕ → ℝ≥0) :
    Tendsto (fun n => paperCircleLocalizedMeasure (a n) n n (t n)) atTop
      (𝓝 (diracProba (1 : Circle))) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f _ hf
  obtain ⟨L,hL⟩ := hf
  have hupper : Tendsto (fun n : ℕ => 20 * (L : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := 20 * (L : ℝ))).mul
        (tendsto_inv_atTop_zero.comp
          (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)))
  have H : Tendsto (fun n => ∫ z, f z
      ∂(paperCircleLocalizedMeasure (a n) n n (t n) : Measure Circle)) atTop (𝓝 (f 1)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hupper.eventually_lt_const hε] with n hn
    have h := localized_lipschitz_error (a n) n n (t n) f L hL
    simp only [paperCircleLocalizationWidth, min_self] at h
    exact (show dist (∫ z, f z
      ∂(paperCircleLocalizedMeasure (a n) n n (t n) : Measure Circle)) (f 1) ≤
        20 * (L : ℝ) / (2 : ℝ) ^ n by simpa only [Real.dist_eq] using h).trans_lt hn
  simpa only [diracProba, ProbabilityMeasure.coe_mk, integral_dirac] using H

/-- Every native bounded continuous circle observable recovers its value at the unit point. -/
theorem integral_paperCircleLocalizedMeasure_tendsto {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (a : (n : ℕ) → ι n → CCMCircleBoundedSymbol) (t : ℕ → ℝ≥0) (f : Circle →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, f z
      ∂(paperCircleLocalizedMeasure (a n) n n (t n) : Measure Circle)) atTop (𝓝 (f 1)) := by
  have H := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (paperCircleLocalizedMeasure_tendsto_dirac a t) f
  simpa only [diracProba, ProbabilityMeasure.coe_mk, integral_dirac] using H

end
end RHTower
