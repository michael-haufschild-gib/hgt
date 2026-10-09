import GaloisForLFunctions.RHTower.PaperCircleEnergyGibbs
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Thermal.Spatial
import GaloisForLFunctions.HTGeometry.PaperFourierLawMeasure
import GaloisForLFunctions.HTGeometry.CanaryKimCircleConcentration

/-! # Spatial localization of native circle-energy Gibbs laws

A dyadic spatial penalty is admissible at every grid resolution. Adding any nonnegative
native energy preserves its localization bounds. The resulting genuine circle probability
measures satisfy the corpus's extremal-mean and chordal concentration estimates.
-/

open MeasureTheory
open scoped BigOperators NNReal ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section

/-- Requested inverse width, capped at the grid resolution. -/
def paperCircleLocalizationWidth (M k : ℕ) : ℝ := 2 ^ min k M

theorem paperCircleLocalizationWidth_ge_one (M k : ℕ) :
    1 ≤ paperCircleLocalizationWidth M k := one_le_pow₀ (by norm_num)

theorem paperCircleLocalizationWidth_pos (M k : ℕ) :
    0 < paperCircleLocalizationWidth M k :=
  lt_of_lt_of_le (by norm_num) (paperCircleLocalizationWidth_ge_one M k)

theorem paperCircleLocalizationWidth_le_grid (M k : ℕ) :
    paperCircleLocalizationWidth M k ≤ 2 ^ M :=
  pow_le_pow_right₀ (by norm_num) (Nat.min_le_right _ _)

variable {ι : Type*} [Fintype ι]

/-- Spatial localization plus the actual native energy, at arbitrary nonnegative coupling. -/
def paperCircleLocalizedForm (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0) :
    Thermal.Form M :=
  Thermal.S M (paperCircleLocalizationWidth M k) + (t : ℝ) • paperCircleGridEnergy a M

theorem paperCircleLocalizedForm_spatial_le (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    Thermal.S M (paperCircleLocalizationWidth M k) ≤ paperCircleLocalizedForm a M k t :=
  le_add_of_nonneg_right (fun x => mul_nonneg t.coe_nonneg (paperCircleGridEnergy_nonneg a M x))

theorem paperCircleLocalizedForm_nonneg (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) : 0 ≤ paperCircleLocalizedForm a M k t :=
  (Thermal.S_nonneg M _).trans (paperCircleLocalizedForm_spatial_le a M k t)

def paperCircleLocalizedLaw (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0) :
    Law (Grid M) := Thermal.label (paperCircleLocalizedForm a M k t)

/-- The mean spatial energy remains uniformly bounded under arbitrary native coupling. -/
theorem paperCircleLocalizedLaw_spatial_energy (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    (paperCircleLocalizedLaw a M k t).Ex
      (Thermal.form (Thermal.S M (paperCircleLocalizationWidth M k))) ≤ 100 :=
  Thermal.S_energy _ (paperCircleLocalizationWidth_ge_one M k)
    (paperCircleLocalizationWidth_le_grid M k) _ (paperCircleLocalizedForm_spatial_le a M k t)

/-- Mean squared circular displacement is controlled at the requested spatial scale. -/
theorem paperCircleLocalizedLaw_variance (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    (paperCircleLocalizedLaw a M k t).Ex (fun x => (Dyadic.diam x) ^ 2) ≤
      100 / paperCircleLocalizationWidth M k ^ 2 :=
  Thermal.S_variance _ (paperCircleLocalizationWidth_ge_one M k)
    (paperCircleLocalizationWidth_le_grid M k) _ (paperCircleLocalizedForm_spatial_le a M k t)

theorem paperCircleLocalizedLaw_cosine_cost (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    (paperCircleLocalizedLaw a M k t).Ex (Thermal.cost 1) ≤
      100 / paperCircleLocalizationWidth M k ^ 2 :=
  Thermal.S_cost _ (paperCircleLocalizationWidth_ge_one M k)
    (paperCircleLocalizationWidth_le_grid M k) _ (paperCircleLocalizedForm_spatial_le a M k t)

/-- Every finite Fourier character has a quantitative root-mean-square phase bound. -/
theorem paperCircleLocalizedLaw_phase_rms (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (u : Grid M) :
    Real.sqrt ((paperCircleLocalizedLaw a M k t).Ex (fun x => ‖1 - chi u x‖ ^ 2)) ≤
      rad u * (20 / paperCircleLocalizationWidth M k) :=
  Thermal.delta_S _ (paperCircleLocalizationWidth_ge_one M k)
    (paperCircleLocalizationWidth_le_grid M k) _ (paperCircleLocalizedForm_spatial_le a M k t) u

/-- Place each grid point on the native multiplicative unit circle. -/
def paperGridCirclePoint {M : ℕ} (x : Grid M) : Circle :=
  ⟨chi 1 x, mem_sphere_zero_iff_norm.mpr (norm_chi 1 x)⟩

def paperCircleLocalizedMeasure (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0) :
    ProbabilityMeasure Circle :=
  (paperCircleLocalizedLaw a M k t).atomicProbability paperGridCirclePoint

/-- Exact conversion from finite expectation to the corpus's circle integral. -/
theorem integral_paperCircleLocalizedMeasure (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (f : Circle → ℝ) :
    (∫ z, f z ∂(paperCircleLocalizedMeasure a M k t : Measure Circle)) =
      (paperCircleLocalizedLaw a M k t).Ex (fun x => f (paperGridCirclePoint x)) :=
  Law.integral_atomicProbability _ _ _

theorem circleExtremalMean_paperCircleLocalizedMeasure (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    circleExtremalMean (paperCircleLocalizedMeasure a M k t) 1 =
      (paperCircleLocalizedLaw a M k t).Ex (Thermal.wave 1) := by
  rw [circleExtremalMean, integral_paperCircleLocalizedMeasure]
  simp only [circleExtremalRate, paperGridCirclePoint, Circle.coe_one,
    map_one, mul_one]
  rfl

/-- Native extremal-mean deficit decays quadratically in the inverse width. -/
theorem paperCircleLocalizedMeasure_mean_deficit (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    1 - circleExtremalMean (paperCircleLocalizedMeasure a M k t) 1 ≤
      100 / paperCircleLocalizationWidth M k ^ 2 := by
  rw [circleExtremalMean_paperCircleLocalizedMeasure]
  have H := paperCircleLocalizedLaw_cosine_cost a M k t
  change (Thermal.label (paperCircleLocalizedForm a M k t)).Ex (Thermal.cost 1) ≤ _ at H
  rw [Thermal.cred_cost, Thermal.cred_ex] at H
  exact H

/-- The actual circle transport cost is bounded uniformly in the energy coupling. -/
theorem paperCircleLocalizedMeasure_distance_sq (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    (∫ z : Circle, ‖(z : ℂ) - 1‖ ^ 2
      ∂(paperCircleLocalizedMeasure a M k t : Measure Circle)) ≤
        200 / paperCircleLocalizationWidth M k ^ 2 := by
  have H := circleExtremalMean_distance (paperCircleLocalizedMeasure a M k t) 1
  simp only [Circle.coe_one] at H
  rw [H]
  calc
    _ ≤ 2 * (100 / paperCircleLocalizationWidth M k ^ 2) :=
      mul_le_mul_of_nonneg_left (paperCircleLocalizedMeasure_mean_deficit a M k t) (by norm_num)
    _ = _ := by ring

/-- Every positive chordal radius has an explicit tail bound, with no extra premises. -/
theorem paperCircleLocalizedMeasure_concentration (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (r : ℝ) :
    Real.exp r ^ 2 * (paperCircleLocalizedMeasure a M k t : Measure Circle).real
      {z : Circle | Real.exp r ≤ ‖(z : ℂ) - 1‖} ≤
        200 / paperCircleLocalizationWidth M k ^ 2 := by
  have H := circleExtremalMean_concentration (paperCircleLocalizedMeasure a M k t) 1 r
  simp only [Circle.coe_one] at H
  apply H.trans
  calc
    _ ≤ 2 * (100 / paperCircleLocalizationWidth M k ^ 2) :=
      mul_le_mul_of_nonneg_left (paperCircleLocalizedMeasure_mean_deficit a M k t) (by norm_num)
    _ = _ := by ring

/-- Strengthening the actual energy can only improve native mean alignment. -/
theorem monotone_paperCircleLocalizedMeasure_mean (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) :
    Monotone (fun t : ℝ≥0 => circleExtremalMean (paperCircleLocalizedMeasure a M k t) 1) := by
  intro s t h
  simp only [circleExtremalMean_paperCircleLocalizedMeasure, paperCircleLocalizedLaw,
    ← Thermal.cred_ex]
  apply Thermal.cred_mono (paperCircleLocalizedForm_nonneg a M k s)
  intro x
  change Thermal.S M (paperCircleLocalizationWidth M k) x + (s : ℝ) * paperCircleGridEnergy a M x ≤
    Thermal.S M (paperCircleLocalizationWidth M k) x + (t : ℝ) * paperCircleGridEnergy a M x
  linarith [mul_le_mul_of_nonneg_right (show (s : ℝ) ≤ t from h)
    (paperCircleGridEnergy_nonneg a M x)]

end
end RHTower
