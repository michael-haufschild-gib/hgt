import GaloisForLFunctions.HTGeometry.GaussBonnetThermodynamicPrescriptions
import GaloisForLFunctions.HTGeometry.SchwarzschildInformationScaling

/-!
# Exact information-surface packing constraints

Formalizes the algebra behind equations (20)--(28) of arXiv:2608.06941v1
against the existing area entropy `egbEntropyB`. Positive grain mass, length,
packing factor, and total mass are parameterized exponentially. Exact horizon
area matching forces packing to scale linearly with mass; a constant packing
factor can match only one mass. The inverse-cube curvature calibration fixes
the grain mass to one half of the length scale in `G=c=1` units.

The paper uses approximate model relations. These theorems concern their exact
algebraic counterpart and do not establish the proposed physical grain model.
-/

noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def informationGrainCount (g m : ℝ) : ℝ := exp m / exp g

def informationSurfaceArea (g l b m : ℝ) : ℝ := exp b * informationGrainCount g m * exp l ^ (2 : ℕ)

def horizonRequiredPacking (g l m : ℝ) : ℝ := 16 * Real.pi * exp g * exp m / exp l ^ (2 : ℕ)

/-- Matching the grain surface area to the horizon fixes packing exactly. -/
theorem informationSurfaceArea_horizon_iff (g l b m : ℝ) :
    informationSurfaceArea g l b m = 4 * egbEntropyB (2 * exp m) ↔
      exp b = horizonRequiredPacking g l m := by
  unfold informationSurfaceArea informationGrainCount horizonRequiredPacking egbEntropyB
  constructor <;> intro h
  · field_simp at h ⊢
    nlinarith [exp_pos m]
  · field_simp at h ⊢
    nlinarith [exp_pos m]

theorem horizonRequiredPacking_pos (g l m : ℝ) : 0 < horizonRequiredPacking g l m := by
  unfold horizonRequiredPacking
  positivity

/-- The exact survivor of the constant-packing obstruction: packing is linear in mass. -/
theorem horizonRequiredPacking_massRatio (g l m n : ℝ) :
    horizonRequiredPacking g l n / horizonRequiredPacking g l m = exp (n - m) := by
  unfold horizonRequiredPacking
  rw [exp_sub]
  field_simp

theorem constantPacking_single_mass (g l b m n : ℝ) :
    informationSurfaceArea g l b m = 4 * egbEntropyB (2 * exp m) ∧
      informationSurfaceArea g l b n = 4 * egbEntropyB (2 * exp n) ↔
      informationSurfaceArea g l b m = 4 * egbEntropyB (2 * exp m) ∧ n = m := by
  constructor
  · rintro ⟨hm, hn⟩
    refine ⟨hm, ?_⟩
    have he := ((informationSurfaceArea_horizon_iff g l b m).mp hm).symm.trans
      ((informationSurfaceArea_horizon_iff g l b n).mp hn)
    have hh : exp (n - m) = 1 := by
      rw [← horizonRequiredPacking_massRatio g l m n, he]
      exact div_self (horizonRequiredPacking_pos g l n).ne'
    exact sub_eq_zero.mp (exp_injective (hh.trans exp_zero.symm))
  · rintro ⟨h, rfl⟩
    exact ⟨h, h⟩

/-- A universal mass-independent packing value is impossible. -/
theorem constantPacking_not_universal (g l b : ℝ) :
    ¬ ∀ m, informationSurfaceArea g l b m = 4 * egbEntropyB (2 * exp m) := by
  intro h
  have hh := (constantPacking_single_mass g l b 0 1).mp ⟨h 0, h 1⟩
  exact one_ne_zero hh.2

/-- Grain information calibrated by grain length agrees with the metric only at this mass ratio. -/
theorem informationGrain_curvature_calibration (g l m t : ℝ) :
    exp l * informationGrainCount g m / exp t ^ (3 : ℕ) = 2 * exp m / exp t ^ (3 : ℕ) ↔
      exp g = exp l / 2 := by
  unfold informationGrainCount
  rw [div_left_inj' (by positivity : exp t ^ (3 : ℕ) ≠ 0)]
  constructor <;> intro h
  · field_simp at h ⊢
    nlinarith [exp_pos m]
  · field_simp at h ⊢
    nlinarith [exp_pos m]

/-- The exact logarithmic encoding of the paper's one-half grain mass. -/
theorem informationGrain_half_mass (l m t : ℝ) :
    exp l * informationGrainCount (l - log 2) m / exp t ^ (3 : ℕ) = 2 * exp m / exp t ^ (3 : ℕ) := by
  rw [informationGrain_curvature_calibration, exp_sub, exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Curvature calibration turns the packing law into the paper's linear `8π M/l` form. -/
theorem informationGrain_calibrated_packing (l m : ℝ) :
    horizonRequiredPacking (l - log 2) l m = 8 * Real.pi * exp m / exp l := by
  unfold horizonRequiredPacking
  rw [exp_sub, exp_log (by norm_num : (0 : ℝ) < 2)]
  field_simp
  ring

/-- The horizon area is recovered with calibrated mass and the forced packing factor. -/
theorem informationGrain_calibrated_area (l m : ℝ) :
    informationSurfaceArea (l - log 2) l
      (log (horizonRequiredPacking (l - log 2) l m)) m = 4 * egbEntropyB (2 * exp m) := by
  rw [informationSurfaceArea_horizon_iff, exp_log (horizonRequiredPacking_pos _ _ _)]

/-- The calibrated grain expression equals the quantity extracted from the actual metric. -/
theorem informationGrain_actual_metric (l m t polar : ℝ) :
    exp l * informationGrainCount (l - log 2) m / exp t ^ (3 : ℕ) =
      schwarzschildInformationCurvature (exp m) (exp t) polar := by
  rw [informationGrain_half_mass, schwarzschildInformationCurvature_eq]

/-- The actual metric forces precisely the same grain-mass calibration. -/
theorem informationGrain_actual_metric_iff (g l m t polar : ℝ) :
    exp l * informationGrainCount g m / exp t ^ (3 : ℕ) =
      schwarzschildInformationCurvature (exp m) (exp t) polar ↔ exp g = exp l / 2 := by
  rw [schwarzschildInformationCurvature_eq, informationGrain_curvature_calibration]

end GaloisForLFunctions.HTGeometry
