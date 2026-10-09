import GaloisForLFunctions.RHTower.PaperCircleEnergyLocalization
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Thermal.GridFreq

/-! # Actual localized heat and conditional frequency laws

The spatial penalty makes every heat coefficient strictly positive. Restricting these
coefficients to a coarser subgroup gives a genuine probability law with an explicit
normalizing-mass bound and an exact Gibbs cost representation.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section

def paperCircleSubgridLevel (M k : ℕ) : ℕ := M - k

theorem paperCircleSubgrid_le (M k : ℕ) : paperCircleSubgridLevel M k ≤ M := Nat.sub_le _ _

theorem paperCircleSubgrid_codim (M k : ℕ) :
    M - paperCircleSubgridLevel M k = min k M := by
  unfold paperCircleSubgridLevel
  omega

private theorem subgrid_width (M k : ℕ) :
    (2 : ℝ) ^ (M - paperCircleSubgridLevel M k) ≤ paperCircleLocalizationWidth M k := by
  rw [paperCircleSubgrid_codim]
  exact le_rfl

/-- The spatial kernel itself is an actual probability law. -/
def paperCircleSpatialHeat (M k : ℕ) : Law (Grid M) :=
  ⟨Thermal.q (Thermal.S M (paperCircleLocalizationWidth M k)),
    Thermal.q_nonneg (Thermal.S_nonneg _ _), Thermal.q_total _⟩

variable {ι : Type*} [Fintype ι]

def paperCircleLocalizedHeat (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0) :
    Law (Grid M) :=
  ⟨Thermal.q (paperCircleLocalizedForm a M k t),
    Thermal.q_nonneg (paperCircleLocalizedForm_nonneg a M k t), Thermal.q_total _⟩

/-- Spatial localization removes every zero coefficient of the native heat law. -/
theorem paperCircleLocalizedHeat_pos (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (t : ℝ≥0) (x : Grid M) : 0 < paperCircleLocalizedHeat a M k t x :=
  Thermal.q_pos_one (paperCircleLocalizedForm_nonneg a M k t)
    ((Thermal.S_one_pos (paperCircleLocalizationWidth_ge_one M k)).trans_le
      (paperCircleLocalizedForm_spatial_le a M k t 1)) x

theorem paperCircleLocalizedHeat_zero (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) :
    paperCircleLocalizedHeat a M k 0 = paperCircleSpatialHeat M k := by
  apply Law.ext
  intro x
  change Thermal.q (Thermal.S M (paperCircleLocalizationWidth M k) +
    (0 : ℝ) • paperCircleGridEnergy a M) x = _
  rw [zero_smul, add_zero]
  rfl

/-- The localized heat is exactly spatial heat convolved with the original native heat. -/
theorem paperCircleLocalizedHeat_convolution (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (t : ℝ≥0) (x : Grid M) :
    paperCircleLocalizedHeat a M k t x = ∑ y : Grid M,
      paperCircleSpatialHeat M k y * paperCircleGridHeat a M t (x - y) :=
  Thermal.q_add _ _ _

/-- Further elapsed time still acts by the original native convolution semigroup. -/
theorem paperCircleLocalizedHeat_add_time (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s t : ℝ≥0) (x : Grid M) :
    paperCircleLocalizedHeat a M k (s + t) x = ∑ y : Grid M,
      paperCircleLocalizedHeat a M k s y * paperCircleGridHeat a M t (x - y) := by
  change Thermal.q (Thermal.S M (paperCircleLocalizationWidth M k) +
    ((s + t : ℝ≥0) : ℝ) • paperCircleGridEnergy a M) x = _
  rw [NNReal.coe_add, add_smul, ← add_assoc, Thermal.q_add]
  rfl

def paperCircleSubgridMass (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0) : ℝ :=
  Thermal.summesh (paperCircleSubgrid_le M k) (paperCircleLocalizedForm a M k t)

/-- Exact probability mass retained by the coarse frequency subgroup. -/
theorem paperCircleSubgridMass_eq_sum (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    paperCircleSubgridMass a M k t = ∑ x : Grid (paperCircleSubgridLevel M k),
      paperCircleLocalizedHeat a M k t (raise (paperCircleSubgrid_le M k) x) := rfl

/-- Retained frequency mass is controlled uniformly in the actual energy and coupling. -/
theorem paperCircleSubgridMass_bounds (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (t : ℝ≥0) :
    Period.side (min k M) ≤ paperCircleSubgridMass a M k t ∧
      paperCircleSubgridMass a M k t ≤ 12 * Period.side (min k M) := by
  have H := Thermal.summesh_bounds (paperCircleSubgrid_le M k) (subgrid_width M k)
    (paperCircleLocalizedForm_spatial_le a M k t)
  dsimp only [paperCircleSubgridMass]
  simpa only [paperCircleSubgrid_codim] using H

theorem paperCircleSubgridMass_pos (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (t : ℝ≥0) : 0 < paperCircleSubgridMass a M k t :=
  (Period.side_pos _).trans_le (paperCircleSubgridMass_bounds a M k t).1

/-- The heat law conditioned onto the coarse subgroup, expressed on its own grid. -/
def paperCircleSubgridLaw (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0) :
    Law (Grid (paperCircleSubgridLevel M k)) :=
  Thermal.fq (paperCircleSubgrid_le M k) (paperCircleLocalizedForm a M k t)
    (paperCircleLocalizedForm_nonneg a M k t)

theorem paperCircleSubgridLaw_apply (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (x : Grid (paperCircleSubgridLevel M k)) :
    paperCircleSubgridLaw a M k t x =
      paperCircleLocalizedHeat a M k t (raise (paperCircleSubgrid_le M k) x) /
        paperCircleSubgridMass a M k t := rfl

theorem paperCircleSubgridLaw_pos (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (x : Grid (paperCircleSubgridLevel M k)) : 0 < paperCircleSubgridLaw a M k t x :=
  div_pos (paperCircleLocalizedHeat_pos a M k t _) (paperCircleSubgridMass_pos a M k t)

def paperCircleSubgridCost (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (x : Grid (paperCircleSubgridLevel M k)) : ℝ :=
  Thermal.fq_cost (paperCircleSubgrid_le M k) (paperCircleLocalizedForm a M k t) x

theorem paperCircleSubgridCost_nonneg (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (x : Grid (paperCircleSubgridLevel M k)) : 0 ≤ paperCircleSubgridCost a M k t x :=
  (Thermal.fq_spec (paperCircleSubgrid_le M k) _ (paperCircleLocalizedForm_nonneg a M k t)
    (subgrid_width M k) (paperCircleLocalizedForm_spatial_le a M k t)).2.1 x

theorem paperCircleSubgridCost_zero (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0) :
    paperCircleSubgridCost a M k t 0 = 0 :=
  (Thermal.fq_spec (paperCircleSubgrid_le M k) _ (paperCircleLocalizedForm_nonneg a M k t)
    (subgrid_width M k) (paperCircleLocalizedForm_spatial_le a M k t)).2.2.1

/-- Cost exponentials are exact Fourier expectations of the actual localized Gibbs law. -/
theorem paperCircleSubgridCost_characteristic (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (x : Grid (paperCircleSubgridLevel M k)) :
    (Real.exp (-paperCircleSubgridCost a M k t x) : ℂ) =
      (paperCircleLocalizedLaw a M k t).Cx (chi (raise (paperCircleSubgrid_le M k) x)) := by
  have H := (Thermal.fq_spec (paperCircleSubgrid_le M k) _
    (paperCircleLocalizedForm_nonneg a M k t) (subgrid_width M k)
    (paperCircleLocalizedForm_spatial_le a M k t)).2.2.2.1 x
  change (Real.exp (-Thermal.fq_cost (paperCircleSubgrid_le M k)
    (paperCircleLocalizedForm a M k t) x) : ℂ) =
      (Thermal.label (paperCircleLocalizedForm a M k t)).Cx
        (fun y => chi (raise (paperCircleSubgrid_le M k) x) y)
  simpa only [Thermal.raiseChar_eq] using H

/-- The conditional frequency law has exactly the source Gibbs log-density. -/
theorem paperCircleSubgridLaw_log (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (x : Grid (paperCircleSubgridLevel M k)) :
    -Real.log (paperCircleSubgridLaw a M k t x) =
      -Real.log (paperCircleSubgridLaw a M k t 0) + paperCircleSubgridCost a M k t x :=
  (Thermal.fq_spec (paperCircleSubgrid_le M k) _ (paperCircleLocalizedForm_nonneg a M k t)
    (subgrid_width M k) (paperCircleLocalizedForm_spatial_le a M k t)).2.2.2.2.1 x

theorem paperCircleSubgridLaw_origin_cost (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    -Real.log (paperCircleSubgridLaw a M k t 0) ≤
      Thermal.F (paperCircleLocalizedForm a M k t) - Real.log ((2 : ℝ) ^ min k M) + 12 := by
  have H := (Thermal.fq_spec (paperCircleSubgrid_le M k) _
    (paperCircleLocalizedForm_nonneg a M k t) (subgrid_width M k)
    (paperCircleLocalizedForm_spatial_le a M k t)).2.2.2.2.2
  dsimp only [paperCircleSubgridLaw]
  simpa only [paperCircleSubgrid_codim] using H

end
end RHTower
