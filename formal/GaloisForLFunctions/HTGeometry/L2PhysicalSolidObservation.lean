import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Full physical-coordinate observations on L²

The almost-everywhere norm envelope defines a bounded family of histories.
Its supremal response is finite, without assuming this family is compact.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory
variable {α Y : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

def l2PhysicalSolidHull (x : Lp ℂ 2 μ) : Set (Lp ℂ 2 μ) :=
  {y | ∀ᵐ t ∂μ, ‖y t‖ ≤ ‖x t‖}

theorem mem_l2PhysicalSolidHull_self (x : Lp ℂ 2 μ) : x ∈ l2PhysicalSolidHull x := by
  change ∀ᵐ t ∂μ, ‖x t‖ ≤ ‖x t‖
  exact Filter.Eventually.of_forall (fun t => show ‖x t‖ ≤ ‖x t‖ from le_rfl)

theorem l2PhysicalSolidHull_norm_le {x y : Lp ℂ 2 μ} (hy : y ∈ l2PhysicalSolidHull x) :
    ‖y‖ ≤ ‖x‖ := Lp.norm_le_norm_of_ae_le hy

def l2PhysicalObservation (T : Lp ℂ 2 μ →L[ℂ] Y) (x : Lp ℂ 2 μ) : ℝ :=
  sSup ((fun y => ‖T y‖) '' l2PhysicalSolidHull x)

theorem l2PhysicalObservation_bddAbove (T : Lp ℂ 2 μ →L[ℂ] Y) (x : Lp ℂ 2 μ) :
    BddAbove ((fun y => ‖T y‖) '' l2PhysicalSolidHull x) := by
  refine ⟨‖T‖ * ‖x‖, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (T.le_opNorm y).trans
    (mul_le_mul_of_nonneg_left (l2PhysicalSolidHull_norm_le hy) (norm_nonneg T))

theorem norm_apply_le_l2PhysicalObservation (T : Lp ℂ 2 μ →L[ℂ] Y)
    {x y : Lp ℂ 2 μ} (hy : y ∈ l2PhysicalSolidHull x) :
    ‖T y‖ ≤ l2PhysicalObservation T x :=
  le_csSup (l2PhysicalObservation_bddAbove T x) ⟨y, hy, rfl⟩

theorem l2PhysicalObservation_nonneg (T : Lp ℂ 2 μ →L[ℂ] Y) (x : Lp ℂ 2 μ) :
    0 ≤ l2PhysicalObservation T x :=
  (norm_nonneg (T x)).trans (norm_apply_le_l2PhysicalObservation T (mem_l2PhysicalSolidHull_self x))

theorem l2PhysicalObservation_le (T : Lp ℂ 2 μ →L[ℂ] Y) (x : Lp ℂ 2 μ) :
    l2PhysicalObservation T x ≤ ‖T‖ * ‖x‖ := by
  apply csSup_le ((show (l2PhysicalSolidHull x).Nonempty from
    ⟨x, mem_l2PhysicalSolidHull_self x⟩).image _)
  rintro _ ⟨y, hy, rfl⟩
  exact (T.le_opNorm y).trans
    (mul_le_mul_of_nonneg_left (l2PhysicalSolidHull_norm_le hy) (norm_nonneg T))

theorem l2PhysicalObservation_eq_zero_iff (T : Lp ℂ 2 μ →L[ℂ] Y) (x : Lp ℂ 2 μ) :
    l2PhysicalObservation T x = 0 ↔ ∀ y ∈ l2PhysicalSolidHull x, T y = 0 := by
  constructor
  · intro h y hy
    exact norm_le_zero_iff.mp (by simpa only [h] using norm_apply_le_l2PhysicalObservation T hy)
  · intro h
    apply le_antisymm _ (l2PhysicalObservation_nonneg T x)
    apply csSup_le ((show (l2PhysicalSolidHull x).Nonempty from
      ⟨x, mem_l2PhysicalSolidHull_self x⟩).image _)
    rintro _ ⟨y, hy, rfl⟩
    simp only [h y hy, norm_zero, le_refl]

end
end GaloisForLFunctions.HTGeometry
