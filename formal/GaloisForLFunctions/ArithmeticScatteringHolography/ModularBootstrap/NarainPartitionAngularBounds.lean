import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartitionBounds
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartitionRegularity
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMellin

/-!
# Angular norm control by the actual scalar heat source

The positive partition majorant and exact scalar projection bound the
angular norm integral by a scalar Mellin-integrable function.
-/

open Complex RHTower Set MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Angular integration turns the positive partition majorant into a scalar heat majorant. -/
theorem integral_norm_narainPartition_le (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in Ioc (0 : ℝ) 1, ‖narainPartition ρ σ x y‖) ≤
      y * (1 + ‖narainScalarHeat ⟨0, ρ.y, ρ.y_pos⟩ σ y‖) := by
  have hi : IntegrableOn (fun x : ℝ => narainPartition ρ σ x y) (Ioc 0 1) :=
    (continuous_narainPartition_fixedHeight ρ σ hy).integrableOn_Ioc
  have hp : IntegrableOn (fun x : ℝ => narainPartition ⟨0, ρ.y, ρ.y_pos⟩ σ x y) (Ioc 0 1) :=
    (continuous_narainPartition_fixedHeight ⟨0, ρ.y, ρ.y_pos⟩ σ hy).integrableOn_Ioc
  calc
    _ ≤ ∫ x in Ioc (0 : ℝ) 1, (narainPartition ⟨0, ρ.y, ρ.y_pos⟩ σ x y).re := by
      apply integral_mono_ae hi.norm hp.re
      filter_upwards [] with x
      exact norm_narainPartition_le_pureArea ρ σ ⟨x, y, hy⟩
    _ = (∫ x in Ioc (0 : ℝ) 1, narainPartition ⟨0, ρ.y, ρ.y_pos⟩ σ x y).re := by
      exact integral_re hp
    _ = y * (1 + (narainScalarHeat ⟨0, ρ.y, ρ.y_pos⟩ σ y).re) := by
      rw [integral_narainPartition_eq_scalar _ _ hy, narainScalarPartition_eq_heat _ _ hy]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (Complex.re_le_norm _)) hy.le

#print axioms integral_norm_narainPartition_le
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
