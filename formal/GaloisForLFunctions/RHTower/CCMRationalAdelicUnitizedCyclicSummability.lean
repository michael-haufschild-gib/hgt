import GaloisForLFunctions.RHTower.CCMRationalAdelicUnitizedCyclicRestrictionFormula

/-!
# Absolute convergence in every mixed unitized CCM sector

The scalar unit cannot be represented by an infinite-dimensional trace-class identity.  The
normalized restriction therefore evaluates the all-scalar sector algebraically.  This file proves
that every remaining mixed sector is nevertheless absolutely summable: one crossed-product
position supplies an `ℓ¹` orbit coefficient, while every other position is controlled by its
uniform `ℓ¹` bound (or by the norm of its scalar coefficient).
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Label := CCMRationalAdelicUnitizedLabel
private abbrev Fiber := CCMRationalAdelicUnitizedFiber
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling

/-- Uniform pointwise bound for one dependent unitized coefficient. -/
def ccmRationalAdelicUnitizedFiberBound :
    (label : Label) → Fiber label → CCMRationalAdelicMoritaBase → ℝ :=
  CCMRationalAdelicUnitizedLabel.rec
    (motive := fun label => Fiber label → CCMRationalAdelicMoritaBase → ℝ)
    (fun z _ => ‖z‖)
    (fun _ t base =>
      ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound
        t base.bInf base.bFin)

theorem ccmRationalAdelicUnitizedFiberBound_nonneg
    (label : Label) (coefficient : Fiber label)
    (base : CCMRationalAdelicMoritaBase) :
    0 ≤ ccmRationalAdelicUnitizedFiberBound label coefficient base := by
  exact CCMRationalAdelicUnitizedLabel.rec
    (motive := fun label => ∀ coefficient : Fiber label,
      0 ≤ ccmRationalAdelicUnitizedFiberBound label coefficient base)
    (fun z => norm_nonneg z)
    (fun _ t =>
      ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound_nonneg
        t base.bInf base.bFin)
    label coefficient

theorem ccmRationalAdelicUnitizedFiberCoefficient_norm_le_bound
    (label : Label) (coefficient : Fiber label)
    (base : CCMRationalAdelicMoritaBase)
    (shift q : CCMRationalUnit) :
    ‖ccmRationalAdelicUnitizedFiberCoefficient
        label coefficient base shift q‖ ≤
      ccmRationalAdelicUnitizedFiberBound label coefficient base := by
  exact CCMRationalAdelicUnitizedLabel.rec
    (motive := fun label => ∀ coefficient : Fiber label,
      ‖ccmRationalAdelicUnitizedFiberCoefficient
          label coefficient base shift q‖ ≤
        ccmRationalAdelicUnitizedFiberBound label coefficient base)
    (fun _ => le_rfl)
    (fun _ t =>
      ccmRationalAdelicBruhatTensorOrbitCoefficient_norm_le_lOneBound
        t base.bInf_ne_zero base.bFin (shift * q))
    label coefficient

theorem ccmRationalAdelicUnitizedFiberCoefficient_crossed_summable_norm
    (k : Scale) (t : Core) (base : CCMRationalAdelicMoritaBase)
    (shift : CCMRationalUnit) :
    Summable (fun q : CCMRationalUnit =>
      ‖ccmRationalAdelicUnitizedFiberCoefficient
        (.crossed k) t base shift q‖) := by
  have h := ccmRationalAdelicBruhatTensorOrbitCoefficient_summable
    t base.bInf_ne_zero base.bFin
  apply h.comp_injective
  intro q r hqr
  exact mul_left_cancel hqr

theorem ccmRationalAdelicUnitizedFiberCoefficient_summable_norm_of_ne_scalar
    (label : Label) (coefficient : Fiber label)
    (base : CCMRationalAdelicMoritaBase) (shift : CCMRationalUnit)
    (hlabel : label ≠ .scalar) :
    Summable (fun q : CCMRationalUnit =>
      ‖ccmRationalAdelicUnitizedFiberCoefficient
        label coefficient base shift q‖) := by
  exact CCMRationalAdelicUnitizedLabel.rec
    (motive := fun label => ∀ coefficient : Fiber label,
      label ≠ .scalar → Summable (fun q : CCMRationalUnit =>
        ‖ccmRationalAdelicUnitizedFiberCoefficient
          label coefficient base shift q‖))
    (fun _ h => (h rfl).elim)
    (fun k t _ =>
      ccmRationalAdelicUnitizedFiberCoefficient_crossed_summable_norm
        k t base shift)
    label coefficient hlabel

theorem ccmRationalAdelicUnitizedCyclicFactor_eq_fiberCoefficient {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) (j : Fin (n + 1)) :
    ccmRationalAdelicUnitizedCyclicFactor label coefficient base q j =
      ccmRationalAdelicUnitizedFiberCoefficient
        (label j) (coefficient j) (base j)
        (ccmRationalAdelicUnitizedCyclicPrefix label j).val⁻¹ q := by
  rfl

/-- Product of uniform bounds away from a selected crossed-product position. -/
def ccmRationalAdelicUnitizedCyclicTailBound {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (selected : Fin (n + 1)) : ℝ :=
  ∏ j ∈ Finset.univ.erase selected,
    ccmRationalAdelicUnitizedFiberBound (label j) (coefficient j) (base j)

theorem ccmRationalAdelicUnitizedCyclicTailBound_nonneg {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (selected : Fin (n + 1)) :
    0 ≤ ccmRationalAdelicUnitizedCyclicTailBound
      label coefficient base selected := by
  apply Finset.prod_nonneg
  intro j hj
  exact ccmRationalAdelicUnitizedFiberBound_nonneg
    (label j) (coefficient j) (base j)

/-- Pointwise domination with an arbitrary selected position as the summable head. -/
theorem ccmRationalAdelicUnitizedCyclicTerm_norm_le {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (selected : Fin (n + 1)) (q : CCMRationalUnit) :
    ‖ccmRationalAdelicUnitizedCyclicTerm label coefficient base q‖ ≤
      ‖ccmRationalAdelicUnitizedCyclicFactor
          label coefficient base q selected‖ *
        ccmRationalAdelicUnitizedCyclicTailBound
          label coefficient base selected := by
  rw [ccmRationalAdelicUnitizedCyclicTerm, norm_prod,
    ← Finset.mul_prod_erase Finset.univ
      (fun j => ‖ccmRationalAdelicUnitizedCyclicFactor
        label coefficient base q j‖) (Finset.mem_univ selected)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod
  · intro j hj
    exact norm_nonneg _
  · intro j hj
    rw [ccmRationalAdelicUnitizedCyclicFactor_eq_fiberCoefficient]
    exact ccmRationalAdelicUnitizedFiberCoefficient_norm_le_bound
      (label j) (coefficient j) (base j) _ q

theorem ccmRationalAdelicUnitizedCyclicFactor_crossed_summable_norm {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (selected : Fin (n + 1))
    (hlabel : label selected ≠ .scalar) :
    Summable (fun q : CCMRationalUnit =>
      ‖ccmRationalAdelicUnitizedCyclicFactor
        label coefficient base q selected‖) := by
  refine (ccmRationalAdelicUnitizedFiberCoefficient_summable_norm_of_ne_scalar
    (label selected) (coefficient selected) (base selected)
      (ccmRationalAdelicUnitizedCyclicPrefix label selected).val⁻¹ hlabel).congr ?_
  intro q
  rw [ccmRationalAdelicUnitizedCyclicFactor_eq_fiberCoefficient]

/-- Every non-all-scalar unitized cyclic sector has an absolutely convergent generalized trace. -/
theorem ccmRationalAdelicUnitizedCyclicTerm_summable_norm_of_not_allScalar {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (hscalar : ¬ ccmRationalAdelicUnitizedAllScalar label) :
    Summable (fun q : CCMRationalUnit =>
      ‖ccmRationalAdelicUnitizedCyclicTerm label coefficient base q‖) := by
  classical
  have hposition : ∃ j, label j ≠ .scalar :=
    not_forall.mp hscalar
  obtain ⟨selected, hselected⟩ := hposition
  have hhead := ccmRationalAdelicUnitizedCyclicFactor_crossed_summable_norm
    label coefficient base selected hselected
  apply Summable.of_nonneg_of_le
    (fun q => norm_nonneg _)
    (fun q => ccmRationalAdelicUnitizedCyclicTerm_norm_le
      label coefficient base selected q)
  exact hhead.mul_right
    (ccmRationalAdelicUnitizedCyclicTailBound
      label coefficient base selected)

theorem ccmRationalAdelicUnitizedCyclicTerm_summable_of_not_allScalar {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (hscalar : ¬ ccmRationalAdelicUnitizedAllScalar label) :
    Summable (ccmRationalAdelicUnitizedCyclicTerm label coefficient base) :=
  summable_norm_iff.mp
    (ccmRationalAdelicUnitizedCyclicTerm_summable_norm_of_not_allScalar
      label coefficient base hscalar)

end RHTower
end GaloisForLFunctions
