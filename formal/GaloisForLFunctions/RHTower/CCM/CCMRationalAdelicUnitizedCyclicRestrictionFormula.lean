import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicUnitizationDFinsupp

/-!
# Normalized mixed-sector formula for the unitized CCM cyclic source

Unitized cyclic chains have dependent labels: a scalar-unit label or a crossed-product scaling
label.  This file defines their scaling prefix, generalized matrix-trace summand, and normalized
branching law.  The all-scalar branch is evaluated algebraically (never as the divergent trace of
an infinite-dimensional identity); the all-crossed branch reduces definitionally to the already
proved absolutely convergent CCM formula.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Scale := CCMRationalAdelicScaling
private abbrev Label := CCMRationalAdelicUnitizedLabel
private abbrev Fiber := CCMRationalAdelicUnitizedFiber

/-- Scaling carried by a unitized label; the scalar unit carries identity scaling. -/
def ccmRationalAdelicUnitizedLabelScale : Label → Scale
  | .scalar => 1
  | .crossed k => k

/-- Product of unitized label scalings strictly before position `j`. -/
def ccmRationalAdelicUnitizedCyclicPrefix {n : ℕ}
    (label : Fin (n + 1) → Label) (j : Fin (n + 1)) : Scale :=
  ∏ i ∈ Finset.univ.filter (fun i => i < j),
    ccmRationalAdelicUnitizedLabelScale (label i)

/-- Total scaling of a mixed scalar/crossed cyclic label tuple. -/
def ccmRationalAdelicUnitizedCyclicTotalScale {n : ℕ}
    (label : Fin (n + 1) → Label) : Scale :=
  ∏ j, ccmRationalAdelicUnitizedLabelScale (label j)

/-- Orbit evaluation of one dependent unitized coefficient after a fixed rational translation. -/
def ccmRationalAdelicUnitizedFiberCoefficient :
    (label : Label) → Fiber label → CCMRationalAdelicMoritaBase →
      CCMRationalUnit → CCMRationalUnit → ℂ :=
  CCMRationalAdelicUnitizedLabel.rec
    (motive := fun label => Fiber label → CCMRationalAdelicMoritaBase →
      CCMRationalUnit → CCMRationalUnit → ℂ)
    (fun z _ _ _ => z)
    (fun _ t base shift q =>
      ccmRationalAdelicBruhatTensorOrbitCoefficient
        t base.bInf base.bFin (shift * q))

/-- One mixed-sector generalized matrix coefficient. -/
def ccmRationalAdelicUnitizedCyclicFactor {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) (j : Fin (n + 1)) : ℂ :=
  ccmRationalAdelicUnitizedFiberCoefficient
    (label j) (coefficient j) (base j)
    (ccmRationalAdelicUnitizedCyclicPrefix label j).val⁻¹ q

/-- Mixed-sector higher generalized trace summand. -/
def ccmRationalAdelicUnitizedCyclicTerm {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) : ℂ :=
  ∏ j, ccmRationalAdelicUnitizedCyclicFactor label coefficient base q j

/-- Every position is the scalar-unit sector. -/
def ccmRationalAdelicUnitizedAllScalar {n : ℕ}
    (label : Fin (n + 1) → Label) : Prop :=
  ∀ j, label j = .scalar

/-- Normalized unitized higher restriction.  The all-scalar branch is finite algebraic
multiplication; every other identity-scaling branch is the generalized orbit sum. -/
def ccmRationalAdelicUnitizedCyclicRestriction {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase) : ℂ := by
  classical
  exact if ccmRationalAdelicUnitizedAllScalar label then
      ccmRationalAdelicUnitizedCyclicTerm label coefficient base 1
    else if ccmRationalAdelicUnitizedCyclicTotalScale label = 1 then
      ∑' q, ccmRationalAdelicUnitizedCyclicTerm label coefficient base q
    else 0

theorem ccmRationalAdelicUnitizedCyclicRestriction_allScalar {n : ℕ}
    (label : Fin (n + 1) → Label)
    (coefficient : (j : Fin (n + 1)) → Fiber (label j))
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (hscalar : ccmRationalAdelicUnitizedAllScalar label) :
    ccmRationalAdelicUnitizedCyclicRestriction label coefficient base =
      ccmRationalAdelicUnitizedCyclicTerm label coefficient base 1 := by
  simp [ccmRationalAdelicUnitizedCyclicRestriction, hscalar]

@[simp]
theorem ccmRationalAdelicUnitizedLabelScale_crossed (k : Scale) :
    ccmRationalAdelicUnitizedLabelScale (.crossed k) = k :=
  rfl

@[simp]
theorem ccmRationalAdelicUnitizedCyclicPrefix_allCrossed {n : ℕ}
    (k : Fin (n + 1) → Scale) (j : Fin (n + 1)) :
    ccmRationalAdelicUnitizedCyclicPrefix (fun i => .crossed (k i)) j =
      ccmRationalAdelicCyclicPrefix k j := by
  rfl

@[simp]
theorem ccmRationalAdelicUnitizedCyclicTotalScale_allCrossed {n : ℕ}
    (k : Fin (n + 1) → Scale) :
    ccmRationalAdelicUnitizedCyclicTotalScale (fun i => .crossed (k i)) =
      ccmRationalAdelicCyclicTotalScale k := by
  rfl

@[simp]
theorem ccmRationalAdelicUnitizedCyclicTerm_allCrossed {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → CCMRationalAdelicBruhatSimpleTensor)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) :
    ccmRationalAdelicUnitizedCyclicTerm
        (fun j => .crossed (k j)) t base q =
      ccmRationalAdelicCyclicRestrictionTerm k t base q := by
  apply Finset.prod_congr rfl
  intro j hj
  simp [ccmRationalAdelicUnitizedCyclicFactor,
    ccmRationalAdelicUnitizedFiberCoefficient]

theorem ccmRationalAdelicUnitizedCyclicTerm_allCrossed_summable {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → CCMRationalAdelicBruhatSimpleTensor)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase) :
    Summable (ccmRationalAdelicUnitizedCyclicTerm
      (fun j => .crossed (k j)) t base) := by
  refine (ccmRationalAdelicCyclicRestrictionTerm_summable k t base).congr ?_
  intro q
  exact (ccmRationalAdelicUnitizedCyclicTerm_allCrossed k t base q).symm

end RHTower
end GaloisForLFunctions
