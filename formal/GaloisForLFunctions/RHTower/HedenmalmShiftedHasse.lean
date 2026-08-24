import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.RHTower.HedenmalmShiftedCokernel

/-!
# Hasse quotient for the translated Hedenmalm derivative

The translated range map and concrete cokernel functional form an exact, right-surjective linear
sequence.  Hence Hilbert-space forcing vectors modulo the global translated range are classified by
one complex obstruction coordinate.  The canonical source forcing represents `-i * XiC α`.
-/

open Complex Function MeasureTheory Set Filter Topology Module
open scoped ENNReal

namespace RHTower.HedenmalmClosedWeightedDerivative

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmThetaSource
  HedenmalmFredholmRange

private abbrev H := Lp ℂ 2 unitIntervalMeasure

/-- Translated Hedenmalm range and scalar cokernel obstruction form an exact pair. -/
theorem thetaShifted_hasse_exact (α : ℂ) :
    Function.Exact (thetaShiftedRangeMap α).toLinearMap
      (thetaCokernelFunctional α).toLinearMap :=
  LinearMap.exact_iff.mpr
    (thetaShiftedRangeMap_range_eq_ker_cokernelFunctional α).symm

/-- **Translated Hedenmalm Hasse quotient.**  Forcing vectors modulo the global translated range
are exactly one complex obstruction coordinate. -/
noncomputable def thetaShiftedHasseQuotientEquiv (α : ℂ) :
    (H ⧸ LinearMap.range (thetaShiftedRangeMap α).toLinearMap) ≃ₗ[ℂ] ℂ :=
  linearHasseQuotientEquiv (thetaShiftedRangeMap α).toLinearMap
    (thetaCokernelFunctional α).toLinearMap (thetaShifted_hasse_exact α)
    (thetaCokernelFunctional_surjective α)

@[simp]
theorem thetaShiftedHasseQuotientEquiv_mk (α : ℂ) (y : H) :
    thetaShiftedHasseQuotientEquiv α (Submodule.Quotient.mk y) =
      thetaCokernelFunctional α y :=
  linearHasseQuotientEquiv_mk (thetaShiftedRangeMap α).toLinearMap
    (thetaCokernelFunctional α).toLinearMap (thetaShifted_hasse_exact α)
    (thetaCokernelFunctional_surjective α) y

/-- A forcing vector is globally realized by the translated range exactly when its scalar Hasse
obstruction vanishes. -/
theorem thetaShiftedRangeMap_exists_preimage_iff_obstruction_zero (α : ℂ) (y : H) :
    (∃ k : thetaCentered, thetaShiftedRangeMap α k = y) ↔
      thetaCokernelFunctional α y = 0 := by
  change y ∈ LinearMap.range (thetaShiftedRangeMap α).toLinearMap ↔
    y ∈ LinearMap.ker (thetaCokernelFunctional α).toLinearMap
  rw [thetaShiftedRangeMap_range_eq_ker_cokernelFunctional]

/-- Two forcing vectors differ by globally translated data exactly when their scalar obstruction
coordinates agree. -/
theorem thetaShifted_congr_hasse_iff (α : ℂ) (y z : H) :
    y - z ∈ LinearMap.range (thetaShiftedRangeMap α).toLinearMap ↔
      thetaCokernelFunctional α y = thetaCokernelFunctional α z :=
  linearHasse_congr_iff (thetaShiftedRangeMap α).toLinearMap
    (thetaCokernelFunctional α).toLinearMap (thetaShifted_hasse_exact α) y z

/-- Hasse class of the canonical Hedenmalm source forcing. -/
noncomputable def thetaSourceForcingHasseClass (α : ℂ) :
    H ⧸ LinearMap.range (thetaShiftedRangeMap α).toLinearMap :=
  Submodule.Quotient.mk thetaSourceForcingVector

/-- The canonical forcing class has obstruction coordinate `-i * XiC α`. -/
theorem thetaShiftedHasseQuotientEquiv_sourceForcing (α : ℂ) :
    thetaShiftedHasseQuotientEquiv α (thetaSourceForcingHasseClass α) =
      -Complex.I * XiC α := by
  rw [thetaSourceForcingHasseClass, thetaShiftedHasseQuotientEquiv_mk,
    thetaCokernelFunctional_sourceForcing]

/-- Vanishing of the canonical Hasse obstruction class is exactly vanishing of `XiC`. -/
theorem thetaSourceForcingHasseClass_eq_zero_iff (α : ℂ) :
    thetaSourceForcingHasseClass α = 0 ↔ XiC α = 0 := by
  constructor
  · intro hclass
    have hmap := congrArg (thetaShiftedHasseQuotientEquiv α) hclass
    rw [thetaShiftedHasseQuotientEquiv_sourceForcing, map_zero] at hmap
    exact (mul_eq_zero.mp hmap).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
  · intro hXi
    apply (thetaShiftedHasseQuotientEquiv α).injective
    rw [thetaShiftedHasseQuotientEquiv_sourceForcing, map_zero, hXi, mul_zero]

end

end RHTower.HedenmalmClosedWeightedDerivative
