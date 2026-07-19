import GaloisForLFunctions.RHTower.XiTransverseShiftPrimeDefectValueReflection

/-!
# Pairwise values for every integral completed-Xi shift

This small value core identifies oriented differences of transverse source carriers with the
corresponding differences of actual corrected completed-Xi shift defects as upper-end germs. It
contains no matroid or base-field transport, allowing rational and all-valuation consumers to
compile independently.
-/

namespace RHTower

open Complex Filter

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiPairwiseValueUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiPairwiseValueUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiPairwiseValueUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiPairwiseValueUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- Pairwise difference between two arbitrary integral transverse source carriers. -/
def xiTransverseShiftPairDifferenceUpperEndCarrier
    {V E : Type*} (shift : V → ℕ) (tail head : E → V) (e : E) :
    upperEndMeroField :=
  xiTransverseShiftUpperEndCarrier (shift (head e)) -
    xiTransverseShiftUpperEndCarrier (shift (tail e))

/-- **Pairwise carrier relative-shift law.** An ordered corrected-Xi edge carrier is the
upper-end translate of the single carrier at its relative shift. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_eq_relativeShift_of_le
    {V E : Type*} (shift : V → ℕ) (tail head : E → V) (e : E)
    (hshift : shift (tail e) ≤ shift (head e)) :
    xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e =
      upperEndTranslationMeroEquiv
        (Complex.I * (shift (tail e) : ℂ))
        (xiTransverseShiftUpperEndCarrier
          (shift (head e) - shift (tail e))) := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier,
    xiTransverseShiftUpperEndCarrier_sub_eq_translation_of_le _ _ hshift]

/-- Unconditional pairwise carrier classifier with the endpoint-order Prop discharged. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_eq_relativeShift
    {V E : Type*} (shift : V → ℕ) (tail head : E → V) (e : E) :
    xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e =
      if shift (tail e) ≤ shift (head e) then
        upperEndTranslationMeroEquiv
          (Complex.I * (shift (tail e) : ℂ))
          (xiTransverseShiftUpperEndCarrier
            (shift (head e) - shift (tail e)))
      else
        -upperEndTranslationMeroEquiv
          (Complex.I * (shift (head e) : ℂ))
          (xiTransverseShiftUpperEndCarrier
            (shift (tail e) - shift (head e))) := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier,
    xiTransverseShiftUpperEndCarrier_sub_eq_relativeShift]

/-- Analytic representative of an arbitrary integral pairwise transverse shift difference. -/
def xiTransverseShiftPairDifferenceUpperEndAnalytic
    {V E : Type*} (shift : V → ℕ) (tail head : E → V) (e : E) :
    upperEndAnalyticSubring :=
  finiteAbscissaLSeriesToUpperEndAnalytic
      (xiTransverseShiftFiniteAbscissaSource (shift (head e))) -
    finiteAbscissaLSeriesToUpperEndAnalytic
      (xiTransverseShiftFiniteAbscissaSource (shift (tail e)))

/-- Actual corrected completed-Xi germ carried by an arbitrary integral oriented shift pair. -/
def xiTransverseShiftPairDifferenceUpperEndGerm
    {V E : Type*} (shift : V → ℕ) (tail head : E → V) (e : E) :
    Germ upperEndFilter ℂ :=
  xiTransverseShiftPrimeDefectUpperEndGerm (shift (head e)) -
    xiTransverseShiftPrimeDefectUpperEndGerm (shift (tail e))

theorem xiTransverseShiftPairDifferenceUpperEndCarrier_eq_algebraMap
    {V E : Type*} (shift : V → ℕ) (tail head : E → V) (e : E) :
    xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (xiTransverseShiftPairDifferenceUpperEndAnalytic shift tail head e) := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier,
    xiTransverseShiftPairDifferenceUpperEndAnalytic,
    xiTransverseShiftUpperEndCarrier, xiTransverseShiftUpperEndCarrier,
    finiteAbscissaLSeriesToUpperEndMero_eq_algebraMap,
    finiteAbscissaLSeriesToUpperEndMero_eq_algebraMap, map_sub]

/-- **Arbitrary integral pairwise completed-Xi value reflection.** Every pairwise transverse
carrier is the difference of the two actual corrected completed-Xi shift defects as an upper-end
germ. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_germ_eq
    {V E : Type*} (shift : V → ℕ) (tail head : E → V) (e : E) :
    ((xiTransverseShiftPairDifferenceUpperEndAnalytic shift tail head e :
        upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
      xiTransverseShiftPairDifferenceUpperEndGerm shift tail head e := by
  rw [xiTransverseShiftPairDifferenceUpperEndAnalytic]
  change finiteAbscissaLSeriesToUpperEndGerm
      (xiTransverseShiftFiniteAbscissaSource (shift (head e))) -
    finiteAbscissaLSeriesToUpperEndGerm
      (xiTransverseShiftFiniteAbscissaSource (shift (tail e))) = _
  rw [xiTransverseShiftUpperEndGerm_eq_xiTransverseShiftPrimeDefect,
    xiTransverseShiftUpperEndGerm_eq_xiTransverseShiftPrimeDefect]
  rfl

end

end RHTower
