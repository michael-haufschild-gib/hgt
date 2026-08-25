import GaloisForLFunctions.RHTower.XiAtomicIncrementCorrection
import GaloisForLFunctions.HTGeometry.SmallGrowthDifferentialField

namespace RHTower

open Complex Filter Function Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiSmallGrowthCarrierUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiSmallGrowthCarrierUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiSmallGrowthCarrierUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiSmallGrowthCarrierUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiSmallGrowthCarrierSmallGrowthDifferential : Differential SmallGrowthMeromorphicField :=
  smallGrowthDifferential

local instance xiSmallGrowthCarrierSmallGrowthDifferentialAlgebra :
    DifferentialAlgebra SmallGrowthMeromorphicField upperEndMeroField :=
  smallGrowthDifferentialAlgebra

theorem xiRotated_fullComplexShiftOrbit_differentialIndependent_over_smallGrowth :
    DifferentialIndependent SmallGrowthMeromorphicField
      (fun h : ℂ => upperEndTranslationMeroEquiv (I * h)
        xiRotatedUpperEndCarrier) := by
  let a : SmallGrowthMeromorphicField :=
    -algebraMap ℂ SmallGrowthMeromorphicField I
  have ha : a ≠ 0 := by
    apply neg_ne_zero.mpr
    change complexToSmallGrowthMeromorphic I ≠ 0
    simpa only [map_zero] using
      complexToSmallGrowthMeromorphic_injective.ne Complex.I_ne_zero
  have hscaled :=
    xiLogDerivRotated_fullComplexShiftOrbit_differentialIndependent_over_smallGrowth.mulBase
      (fun _ : ℂ => a) (fun _ => ha)
  let u : ℂ → upperEndMeroField := fun h =>
    upperEndTranslationMeroEquiv (I * h) xiRotatedUpperEndCarrier
  have hconst : algebraMap SmallGrowthMeromorphicField upperEndMeroField a =
      -algebraMap ℂ upperEndMeroField I := by
    change entireFieldToUpperEndMero (-constEntire ℂ I) = _
    rw [map_neg]
    change -entireFieldToUpperEndMero (constEntire ℂ I) = _
    rw [constEntire_apply, entireFieldToUpperEndMero_ofEntire]
    congr 1
    change algebraMap upperEndAnalyticSubring upperEndMeroField
        (entireToUpperEndAnalytic ⟨fun _ : ℂ => I, analyticOnNhd_const⟩) =
      upperEndPolyToMero (Polynomial.C I)
    change algebraMap upperEndAnalyticSubring upperEndMeroField
        (entireToUpperEndAnalytic ⟨fun _ : ℂ => I, analyticOnNhd_const⟩) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndPolyToAnalytic (Polynomial.C I))
    congr 1
    apply Subtype.ext
    change ((fun _ : ℂ => I) : Germ upperEndFilter ℂ) =
      ((fun z : ℂ => (Polynomial.C I).eval z) : Germ upperEndFilter ℂ)
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (by simp)
  have hlog : (fun h : ℂ => (u h)′ / u h) =
      fun h : ℂ => algebraMap SmallGrowthMeromorphicField upperEndMeroField a *
        upperEndTranslationMeroEquiv (I * h)
          xiLogDerivRotatedUpperEndCarrier := by
    funext h
    change (upperEndTranslationMeroEquiv (I * h) xiRotatedUpperEndCarrier)′ /
        upperEndTranslationMeroEquiv (I * h) xiRotatedUpperEndCarrier = _
    calc
      (upperEndTranslationMeroEquiv (I * h) xiRotatedUpperEndCarrier)′ /
          upperEndTranslationMeroEquiv (I * h) xiRotatedUpperEndCarrier =
        upperEndTranslationMeroEquiv (I * h)
          (xiRotatedUpperEndCarrier′ / xiRotatedUpperEndCarrier) := by
            rw [← upperEndTranslationMeroEquiv_deriv, map_div₀]
      _ = upperEndTranslationMeroEquiv (I * h)
          (-algebraMap ℂ upperEndMeroField I *
            xiLogDerivRotatedUpperEndCarrier) := by
            rw [xiRotatedUpperEndCarrier_logDeriv]
      _ = algebraMap SmallGrowthMeromorphicField upperEndMeroField a *
          upperEndTranslationMeroEquiv (I * h)
            xiLogDerivRotatedUpperEndCarrier := by
            rw [hconst, map_mul, map_neg]
            have hi := (upperEndTranslationMeroDifferentialAlgEquiv
              (I * h)).toAlgEquiv.commutes I
            change upperEndTranslationMeroEquiv (I * h)
                (algebraMap ℂ upperEndMeroField I) =
              algebraMap ℂ upperEndMeroField I at hi
            rw [hi]
  apply (differentialIndependent_deriv_div_self_iff u).mpr
  rw [hlog]
  exact hscaled

end

end RHTower
