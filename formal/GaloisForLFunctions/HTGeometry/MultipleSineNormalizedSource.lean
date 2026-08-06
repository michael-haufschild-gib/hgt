import GaloisForLFunctions.HTGeometry.MultipleSineRationalNormalization
import GaloisForLFunctions.HTGeometry.PolynomialShiftDifference

/-!
# The normalized two-period source and its exact difference equation

Adding the rational normalization to the two-period multiple-sine source turns the ladder into

```text
(T_k - 1) M = -(π/ω_j) cot(π z/ω_j) + Q_k(z),
```

with `Q_k` a polynomial: every pole of the accumulated rational defect has cancelled.  This is the
last step before the exact double-sine difference equation, where discrete integration removes the
polynomial up to a constant.

The translations commute on the meromorphic field, which is what makes the two directions'
polynomial remainders a cocycle.
-/

open Filter Set Topology Complex Polynomial
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance normalizedSourceDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

/-! ### Translations commute -/

theorem addTranslationAnalyticEquiv_comm (a b : ℂ) (x : analyticSubring (Set.univ : Set ℂ)) :
    addTranslationAnalyticEquiv a (addTranslationAnalyticEquiv b x)
      = addTranslationAnalyticEquiv b (addTranslationAnalyticEquiv a x) := by
  apply Subtype.ext
  show ((precompAnalytic (analyticOnNhd_addTranslation a _) (Set.mapsTo_univ _ _)
      (precompAnalytic (analyticOnNhd_addTranslation b _) (Set.mapsTo_univ _ _) x) :
        analyticSubring (Set.univ : Set ℂ)) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) =
    ((precompAnalytic (analyticOnNhd_addTranslation b _) (Set.mapsTo_univ _ _)
      (precompAnalytic (analyticOnNhd_addTranslation a _) (Set.mapsTo_univ _ _) x) :
        analyticSubring (Set.univ : Set ℂ)) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
  rw [precompAnalytic_coe, precompAnalytic_coe, precompAnalytic_coe, precompAnalytic_coe]
  induction (x : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) using Germ.inductionOn with
  | _ F =>
    rw [Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto]
    refine Germ.coe_eq.mpr (eventually_principal.mpr fun z _ => ?_)
    simp only [Function.comp_apply, addTranslation]
    ring_nf

/-- **Translations commute on the meromorphic field.** -/
theorem addTranslationMeroEquiv_comm (a b : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv a (addTranslationMeroEquiv b x)
      = addTranslationMeroEquiv b (addTranslationMeroEquiv a x) := by
  have hext :
      (((addTranslationMeroEquiv a).toRingHom).comp ((addTranslationMeroEquiv b).toRingHom)) =
        (((addTranslationMeroEquiv b).toRingHom).comp ((addTranslationMeroEquiv a).toRingHom)) := by
    refine IsLocalization.ringHom_ext
      (nonZeroDivisors (analyticSubring (Set.univ : Set ℂ))) ?_
    ext c
    show addTranslationMeroEquiv a (addTranslationMeroEquiv b
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) c)) =
      addTranslationMeroEquiv b (addTranslationMeroEquiv a
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) c))
    rw [addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
      addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
      addTranslationAnalyticEquiv_comm]
  simpa using DFunLike.congr_fun hext x

end

end GaloisForLFunctions

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The antisymmetrized ladder-correction polynomial: the remainder after normalization. -/
def normalizedRemainder (ω : ι → ℂ) (S : Finset ι) (k j : ι) (hk : k ∈ S) : Polynomial ℂ :=
  barnesLadderPolyPart (subframe ω S) ⟨k, hk⟩
    - (barnesLadderPolyPart (subframe ω S) ⟨k, hk⟩).comp
        (Polynomial.C (ω j) - Polynomial.X)

/-- **The normalized source has a polynomial difference defect.**  Adding the rational
normalization cancels every pole, leaving the antisymmetrized ladder-correction polynomial. -/
theorem normalizedSource_shiftDiff (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (S : Finset ι) (k j : ι) (hk : k ∈ S) (herase : S.erase k = ({j} : Finset ι))
    (hcard : S.card = 2) (hS : S.Nonempty) :
    addTranslationMeroEquiv (ω k)
        (frameSourceMero ω hω S hS + ratMero (normalizationRat (ω k + ω j)))
      - (frameSourceMero ω hω S hS + ratMero (normalizationRat (ω k + ω j)))
    = -periodCotMero (ω j)
      + ratMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) (normalizedRemainder ω S k j hk)) := by
  classical
  haveI : Nonempty {i : ι // i ∈ S} := ⟨⟨k, hk⟩⟩
  have hjmem : j ∈ S.erase k := by
    rw [herase]
    exact Finset.mem_singleton_self j
  haveI : Nonempty {i : ι // i ∈ S.erase k} := ⟨⟨j, hjmem⟩⟩
  have h2 : 2 ≤ S.card := by omega
  have hωk : ω k ≠ 0 := by
    intro hcon
    have := hω k
    rw [hcon] at this
    simp at this
  have hne : (S.erase k).Nonempty := ⟨j, hjmem⟩
  have hsingle : ({j} : Finset ι).Nonempty := ⟨j, Finset.mem_singleton_self j⟩
  set ρ : RatFunc ℂ := normalizationRat (ω k + ω j) with hρ
  set D : RatFunc ℂ := subframeLadderRat ω S k hk
      + (frameSignZ S : RatFunc ℂ) * ratReflectBy (frameReflectionPoint ω (S.erase k))
          (subframeLadderRat ω S k hk) with hD
  have hladder := multipleSine_ladder_defect_eq ω hω S k hk h2
  rw [← hD] at hladder
  have hdel : multipleSineSourceMero ω hω (S.erase k)
      = periodCotMero (ω j) + ratMero (orderOneCorrection (ω j)) := by
    rw [← frameSourceMero_eq ω hω (S.erase k) hne,
      frameSourceMero_congr ω hω herase hne hsingle, frameSourceMero_singleton_eq]
  have hsrc : multipleSineSourceMero ω hω S = frameSourceMero ω hω S hS :=
    (frameSourceMero_eq ω hω S hS).symm
  rw [hsrc, hdel] at hladder
  have hshift : addTranslationMeroEquiv (ω k) (ratMero ρ)
      = ratMero (ratShiftBy (ω k) ρ) :=
    addTranslationMeroEquiv_ratfuncToMero_by (ω k) ρ
  have hnorm := multipleSine_two_normalized_defect ω S k j hk herase hcard hωk
  rw [← hD, ← hρ] at hnorm
  have hnormM := congrArg ratMero hnorm
  rw [map_add, map_sub, map_sub, ← normalizedRemainder] at hnormM
  rw [map_add, hshift]
  linear_combination hladder + hnormM

end

end GaloisForLFunctions.HTGeometry
