import GaloisForLFunctions.RHTower.DeningerRationalWittInseparabilityDescent
import GaloisForLFunctions.RHTower.DeningerRationalWittNormalDomainGaloisIntersection

/-!
# Imperfect normal-domain rational-Witt descent

This module combines the imperfect-field inseparability classification with normalization
incidence and integral closedness.  For every integrally closed domain `A`, with no perfectness
assumption on its fraction field, a reduced-monoid-algebra element over the absolute closure
descends from `W_rat(A)` exactly when it is absolute-Galois invariant, its atom coefficients
have Deninger's inseparability divisibility, and its rational-Witt vector comes from the absolute
normalization.

Thus this is the sharp normal-domain correction of the domain clause in Deninger's Theorem 1.2.
The separately formalized cusp counterexample shows normality cannot be removed.
-/

namespace RHTower
noncomputable section

open scoped nonZeroDivisors

theorem deningerRationalWittNormalDomain_galoisInvariant_insepDivisible_normalization_iff_exists_base
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (x : MonoidAlgebra ℤ (DeningerRationalWittAbsoluteClosure A)ˣ) :
    ((∀ g : DeningerRationalWittAbsoluteGalois (FractionRing A),
        deningerRationalWittIntegralGaloisAction (FractionRing A) g x = x) ∧
      deningerRationalWittIntegralAtomInsepDivisible (FractionRing A) x ∧
      ∃ wB : DeningerRationalWittAdditive
          (DeningerRationalWittAbsoluteNormalization A),
        deningerRationalWittAdditiveMap
            (integralClosure A
              (DeningerRationalWittAbsoluteClosure A)).val.toRingHom wB =
          Additive.toMul
            (deningerRationalWittReducedMonoidAlgebraToAdditive
              (DeningerRationalWittAbsoluteClosure A) x)) ↔
      ∃ wA : DeningerRationalWittAdditive A,
        deningerRationalWittAdditiveMap
            (algebraMap A (DeningerRationalWittAbsoluteClosure A)) wA =
          Additive.toMul
            (deningerRationalWittReducedMonoidAlgebraToAdditive
              (DeningerRationalWittAbsoluteClosure A) x) := by
  letI : IsScalarTower A (FractionRing A)
      (DeningerRationalWittAbsoluteClosure A) := inferInstance
  letI : Algebra.IsAlgebraic A (DeningerRationalWittAbsoluteClosure A) :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := A) (K := FractionRing A)
        (C := DeningerRationalWittAbsoluteClosure A)).mpr inferInstance
  letI : FaithfulSMul A (DeningerRationalWittAbsoluteClosure A) :=
    (faithfulSMul_iff_algebraMap_injective A
      (DeningerRationalWittAbsoluteClosure A)).mpr <| by
      intro a b hab
      apply IsFractionRing.injective A (FractionRing A)
      apply (algebraMap (FractionRing A)
        (DeningerRationalWittAbsoluteClosure A)).injective
      simpa only [IsScalarTower.algebraMap_apply A (FractionRing A)
        (DeningerRationalWittAbsoluteClosure A)] using hab
  letI : IsFractionRing (DeningerRationalWittAbsoluteNormalization A)
      (DeningerRationalWittAbsoluteClosure A) :=
    integralClosure.isFractionRing_of_algebraic
      (fun a ha => FaithfulSMul.algebraMap_injective A
        (DeningerRationalWittAbsoluteClosure A) (ha.trans (map_zero _).symm))
  let eBL : FractionRing (DeningerRationalWittAbsoluteNormalization A)
      ≃ₐ[DeningerRationalWittAbsoluteNormalization A]
        DeningerRationalWittAbsoluteClosure A :=
    FractionRing.algEquiv (DeningerRationalWittAbsoluteNormalization A)
      (DeningerRationalWittAbsoluteClosure A)
  letI : IsAlgClosed
      (FractionRing (DeningerRationalWittAbsoluteNormalization A)) :=
    deningerIsAlgClosed_of_ringEquiv eBL.toRingEquiv
  letI : IsIntegrallyClosed
      (DeningerRationalWittAbsoluteNormalization A) :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn
      (DeningerRationalWittAbsoluteNormalization A)
      (DeningerRationalWittAbsoluteClosure A)
  constructor
  · rintro ⟨hxG, hxd, wB, hwB⟩
    let e := deningerRationalWittReducedMonoidAlgebraRingEquiv
      (DeningerRationalWittAbsoluteClosure A)
    let w : DeningerRationalWittRing (DeningerRationalWittAbsoluteClosure A) := e x
    have hwB' : deningerRationalWittAdditiveMap
        (integralClosure A
          (DeningerRationalWittAbsoluteClosure A)).val.toRingHom wB =
        Additive.toMul w.additiveVal := by
      rw [deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal]
      exact hwB
    let xB : MonoidAlgebra ℤ (DeningerRationalWittAbsoluteNormalization A)⁰ :=
      (deningerAICRationalWittComparisonEquiv
        (DeningerRationalWittAbsoluteNormalization A)).symm (Additive.ofMul wB)
    let fBL := (integralClosure A
      (DeningerRationalWittAbsoluteClosure A)).val.toRingHom
    let uBL := deningerRationalWittNonzeroDivisorUnitMap fBL Subtype.val_injective
    have hxmap : x = MonoidAlgebra.mapDomainRingHom ℤ uBL xB := by
      simpa [w, e, xB, uBL] using
        (deningerRationalWittMappedNormalization_presentation
          fBL Subtype.val_injective wB w hwB')
    let s := deningerRationalWittPositiveAtoms x
    let t := deningerRationalWittNegativeAtoms x
    let P := deningerRationalWittAtomPolynomial s
    let Q := deningerRationalWittAtomPolynomial t
    have hpos : ∀ a ∈ s,
        IsIntegral A (a : DeningerRationalWittAbsoluteClosure A) := by
      intro a ha
      change a ∈ deningerRationalWittPositiveAtoms x at ha
      rw [hxmap] at ha
      exact deningerRationalWittPositiveAtom_integral_of_mappedNormalization
        fBL Subtype.val_injective xB (fun b => b.1.2) ha
    have hneg : ∀ a ∈ t,
        IsIntegral A (a : DeningerRationalWittAbsoluteClosure A) := by
      intro a ha
      change a ∈ deningerRationalWittNegativeAtoms x at ha
      rw [hxmap] at ha
      exact deningerRationalWittNegativeAtom_integral_of_mappedNormalization
        fBL Subtype.val_injective xB (fun b => b.1.2) ha
    have hPint : ∀ n, IsIntegral A (P.coeff n) := fun n =>
      deningerRationalWittAtomPolynomial_coeff_isIntegral s hpos n
    have hQint : ∀ n, IsIntegral A (Q.coeff n) := fun n =>
      deningerRationalWittAtomPolynomial_coeff_isIntegral t hneg n
    have hsG : deningerRationalWittAtomMultisetGaloisInvariant (FractionRing A) s :=
      fun g => deningerRationalWittPositiveAtoms_galois (FractionRing A) g x (hxG g)
    have htG : deningerRationalWittAtomMultisetGaloisInvariant (FractionRing A) t :=
      fun g => deningerRationalWittNegativeAtoms_galois (FractionRing A) g x (hxG g)
    obtain ⟨hsd, htd⟩ :=
      (deningerRationalWittIntegralAtomInsepDivisible_iff_positive_negative
        (FractionRing A) x).mp hxd
    obtain ⟨P0, hP0zero, hP0map⟩ :=
      deningerRationalWittAtomPolynomial_exists_base_of_galoisInvariant_insepDivisible
        (FractionRing A) s hsG hsd
    obtain ⟨Q0, hQ0zero, hQ0map⟩ :=
      deningerRationalWittAtomPolynomial_exists_base_of_galoisInvariant_insepDivisible
        (FractionRing A) t htG htd
    obtain ⟨PA, hPAmap⟩ :=
      deningerRationalWittPolynomial_exists_normal_base A P0 P hP0map hPint
    obtain ⟨QA, hQAmap⟩ :=
      deningerRationalWittPolynomial_exists_normal_base A Q0 Q hQ0map hQint
    have hPAzero : PA.coeff 0 = 1 := by
      apply IsFractionRing.injective A (FractionRing A)
      have hc := congrArg (fun R : Polynomial (FractionRing A) => R.coeff 0) hPAmap
      simpa [hP0zero] using hc
    have hQAzero : QA.coeff 0 = 1 := by
      apply IsFractionRing.injective A (FractionRing A)
      have hc := congrArg (fun R : Polynomial (FractionRing A) => R.coeff 0) hQAmap
      simpa [hQ0zero] using hc
    have hPAL : PA.map
        (algebraMap A (DeningerRationalWittAbsoluteClosure A)) = P := by
      calc
        PA.map (algebraMap A (DeningerRationalWittAbsoluteClosure A)) =
            (PA.map (algebraMap A (FractionRing A))).map
              (algebraMap (FractionRing A)
                (DeningerRationalWittAbsoluteClosure A)) := by
                  rw [Polynomial.map_map,
                    ← IsScalarTower.algebraMap_eq A (FractionRing A)
                      (DeningerRationalWittAbsoluteClosure A)]
        _ = P0.map (algebraMap (FractionRing A)
            (DeningerRationalWittAbsoluteClosure A)) := by rw [hPAmap]
        _ = P := hP0map
    have hQAL : QA.map
        (algebraMap A (DeningerRationalWittAbsoluteClosure A)) = Q := by
      calc
        QA.map (algebraMap A (DeningerRationalWittAbsoluteClosure A)) =
            (QA.map (algebraMap A (FractionRing A))).map
              (algebraMap (FractionRing A)
                (DeningerRationalWittAbsoluteClosure A)) := by
                  rw [Polynomial.map_map,
                    ← IsScalarTower.algebraMap_eq A (FractionRing A)
                      (DeningerRationalWittAbsoluteClosure A)]
        _ = Q0.map (algebraMap (FractionRing A)
            (DeningerRationalWittAbsoluteClosure A)) := by rw [hQAmap]
        _ = Q := hQ0map
    refine ⟨deningerRationalWittNormalizedFraction PA QA hPAzero hQAzero, ?_⟩
    rw [deningerRationalWittNormalizedFraction_map]
    calc
      deningerRationalWittNormalizedFraction
          (PA.map (algebraMap A (DeningerRationalWittAbsoluteClosure A)))
          (QA.map (algebraMap A (DeningerRationalWittAbsoluteClosure A))) _ _ =
        deningerRationalWittNormalizedFraction P Q
          (deningerRationalWittAtomPolynomial_coeff_zero s)
          (deningerRationalWittAtomPolynomial_coeff_zero t) := by
            simp only [deningerRationalWittNormalizedFraction]
            rw [deningerRationalWittNormalizedPolynomial_congr hPAL,
              deningerRationalWittNormalizedPolynomial_congr hQAL]
      _ = Additive.toMul
          (deningerRationalWittReducedMonoidAlgebraToAdditive
            (DeningerRationalWittAbsoluteClosure A) x) := by
        simpa [P, Q, s, t] using deningerRationalWittNormalizedFraction_eq_comparison x
  · rintro ⟨wA, hwA⟩
    let wK := deningerRationalWittAdditiveMap
      (algebraMap A (FractionRing A)) wA
    have hwK : deningerRationalWittAdditiveMap
        (algebraMap (FractionRing A) (DeningerRationalWittAbsoluteClosure A)) wK =
        Additive.toMul
          (deningerRationalWittReducedMonoidAlgebraToAdditive
            (DeningerRationalWittAbsoluteClosure A) x) := by
      change deningerRationalWittAdditiveMap
          (algebraMap (FractionRing A) (DeningerRationalWittAbsoluteClosure A))
          (deningerRationalWittAdditiveMap (algebraMap A (FractionRing A)) wA) = _
      rw [← MonoidHom.comp_apply, ← deningerRationalWittAdditiveMap_comp]
      simpa only [IsScalarTower.algebraMap_eq A (FractionRing A)
        (DeningerRationalWittAbsoluteClosure A)] using hwA
    have hfield :=
      (deningerRationalWittIntegralGaloisInvariantInsepDivisible_iff_exists_base
        (FractionRing A) x).mpr ⟨wK, hwK⟩
    refine ⟨hfield.1, hfield.2, ?_⟩
    let wB := deningerRationalWittAdditiveMap
      (algebraMap A (DeningerRationalWittAbsoluteNormalization A)) wA
    refine ⟨wB, ?_⟩
    change deningerRationalWittAdditiveMap
        (integralClosure A (DeningerRationalWittAbsoluteClosure A)).val.toRingHom
        (deningerRationalWittAdditiveMap
          (algebraMap A (DeningerRationalWittAbsoluteNormalization A)) wA) = _
    rw [← MonoidHom.comp_apply, ← deningerRationalWittAdditiveMap_comp]
    simpa using hwA

end
end RHTower

