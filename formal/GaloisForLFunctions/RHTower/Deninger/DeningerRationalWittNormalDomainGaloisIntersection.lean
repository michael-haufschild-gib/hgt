import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittAICDomainComparison
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittDomainDescentCounterexample
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Deninger's rational-Witt Galois intersection over normal domains

The unrestricted domain-level Galois descent assertion fails.  Over an integrally
closed domain `A` with perfect fraction field, however, the intersection of the
Galois-fixed rational Witt vectors with those coming from the absolute integral
closure is exactly the image of the rational Witt vectors of `A`.

The proof uses the literal reduced-monoid-algebra carrier.  Integral closure
membership makes every positive and negative atom integral over `A`; Galois
fixedness descends their two canonical atom polynomials to `FractionRing A`; and
normality descends their coefficients further to `A`.
-/

namespace RHTower

noncomputable section

open scoped nonZeroDivisors

/-- Absolute algebraic closure used in the corrected domain-level descent theorem. -/
abbrev DeningerRationalWittAbsoluteClosure
    (A : Type*) [CommRing A] [IsDomain A] :=
  AlgebraicClosure (FractionRing A)

/-- Absolute integral closure used in the corrected domain-level descent theorem. -/
abbrev DeningerRationalWittAbsoluteNormalization
    (A : Type*) [CommRing A] [IsDomain A] :=
  integralClosure A (DeningerRationalWittAbsoluteClosure A)

/-- An injective map from a domain to a field sends non-zero-divisors to units. -/
noncomputable def deningerRationalWittNonzeroDivisorUnitMap
    {B L : Type*} [CommRing B] [IsDomain B] [Field L]
    (f : B →+* L) (hf : Function.Injective f) : B⁰ →* Lˣ where
  toFun b := Units.mk0 (f b.1)
    ((map_ne_zero_iff f hf).mpr (mem_nonZeroDivisors_iff_ne_zero.mp b.2))
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- Every positive atom in the image of a domain presentation is integral. -/
theorem deningerRationalWittPositiveAtom_integral_of_mappedNormalization
    {R B L : Type*} [CommRing R] [CommRing B] [IsDomain B] [Field L]
    [Algebra R L] (f : B →+* L) (hf : Function.Injective f)
    (xB : MonoidAlgebra ℤ B⁰)
    (hB : ∀ b : B⁰, IsIntegral R (f b.1))
    {a : Lˣ}
    (ha : a ∈ deningerRationalWittPositiveAtoms
      (MonoidAlgebra.mapDomainRingHom ℤ
        (deningerRationalWittNonzeroDivisorUnitMap f hf) xB)) :
    IsIntegral R (a : L) := by
  let xL := MonoidAlgebra.mapDomainRingHom ℤ
    (deningerRationalWittNonzeroDivisorUnitMap f hf) xB
  rw [deningerRationalWittPositiveAtoms, Finsupp.mem_toMultiset,
    Finsupp.mem_support_iff] at ha
  change (xL.coeff a).toNat ≠ 0 at ha
  have hcoeff : xL.coeff a ≠ 0 := by
    intro hz
    apply ha
    simp [hz]
  change (Finsupp.mapDomain
    (deningerRationalWittNonzeroDivisorUnitMap f hf) xB.coeff) a ≠ 0 at hcoeff
  obtain ⟨b, hb⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hcoeff
  have hi := hB b
  rw [← hb]
  simpa [deningerRationalWittNonzeroDivisorUnitMap] using hi

/-- Every negative atom in the image of a domain presentation is integral. -/
theorem deningerRationalWittNegativeAtom_integral_of_mappedNormalization
    {R B L : Type*} [CommRing R] [CommRing B] [IsDomain B] [Field L]
    [Algebra R L] (f : B →+* L) (hf : Function.Injective f)
    (xB : MonoidAlgebra ℤ B⁰)
    (hB : ∀ b : B⁰, IsIntegral R (f b.1))
    {a : Lˣ}
    (ha : a ∈ deningerRationalWittNegativeAtoms
      (MonoidAlgebra.mapDomainRingHom ℤ
        (deningerRationalWittNonzeroDivisorUnitMap f hf) xB)) :
    IsIntegral R (a : L) := by
  let xL := MonoidAlgebra.mapDomainRingHom ℤ
    (deningerRationalWittNonzeroDivisorUnitMap f hf) xB
  rw [deningerRationalWittNegativeAtoms, Finsupp.mem_toMultiset,
    Finsupp.mem_support_iff] at ha
  change (-xL.coeff a).toNat ≠ 0 at ha
  have hcoeff : xL.coeff a ≠ 0 := by
    intro hz
    apply ha
    simp [hz]
  change (Finsupp.mapDomain
    (deningerRationalWittNonzeroDivisorUnitMap f hf) xB.coeff) a ≠ 0 at hcoeff
  obtain ⟨b, hb⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hcoeff
  have hi := hB b
  rw [← hb]
  simpa [deningerRationalWittNonzeroDivisorUnitMap] using hi

/-- Naturality of the algebraically-closed-fraction-field comparison into a field. -/
theorem deningerAICRationalWittComparison_natural_field
    {B L : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [IsAlgClosed (FractionRing B)] [Field L]
    (f : B →+* L) (hf : Function.Injective f)
    (x : MonoidAlgebra ℤ B⁰) :
    deningerRationalWittReducedMonoidAlgebraToAdditive L
        (MonoidAlgebra.mapDomainRingHom ℤ
          (deningerRationalWittNonzeroDivisorUnitMap f hf) x) =
      Additive.ofMul
        (deningerRationalWittAdditiveMap f
          (Additive.toMul (deningerAICRationalWittComparison B x))) := by
  induction x using MonoidAlgebra.induction with
  | zero => simp
  | single_add a n x _ha _hn ih =>
      rw [map_add, map_add, map_add, ih]
      simp [deningerAICRationalWittComparison_single,
        deningerRationalWittReducedMonoidAlgebraToAdditive_single,
        deningerRationalWittAdditiveMap_teichmuller,
        deningerRationalWittNonzeroDivisorUnitMap]

/-- A rational Witt vector mapped from an AIC domain has the mapped canonical
reduced-monoid-algebra presentation. -/
theorem deningerRationalWittMappedNormalization_presentation
    {B L : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [IsAlgClosed (FractionRing B)] [Field L] [IsAlgClosed L]
    (f : B →+* L) (hf : Function.Injective f)
    (wB : DeningerRationalWittAdditive B)
    (w : DeningerRationalWittRing L)
    (hwB : deningerRationalWittAdditiveMap f wB = Additive.toMul w.additiveVal) :
    let e := deningerRationalWittReducedMonoidAlgebraRingEquiv L
    let xL : MonoidAlgebra ℤ Lˣ := e.symm w
    let xB : MonoidAlgebra ℤ B⁰ :=
      (deningerAICRationalWittComparisonEquiv B).symm (Additive.ofMul wB)
    xL = MonoidAlgebra.mapDomainRingHom ℤ
      (deningerRationalWittNonzeroDivisorUnitMap f hf) xB := by
  dsimp only
  let e := deningerRationalWittReducedMonoidAlgebraRingEquiv L
  let xL : MonoidAlgebra ℤ Lˣ := e.symm w
  let xB : MonoidAlgebra ℤ B⁰ :=
    (deningerAICRationalWittComparisonEquiv B).symm (Additive.ofMul wB)
  have hxB : deningerAICRationalWittComparison B xB = Additive.ofMul wB := by
    exact (deningerAICRationalWittComparisonEquiv B).apply_symm_apply
      (Additive.ofMul wB)
  apply e.injective
  apply DeningerRationalWittRing.ext
  change (e xL).additiveVal =
    (e (MonoidAlgebra.mapDomainRingHom ℤ
      (deningerRationalWittNonzeroDivisorUnitMap f hf) xB)).additiveVal
  rw [deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal]
  calc
    (e xL).additiveVal = w.additiveVal := by simp [xL]
    _ = Additive.ofMul (deningerRationalWittAdditiveMap f wB) := by rw [hwB]; simp
    _ = Additive.ofMul
        (deningerRationalWittAdditiveMap f
          (Additive.toMul (deningerAICRationalWittComparison B xB))) := by
      congr 2
      rw [hxB]
      rfl
    _ = deningerRationalWittReducedMonoidAlgebraToAdditive L
        (MonoidAlgebra.mapDomainRingHom ℤ
          (deningerRationalWittNonzeroDivisorUnitMap f hf) xB) :=
      (deningerAICRationalWittComparison_natural_field f hf xB).symm

/-- Coefficients of a Teichmüller factor are integral when its atom is integral. -/
theorem deningerRationalWittTeichmullerPolynomial_coeff_isIntegral
    {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (a : L) (ha : IsIntegral R a) (n : ℕ) :
    IsIntegral R ((deningerRationalWittTeichmullerPolynomial a).coeff n) := by
  rw [deningerRationalWittTeichmullerPolynomial, Polynomial.coeff_sub,
    Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
  by_cases h0 : n = 0
  · simpa [h0] using (isIntegral_one : IsIntegral R (1 : L))
  by_cases h1 : n = 1
  · simpa [h0, h1] using ha.neg
  · simpa [h0, h1] using (isIntegral_zero : IsIntegral R (0 : L))

/-- Every coefficient of an atom polynomial is integral when all atoms are integral. -/
theorem deningerRationalWittAtomPolynomial_coeff_isIntegral
    {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (s : Multiset Lˣ) (hs : ∀ a ∈ s, IsIntegral R (a : L)) (n : ℕ) :
    IsIntegral R ((deningerRationalWittAtomPolynomial s).coeff n) := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
      rw [deningerRationalWittAtomPolynomial, Multiset.map_zero,
        Multiset.prod_zero, Polynomial.coeff_one]
      split
      · exact isIntegral_one
      · exact isIntegral_zero
  | @cons a s ih =>
      rw [show deningerRationalWittAtomPolynomial (a ::ₘ s) =
          deningerRationalWittTeichmullerPolynomial (a : L) *
            deningerRationalWittAtomPolynomial s by
        simp [deningerRationalWittAtomPolynomial], Polynomial.coeff_mul]
      apply IsIntegral.sum
      intro ij hij
      exact (deningerRationalWittTeichmullerPolynomial_coeff_isIntegral
          (a : L) (hs a (by simp)) ij.1).mul
        (ih (fun b hb => hs b (by simp [hb])) ij.2)

/-- A polynomial over the fraction field whose coefficients become integral over a
normal base after embedding in the algebraic closure already lifts from the base. -/
theorem deningerRationalWittPolynomial_exists_normal_base
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (P0 : Polynomial (FractionRing A))
    (P : Polynomial (DeningerRationalWittAbsoluteClosure A))
    (hmap : P0.map (algebraMap (FractionRing A)
      (DeningerRationalWittAbsoluteClosure A)) = P)
    (hP : ∀ n, IsIntegral A (P.coeff n)) :
    ∃ PA : Polynomial A,
      PA.map (algebraMap A (FractionRing A)) = P0 := by
  have hlifts : P0 ∈ Polynomial.lifts
      (algebraMap A (FractionRing A)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    apply (IsIntegrallyClosed.isIntegral_iff).mp
    apply RingHom.IsIntegralElem.of_map
      (g := algebraMap (FractionRing A)
        (DeningerRationalWittAbsoluteClosure A))
      (algebraMap (FractionRing A)
        (DeningerRationalWittAbsoluteClosure A)).injective
    have hc := congrArg
      (fun Q : Polynomial (DeningerRationalWittAbsoluteClosure A) => Q.coeff n) hmap
    rw [Polynomial.coeff_map] at hc
    rw [hc]
    exact hP n
  obtain ⟨PA, hPA, _⟩ := Polynomial.exists_support_eq_of_mem_lifts hlifts
  exact ⟨PA, hPA⟩

/-- Algebraic closedness transfers through a ring equivalence of fields. -/
theorem deningerIsAlgClosed_of_ringEquiv
    {K L : Type*} [Field K] [Field L] [IsAlgClosed L]
    (e : K ≃+* L) : IsAlgClosed K where
  splits P := Polynomial.Splits.of_splits_map e.toRingHom
    (IsAlgClosed.splits (P.map e.toRingHom))
    (fun a _ => e.surjective a)

/-- **Corrected Deninger domain descent.**  For a normal domain with perfect
fraction field, the Galois-fixed rational Witt vectors which come from its absolute
integral closure are exactly those which come from the base domain. -/
theorem deningerRationalWittNormalDomain_galoisFixed_normalization_iff_exists_base
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [PerfectField (FractionRing A)]
    (w : DeningerRationalWittRing (DeningerRationalWittAbsoluteClosure A)) :
    ((∀ g : DeningerRationalWittAbsoluteGalois (FractionRing A),
        deningerRationalWittLiteralGaloisAction (FractionRing A) g w = w) ∧
      ∃ wB : DeningerRationalWittAdditive
          (DeningerRationalWittAbsoluteNormalization A),
        deningerRationalWittAdditiveMap
            (integralClosure A
              (DeningerRationalWittAbsoluteClosure A)).val.toRingHom wB =
          Additive.toMul w.additiveVal) ↔
      ∃ wA : DeningerRationalWittAdditive A,
        deningerRationalWittAdditiveMap
            (algebraMap A (DeningerRationalWittAbsoluteClosure A)) wA =
          Additive.toMul w.additiveVal := by
  letI : IsScalarTower A (FractionRing A)
      (DeningerRationalWittAbsoluteClosure A) := inferInstance
  letI : Algebra.IsAlgebraic A (DeningerRationalWittAbsoluteClosure A) :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := A) (K := FractionRing A)
        (C := DeningerRationalWittAbsoluteClosure A)).mpr inferInstance
  letI : FaithfulSMul A (DeningerRationalWittAbsoluteClosure A) :=
    (faithfulSMul_iff_algebraMap_injective A
      (DeningerRationalWittAbsoluteClosure A)).mpr <| by
      intro x y hxy
      apply IsFractionRing.injective A (FractionRing A)
      apply (algebraMap (FractionRing A)
        (DeningerRationalWittAbsoluteClosure A)).injective
      simpa only [IsScalarTower.algebraMap_apply A (FractionRing A)
        (DeningerRationalWittAbsoluteClosure A)] using hxy
  letI : IsFractionRing (DeningerRationalWittAbsoluteNormalization A)
      (DeningerRationalWittAbsoluteClosure A) :=
    integralClosure.isFractionRing_of_algebraic
      (fun x hx => FaithfulSMul.algebraMap_injective A
        (DeningerRationalWittAbsoluteClosure A) (hx.trans (map_zero _).symm))
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
  · rintro ⟨hfixed, wB, hwB⟩
    let e := deningerRationalWittReducedMonoidAlgebraRingEquiv
      (DeningerRationalWittAbsoluteClosure A)
    let xL : MonoidAlgebra ℤ (DeningerRationalWittAbsoluteClosure A)ˣ := e.symm w
    let xB : MonoidAlgebra ℤ (DeningerRationalWittAbsoluteNormalization A)⁰ :=
      (deningerAICRationalWittComparisonEquiv
        (DeningerRationalWittAbsoluteNormalization A)).symm (Additive.ofMul wB)
    let fBL := (integralClosure A
      (DeningerRationalWittAbsoluteClosure A)).val.toRingHom
    let uBL := deningerRationalWittNonzeroDivisorUnitMap fBL Subtype.val_injective
    have hxmap : xL = MonoidAlgebra.mapDomainRingHom ℤ uBL xB := by
      exact deningerRationalWittMappedNormalization_presentation
        fBL Subtype.val_injective wB w hwB
    have hxfixed : ∀ g : DeningerRationalWittAbsoluteGalois (FractionRing A),
        deningerRationalWittIntegralGaloisAction (FractionRing A) g xL = xL := by
      intro g
      have hw' := congrArg e.symm (hfixed g)
      simpa [e, xL, deningerRationalWittLiteralGaloisAction] using hw'
    let P := deningerRationalWittAtomPolynomial
      (deningerRationalWittPositiveAtoms xL)
    let Q := deningerRationalWittAtomPolynomial
      (deningerRationalWittNegativeAtoms xL)
    have hpos : ∀ a ∈ deningerRationalWittPositiveAtoms xL,
        IsIntegral A (a : DeningerRationalWittAbsoluteClosure A) := by
      intro a ha
      rw [hxmap] at ha
      apply deningerRationalWittPositiveAtom_integral_of_mappedNormalization
        fBL Subtype.val_injective xB (fun b => b.1.2) ha
    have hneg : ∀ a ∈ deningerRationalWittNegativeAtoms xL,
        IsIntegral A (a : DeningerRationalWittAbsoluteClosure A) := by
      intro a ha
      rw [hxmap] at ha
      apply deningerRationalWittNegativeAtom_integral_of_mappedNormalization
        fBL Subtype.val_injective xB (fun b => b.1.2) ha
    have hPint : ∀ n, IsIntegral A (P.coeff n) := by
      intro n
      exact deningerRationalWittAtomPolynomial_coeff_isIntegral _ hpos n
    have hQint : ∀ n, IsIntegral A (Q.coeff n) := by
      intro n
      exact deningerRationalWittAtomPolynomial_coeff_isIntegral _ hneg n
    obtain ⟨P0, hP0map⟩ :=
      deningerRationalWittPolynomial_galoisFixed_exists_base
        (FractionRing A) P
        (fun g => deningerRationalWittPositiveAtomPolynomial_galois
          (FractionRing A) g xL (hxfixed g))
    obtain ⟨Q0, hQ0map⟩ :=
      deningerRationalWittPolynomial_galoisFixed_exists_base
        (FractionRing A) Q
        (fun g => deningerRationalWittNegativeAtomPolynomial_galois
          (FractionRing A) g xL (hxfixed g))
    obtain ⟨PA, hPAmap⟩ :=
      deningerRationalWittPolynomial_exists_normal_base A P0 P hP0map hPint
    obtain ⟨QA, hQAmap⟩ :=
      deningerRationalWittPolynomial_exists_normal_base A Q0 Q hQ0map hQint
    have hP0zero : P0.coeff 0 = 1 := by
      apply (algebraMap (FractionRing A)
        (DeningerRationalWittAbsoluteClosure A)).injective
      have hc := congrArg
        (fun R : Polynomial (DeningerRationalWittAbsoluteClosure A) => R.coeff 0)
        hP0map
      simpa [P] using hc
    have hQ0zero : Q0.coeff 0 = 1 := by
      apply (algebraMap (FractionRing A)
        (DeningerRationalWittAbsoluteClosure A)).injective
      have hc := congrArg
        (fun R : Polynomial (DeningerRationalWittAbsoluteClosure A) => R.coeff 0)
        hQ0map
      simpa [Q] using hc
    have hPAzero : PA.coeff 0 = 1 := by
      apply IsFractionRing.injective A (FractionRing A)
      have hc := congrArg
        (fun R : Polynomial (FractionRing A) => R.coeff 0) hPAmap
      simpa [hP0zero] using hc
    have hQAzero : QA.coeff 0 = 1 := by
      apply IsFractionRing.injective A (FractionRing A)
      have hc := congrArg
        (fun R : Polynomial (FractionRing A) => R.coeff 0) hQAmap
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
          (deningerRationalWittAtomPolynomial_coeff_zero _)
          (deningerRationalWittAtomPolynomial_coeff_zero _) := by
            simp only [deningerRationalWittNormalizedFraction]
            rw [deningerRationalWittNormalizedPolynomial_congr hPAL,
              deningerRationalWittNormalizedPolynomial_congr hQAL]
      _ = Additive.toMul
          (deningerRationalWittReducedMonoidAlgebraToAdditive
            (DeningerRationalWittAbsoluteClosure A) xL) := by
        simpa [P, Q] using deningerRationalWittNormalizedFraction_eq_comparison xL
      _ = Additive.toMul w.additiveVal := by
        congr 1
        calc
          deningerRationalWittReducedMonoidAlgebraToAdditive
              (DeningerRationalWittAbsoluteClosure A) xL = (e xL).additiveVal :=
            (deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal xL).symm
          _ = w.additiveVal := by simp [e, xL]
  · rintro ⟨wA, hwA⟩
    let wK := deningerRationalWittAdditiveMap
      (algebraMap A (FractionRing A)) wA
    have hwLift : deningerRationalWittPerfectBaseLift (FractionRing A) wK = w := by
      apply DeningerRationalWittRing.ext
      change Additive.ofMul
          (deningerRationalWittAdditiveMap
            (algebraMap (FractionRing A)
              (DeningerRationalWittAbsoluteClosure A)) wK) = w.additiveVal
      have hc : deningerRationalWittAdditiveMap
          (algebraMap (FractionRing A)
            (DeningerRationalWittAbsoluteClosure A)) wK =
          deningerRationalWittAdditiveMap
            (algebraMap A (DeningerRationalWittAbsoluteClosure A)) wA := by
        change deningerRationalWittAdditiveMap
            (algebraMap (FractionRing A)
              (DeningerRationalWittAbsoluteClosure A))
              (deningerRationalWittAdditiveMap
                (algebraMap A (FractionRing A)) wA) = _
        rw [← MonoidHom.comp_apply, ← deningerRationalWittAdditiveMap_comp]
        congr 2
      rw [hc, hwA]
      rfl
    constructor
    · intro g
      rw [← hwLift]
      exact deningerRationalWittPerfectBaseLift_galoisFixed
        (FractionRing A) wK g
    · let wB := deningerRationalWittAdditiveMap
          (algebraMap A (DeningerRationalWittAbsoluteNormalization A)) wA
      refine ⟨wB, ?_⟩
      calc
        deningerRationalWittAdditiveMap
            (integralClosure A
              (DeningerRationalWittAbsoluteClosure A)).val.toRingHom wB =
          deningerRationalWittAdditiveMap
            ((integralClosure A
              (DeningerRationalWittAbsoluteClosure A)).val.toRingHom.comp
              (algebraMap A (DeningerRationalWittAbsoluteNormalization A))) wA := by
                rw [deningerRationalWittAdditiveMap_comp]
                rfl
        _ = deningerRationalWittAdditiveMap
            (algebraMap A (DeningerRationalWittAbsoluteClosure A)) wA := by
              congr 2
        _ = Additive.toMul w.additiveVal := hwA

end

end RHTower
