import GaloisForLFunctions.RHTower.DeningerRationalWittLiteralGaloisDescent
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Finsupp.Multiset

/-!
# Exact base-field descent for literal rational Witt vectors

For a prime `p`, this module proves the source-level fixed-ring theorem behind Deninger's
rational-Witt Galois descent.  A Frobenius-fixed element of literal
`W_rat(AlgebraicClosure (ZMod p))` is written canonically as a difference of positive and
negative Teichmüller orbit sums.  Multiplying each orbit into a normalized polynomial produces
Frobenius-fixed numerator and denominator coefficients, which descend individually to `ZMod p`.

The reverse inclusion is proved from naturality of the literal localized-polynomial comparison.
Thus the final theorem identifies Frobenius fixed points exactly with the image of the literal
base-field rational-Witt carrier; no descent premise or abstract fixed-point interface is assumed.
-/

namespace RHTower

noncomputable section

theorem deningerPrimeArithmeticFrobeniusFixed_exists_base
    (p : Nat.Primes) (x : DeningerPrimeArithmeticClosure p)
    (hx : deningerPrimeArithmeticFrobenius p x = x) :
    ∃ y : ZMod (p : ℕ),
      algebraMap (ZMod (p : ℕ)) (DeningerPrimeArithmeticClosure p) y = x := by
  have hxpow : x ^ (p : ℕ) = x := by
    change x ^ Fintype.card (ZMod (p : ℕ)) = x at hx
    simpa [ZMod.card] using hx
  have hbot : x ∈ (⊥ : Subfield (DeningerPrimeArithmeticClosure p)) :=
    (Subfield.mem_bot_iff_pow_eq_self
      (F := DeningerPrimeArithmeticClosure p) (p : ℕ)).2 hxpow
  rw [mem_bot_iff_intCast (p : ℕ)
    (DeningerPrimeArithmeticClosure p)] at hbot
  obtain ⟨n, hn⟩ := hbot
  refine ⟨(n : ZMod (p : ℕ)), ?_⟩
  simpa using hn

theorem deningerPrimePolynomialFrobeniusFixed_exists_base
    (p : Nat.Primes) (P : Polynomial (DeningerPrimeArithmeticClosure p))
    (hP : P.map (deningerPrimeArithmeticFrobenius p).toRingEquiv.toRingHom = P) :
    ∃ P0 : Polynomial (ZMod (p : ℕ)),
      P0.map (algebraMap (ZMod (p : ℕ))
        (DeningerPrimeArithmeticClosure p)) = P := by
  have hlifts : P ∈ Polynomial.lifts
      (algebraMap (ZMod (p : ℕ)) (DeningerPrimeArithmeticClosure p)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    apply deningerPrimeArithmeticFrobeniusFixed_exists_base p
    have hc := congrArg (fun Q : Polynomial (DeningerPrimeArithmeticClosure p) =>
      Q.coeff n) hP
    simpa using hc
  obtain ⟨P0, hmap, _⟩ := Polynomial.exists_support_eq_of_mem_lifts hlifts
  exact ⟨P0, hmap⟩

noncomputable def deningerRationalWittPositiveCoefficients
    {K : Type*} [Field K] (x : MonoidAlgebra ℤ Kˣ) : Kˣ →₀ ℕ :=
  x.coeff.mapRange Int.toNat (by simp)

noncomputable def deningerRationalWittNegativeCoefficients
    {K : Type*} [Field K] (x : MonoidAlgebra ℤ Kˣ) : Kˣ →₀ ℕ :=
  x.coeff.mapRange (fun n => (-n).toNat) (by simp)

noncomputable def deningerRationalWittPositiveAtoms
    {K : Type*} [Field K] (x : MonoidAlgebra ℤ Kˣ) : Multiset Kˣ :=
  Finsupp.toMultiset (deningerRationalWittPositiveCoefficients x)

noncomputable def deningerRationalWittNegativeAtoms
    {K : Type*} [Field K] (x : MonoidAlgebra ℤ Kˣ) : Multiset Kˣ :=
  Finsupp.toMultiset (deningerRationalWittNegativeCoefficients x)

noncomputable def deningerPrimeFrobeniusUnitEquiv
    (p : Nat.Primes) :
    (DeningerPrimeArithmeticClosure p)ˣ ≃
      (DeningerPrimeArithmeticClosure p)ˣ :=
  (Units.mapEquiv
    (deningerPrimeArithmeticFrobenius p).toRingEquiv.toMulEquiv).toEquiv

theorem deningerRationalWittAtomSum_coeff
    {K : Type*} [Field K] [DecidableEq K]
    (s : Multiset Kˣ) (a : Kˣ) :
    (deningerRationalWittAtomSum s).coeff a = (s.count a : ℤ) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [deningerRationalWittAtomSum]
  | @cons b s ih =>
      rw [show deningerRationalWittAtomSum (b ::ₘ s) =
        MonoidAlgebra.single b 1 + deningerRationalWittAtomSum s by
          simp [deningerRationalWittAtomSum]]
      rw [MonoidAlgebra.coeff_add]
      change (MonoidAlgebra.single b 1).coeff a +
        (deningerRationalWittAtomSum s).coeff a = _
      rw [ih, Multiset.count_cons]
      rw [MonoidAlgebra.coeff_single]
      by_cases h : b = a
      · subst b
        simp [add_comm]
      · simp [Ne.symm h]

theorem deningerRationalWitt_eq_positiveAtoms_sub_negativeAtoms
    {K : Type*} [Field K] (x : MonoidAlgebra ℤ Kˣ) :
    x = deningerRationalWittAtomSum (deningerRationalWittPositiveAtoms x) -
      deningerRationalWittAtomSum (deningerRationalWittNegativeAtoms x) := by
  classical
  apply MonoidAlgebra.ext
  ext a
  change x.coeff a =
    (deningerRationalWittAtomSum (deningerRationalWittPositiveAtoms x)).coeff a -
      (deningerRationalWittAtomSum (deningerRationalWittNegativeAtoms x)).coeff a
  rw [deningerRationalWittAtomSum_coeff, deningerRationalWittAtomSum_coeff]
  change x.coeff a =
    ((Finsupp.toMultiset (deningerRationalWittPositiveCoefficients x)).count a : ℤ) -
      ((Finsupp.toMultiset (deningerRationalWittNegativeCoefficients x)).count a : ℤ)
  rw [Finsupp.count_toMultiset, Finsupp.count_toMultiset]
  change x.coeff a = ((x.coeff a).toNat : ℤ) - (((-(x.coeff a)).toNat : ℕ) : ℤ)
  exact (Int.toNat_sub_toNat_neg (x.coeff a)).symm

theorem deningerPrimeIntegralRationalWitt_frobenius_coeff
    (p : Nat.Primes)
    (x : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ)
    (hx : deningerPrimeIntegralRationalWittFrobenius p x = x)
    (a : (DeningerPrimeArithmeticClosure p)ˣ) :
    x.coeff
        ((deningerPrimeFrobeniusUnitEquiv p).symm a) =
      x.coeff a := by
  have hc := congrArg
    (fun y : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ =>
      y.coeff a) hx
  simpa [deningerPrimeIntegralRationalWittFrobenius,
    deningerPrimeIntegralRationalWittGaloisAction,
    deningerPrimeFrobeniusUnitEquiv] using hc

theorem deningerRationalWittPositiveCoefficients_frobenius
    (p : Nat.Primes)
    (x : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ)
    (hx : deningerPrimeIntegralRationalWittFrobenius p x = x) :
    Finsupp.equivMapDomain
        (deningerPrimeFrobeniusUnitEquiv p)
        (deningerRationalWittPositiveCoefficients x) = deningerRationalWittPositiveCoefficients x := by
  classical
  apply Finsupp.ext
  intro a
  simp only [Finsupp.equivMapDomain_apply, deningerRationalWittPositiveCoefficients,
    Finsupp.mapRange_apply]
  rw [deningerPrimeIntegralRationalWitt_frobenius_coeff p x hx a]

theorem deningerRationalWittNegativeCoefficients_frobenius
    (p : Nat.Primes)
    (x : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ)
    (hx : deningerPrimeIntegralRationalWittFrobenius p x = x) :
    Finsupp.equivMapDomain
        (deningerPrimeFrobeniusUnitEquiv p)
        (deningerRationalWittNegativeCoefficients x) = deningerRationalWittNegativeCoefficients x := by
  classical
  apply Finsupp.ext
  intro a
  simp only [Finsupp.equivMapDomain_apply, deningerRationalWittNegativeCoefficients,
    Finsupp.mapRange_apply]
  rw [deningerPrimeIntegralRationalWitt_frobenius_coeff p x hx a]

theorem deningerRationalWittPositiveAtoms_frobenius
    (p : Nat.Primes)
    (x : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ)
    (hx : deningerPrimeIntegralRationalWittFrobenius p x = x) :
    (deningerRationalWittPositiveAtoms x).map
        (deningerPrimeFrobeniusUnitEquiv p) =
      deningerRationalWittPositiveAtoms x := by
  rw [deningerRationalWittPositiveAtoms, Finsupp.toMultiset_map,
    ← Finsupp.equivMapDomain_eq_mapDomain
      (deningerPrimeFrobeniusUnitEquiv p),
    deningerRationalWittPositiveCoefficients_frobenius p x hx]

theorem deningerRationalWittNegativeAtoms_frobenius
    (p : Nat.Primes)
    (x : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ)
    (hx : deningerPrimeIntegralRationalWittFrobenius p x = x) :
    (deningerRationalWittNegativeAtoms x).map
        (deningerPrimeFrobeniusUnitEquiv p) =
      deningerRationalWittNegativeAtoms x := by
  rw [deningerRationalWittNegativeAtoms, Finsupp.toMultiset_map,
    ← Finsupp.equivMapDomain_eq_mapDomain
      (deningerPrimeFrobeniusUnitEquiv p),
    deningerRationalWittNegativeCoefficients_frobenius p x hx]

def deningerRationalWittAtomPolynomial
    {A : Type*} [CommRing A] (s : Multiset Aˣ) : Polynomial A :=
  (s.map fun a : Aˣ =>
    deningerRationalWittTeichmullerPolynomial (a : A)).prod

theorem deningerRationalWittAtomPolynomial_map
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A ≃+* B) (s : Multiset Aˣ) :
    (deningerRationalWittAtomPolynomial s).map f.toRingHom =
      deningerRationalWittAtomPolynomial (s.map (Units.mapEquiv f.toMulEquiv)) := by
  simp only [deningerRationalWittAtomPolynomial, Polynomial.map_multiset_prod,
    Multiset.map_map, Function.comp_apply]
  congr 1
  apply Multiset.map_congr rfl
  intro a _ha
  ext n
  simp [deningerRationalWittTeichmullerPolynomial]

theorem deningerPrimeRationalWittPositiveAtomPolynomial_frobenius
    (p : Nat.Primes)
    (x : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ)
    (hx : deningerPrimeIntegralRationalWittFrobenius p x = x) :
    (deningerRationalWittAtomPolynomial (deningerRationalWittPositiveAtoms x)).map
        (deningerPrimeArithmeticFrobenius p).toRingEquiv.toRingHom =
      deningerRationalWittAtomPolynomial (deningerRationalWittPositiveAtoms x) := by
  rw [deningerRationalWittAtomPolynomial_map]
  exact congrArg deningerRationalWittAtomPolynomial
    (deningerRationalWittPositiveAtoms_frobenius p x hx)

theorem deningerPrimeRationalWittNegativeAtomPolynomial_frobenius
    (p : Nat.Primes)
    (x : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ)
    (hx : deningerPrimeIntegralRationalWittFrobenius p x = x) :
    (deningerRationalWittAtomPolynomial (deningerRationalWittNegativeAtoms x)).map
        (deningerPrimeArithmeticFrobenius p).toRingEquiv.toRingHom =
      deningerRationalWittAtomPolynomial (deningerRationalWittNegativeAtoms x) := by
  rw [deningerRationalWittAtomPolynomial_map]
  exact congrArg deningerRationalWittAtomPolynomial
    (deningerRationalWittNegativeAtoms_frobenius p x hx)

@[simp] theorem deningerRationalWittAtomPolynomial_coeff_zero
    {A : Type*} [CommRing A] (s : Multiset Aˣ) :
    (deningerRationalWittAtomPolynomial s).coeff 0 = 1 := by
  change Polynomial.constantCoeff
    ((s.map fun a : Aˣ =>
      deningerRationalWittTeichmullerPolynomial (a : A)).prod) = 1
  rw [map_multiset_prod]
  simp

noncomputable def deningerRationalWittNormalizedPolynomialUnit
    {A : Type*} [CommRing A] (P : Polynomial A) (hP : P.coeff 0 = 1) :
    (DeningerRationalWittLocalization A)ˣ :=
  (IsLocalization.map_units (M := deningerRationalWittDenominators A)
    (DeningerRationalWittLocalization A) ⟨P, hP⟩).unit

@[simp] theorem deningerRationalWittNormalizedPolynomialUnit_val
    {A : Type*} [CommRing A] (P : Polynomial A) (hP : P.coeff 0 = 1) :
    (deningerRationalWittNormalizedPolynomialUnit P hP :
      DeningerRationalWittLocalization A) =
      algebraMap (Polynomial A) (DeningerRationalWittLocalization A) P := by
  exact (IsLocalization.map_units (M := deningerRationalWittDenominators A)
    (DeningerRationalWittLocalization A) ⟨P, hP⟩).unit_spec

noncomputable def deningerRationalWittNormalizedPolynomial
    {A : Type*} [CommRing A] (P : Polynomial A) (hP : P.coeff 0 = 1) :
    DeningerRationalWittAdditive A := by
  refine ⟨deningerRationalWittNormalizedPolynomialUnit P hP, ?_⟩
  apply Units.ext
  change deningerRationalWittEvaluationZero A
      (deningerRationalWittNormalizedPolynomialUnit P hP :
        DeningerRationalWittLocalization A) = 1
  rw [deningerRationalWittNormalizedPolynomialUnit_val,
    deningerRationalWittEvaluationZero_algebraMap, hP]

noncomputable def deningerRationalWittNormalizedFraction
    {A : Type*} [CommRing A]
    (P Q : Polynomial A) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    DeningerRationalWittAdditive A :=
  deningerRationalWittNormalizedPolynomial P hP * (deningerRationalWittNormalizedPolynomial Q hQ)⁻¹

theorem deningerRationalWittNormalizedPolynomial_map
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (P : Polynomial A) (hP : P.coeff 0 = 1) :
    deningerRationalWittAdditiveMap f (deningerRationalWittNormalizedPolynomial P hP) =
      deningerRationalWittNormalizedPolynomial (P.map f) (by simp [hP]) := by
  apply Subtype.ext
  apply Units.ext
  change deningerRationalWittLocalizationMap f
      (deningerRationalWittNormalizedPolynomialUnit P hP :
        DeningerRationalWittLocalization A) =
    (deningerRationalWittNormalizedPolynomialUnit (P.map f) _ :
      DeningerRationalWittLocalization B)
  rw [deningerRationalWittNormalizedPolynomialUnit_val,
    deningerRationalWittNormalizedPolynomialUnit_val]
  rw [deningerRationalWittLocalizationMap, IsLocalization.map_eq]
  rfl

theorem deningerRationalWittNormalizedPolynomial_congr
    {A : Type*} [CommRing A]
    {P Q : Polynomial A} (hPQ : P = Q)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerRationalWittNormalizedPolynomial P hP =
      deningerRationalWittNormalizedPolynomial Q hQ := by
  subst Q
  rfl

theorem deningerRationalWittNormalizedFraction_map
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (P Q : Polynomial A)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerRationalWittAdditiveMap f
        (deningerRationalWittNormalizedFraction P Q hP hQ) =
      deningerRationalWittNormalizedFraction (P.map f) (Q.map f)
        (by simp [hP]) (by simp [hQ]) := by
  simp [deningerRationalWittNormalizedFraction, deningerRationalWittNormalizedPolynomial_map]

theorem deningerRationalWittNormalizedPolynomial_atomPolynomial
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    deningerRationalWittNormalizedPolynomial (deningerRationalWittAtomPolynomial s)
        (deningerRationalWittAtomPolynomial_coeff_zero s) =
      (s.map fun a : Kˣ =>
        deningerRationalWittTeichmuller (A := K) (a : K)).prod := by
  apply Subtype.ext
  apply Units.ext
  change (deningerRationalWittNormalizedPolynomialUnit (deningerRationalWittAtomPolynomial s) _ :
      DeningerRationalWittLocalization K) =
    ((((s.map fun a : Kˣ =>
      deningerRationalWittTeichmuller (A := K) (a : K)).prod).1 :
        (DeningerRationalWittLocalization K)ˣ) :
      DeningerRationalWittLocalization K)
  rw [deningerRationalWittNormalizedPolynomialUnit_val,
    deningerRationalWitt_prod_teichmuller_val]
  rfl

theorem deningerRationalWittNormalizedFraction_eq_comparison
    {K : Type*} [Field K] (x : MonoidAlgebra ℤ Kˣ) :
    deningerRationalWittNormalizedFraction
        (deningerRationalWittAtomPolynomial (deningerRationalWittPositiveAtoms x))
        (deningerRationalWittAtomPolynomial (deningerRationalWittNegativeAtoms x))
        (deningerRationalWittAtomPolynomial_coeff_zero (deningerRationalWittPositiveAtoms x))
        (deningerRationalWittAtomPolynomial_coeff_zero (deningerRationalWittNegativeAtoms x)) =
      Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive K x) := by
  conv_rhs => rw [deningerRationalWitt_eq_positiveAtoms_sub_negativeAtoms x]
  rw [map_sub]
  change deningerRationalWittNormalizedPolynomial _ _ * (deningerRationalWittNormalizedPolynomial _ _)⁻¹ =
    Additive.toMul
      (deningerRationalWittReducedMonoidAlgebraToAdditive K
        (deningerRationalWittAtomSum (deningerRationalWittPositiveAtoms x))) *
      (Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive K
          (deningerRationalWittAtomSum (deningerRationalWittNegativeAtoms x))))⁻¹
  rw [deningerRationalWittNormalizedPolynomial_atomPolynomial,
    deningerRationalWittNormalizedPolynomial_atomPolynomial,
    deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum_toMul,
    deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum_toMul]

theorem deningerPrimeLiteralRationalWitt_fixed_exists_base
    (p : Nat.Primes)
    (w : DeningerRationalWittRing (DeningerPrimeArithmeticClosure p))
    (hw : deningerPrimeLiteralRationalWittFrobenius p w = w) :
    ∃ w0 : DeningerRationalWittAdditive (ZMod (p : ℕ)),
      deningerRationalWittAdditiveMap
          (algebraMap (ZMod (p : ℕ)) (DeningerPrimeArithmeticClosure p)) w0 =
        Additive.toMul w.additiveVal := by
  let e := deningerPrimeRationalWittReducedMonoidAlgebraRingEquiv p
  let x : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ := e.symm w
  have hx : deningerPrimeIntegralRationalWittFrobenius p x = x := by
    have hw' := congrArg e.symm hw
    simpa [e, x, deningerPrimeLiteralRationalWittFrobenius,
      deningerPrimeLiteralRationalWittGaloisAction,
      deningerPrimeIntegralRationalWittFrobenius] using hw'
  let P := deningerRationalWittAtomPolynomial (deningerRationalWittPositiveAtoms x)
  let Q := deningerRationalWittAtomPolynomial (deningerRationalWittNegativeAtoms x)
  have hP : P.coeff 0 = 1 := by simp [P]
  have hQ : Q.coeff 0 = 1 := by simp [Q]
  obtain ⟨P0, hP0map⟩ :=
    deningerPrimePolynomialFrobeniusFixed_exists_base p P
      (deningerPrimeRationalWittPositiveAtomPolynomial_frobenius p x hx)
  obtain ⟨Q0, hQ0map⟩ :=
    deningerPrimePolynomialFrobeniusFixed_exists_base p Q
      (deningerPrimeRationalWittNegativeAtomPolynomial_frobenius p x hx)
  have hP0 : P0.coeff 0 = 1 := by
    apply (algebraMap (ZMod (p : ℕ))
      (DeningerPrimeArithmeticClosure p)).injective
    have hc := congrArg
      (fun R : Polynomial (DeningerPrimeArithmeticClosure p) => R.coeff 0)
      hP0map
    simpa [P] using hc
  have hQ0 : Q0.coeff 0 = 1 := by
    apply (algebraMap (ZMod (p : ℕ))
      (DeningerPrimeArithmeticClosure p)).injective
    have hc := congrArg
      (fun R : Polynomial (DeningerPrimeArithmeticClosure p) => R.coeff 0)
      hQ0map
    simpa [Q] using hc
  refine ⟨deningerRationalWittNormalizedFraction P0 Q0 hP0 hQ0, ?_⟩
  rw [deningerRationalWittNormalizedFraction_map]
  have hcomparison :
      Additive.toMul
          (deningerRationalWittReducedMonoidAlgebraToAdditive
            (DeningerPrimeArithmeticClosure p) x) =
        Additive.toMul w.additiveVal := by
    congr 1
    calc
      deningerRationalWittReducedMonoidAlgebraToAdditive
          (DeningerPrimeArithmeticClosure p) x =
          (e x).additiveVal :=
        (deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal x).symm
      _ = w.additiveVal := by simp [x]
  calc
    deningerRationalWittNormalizedFraction
        (P0.map (algebraMap (ZMod (p : ℕ))
          (DeningerPrimeArithmeticClosure p)))
        (Q0.map (algebraMap (ZMod (p : ℕ))
          (DeningerPrimeArithmeticClosure p))) _ _ =
        deningerRationalWittNormalizedFraction P Q hP hQ := by
      simp only [deningerRationalWittNormalizedFraction]
      rw [deningerRationalWittNormalizedPolynomial_congr hP0map,
        deningerRationalWittNormalizedPolynomial_congr hQ0map]
    _ = Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive
          (DeningerPrimeArithmeticClosure p) x) := by
      simpa [P, Q] using deningerRationalWittNormalizedFraction_eq_comparison x
    _ = Additive.toMul w.additiveVal := hcomparison

theorem deningerRationalWittComparison_natural
    {K L : Type*} [Field K] [Field L]
    (f : K ≃+* L) (x : MonoidAlgebra ℤ Kˣ) :
    deningerRationalWittReducedMonoidAlgebraToAdditive L
        ((MonoidAlgebra.domCongr ℤ ℤ
          (Units.mapEquiv f.toMulEquiv)) x) =
      Additive.ofMul
        (deningerRationalWittAdditiveMap f.toRingHom
          (Additive.toMul
            (deningerRationalWittReducedMonoidAlgebraToAdditive K x))) := by
  induction x using MonoidAlgebra.induction with
  | zero => simp
  | single_add a n x _ha _hn ih =>
      rw [map_add, map_add, map_add, ih]
      simp [deningerRationalWittReducedMonoidAlgebraToAdditive_single,
        deningerRationalWittAdditiveMap_teichmuller]

theorem deningerPrimeLiteralRationalWittGaloisAction_additiveVal
    (p : Nat.Primes) (g : DeningerPrimeArithmeticGalois p)
    (w : DeningerRationalWittRing (DeningerPrimeArithmeticClosure p)) :
    (deningerPrimeLiteralRationalWittGaloisAction p g w).additiveVal =
      Additive.ofMul
        (deningerRationalWittAdditiveMap g.toRingEquiv.toRingHom
          (Additive.toMul w.additiveVal)) := by
  let e := deningerPrimeRationalWittReducedMonoidAlgebraRingEquiv p
  let x : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ := e.symm w
  change (e (deningerPrimeIntegralRationalWittGaloisAction p g x)).additiveVal = _
  dsimp only [e]
  change (deningerRationalWittReducedMonoidAlgebraRingEquiv
    (DeningerPrimeArithmeticClosure p)
      (deningerPrimeIntegralRationalWittGaloisAction p g x)).additiveVal = _
  rw [deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal]
  have hn := deningerRationalWittComparison_natural g.toRingEquiv x
  change deningerRationalWittReducedMonoidAlgebraToAdditive
      (DeningerPrimeArithmeticClosure p)
      ((MonoidAlgebra.domCongr ℤ ℤ
        (Units.mapEquiv g.toRingEquiv.toMulEquiv)) x) = _
  calc
    deningerRationalWittReducedMonoidAlgebraToAdditive
        (DeningerPrimeArithmeticClosure p)
        ((MonoidAlgebra.domCongr ℤ ℤ
          (Units.mapEquiv g.toRingEquiv.toMulEquiv)) x) =
      Additive.ofMul
        (deningerRationalWittAdditiveMap g.toRingEquiv.toRingHom
          (Additive.toMul
            (deningerRationalWittReducedMonoidAlgebraToAdditive
              (DeningerPrimeArithmeticClosure p) x))) := hn
    _ = Additive.ofMul
        (deningerRationalWittAdditiveMap g.toRingEquiv.toRingHom
          (Additive.toMul w.additiveVal)) := by
      congr 3
      calc
        deningerRationalWittReducedMonoidAlgebraToAdditive
            (DeningerPrimeArithmeticClosure p) x = (e x).additiveVal :=
          (deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal x).symm
        _ = w.additiveVal := by simp [x]

noncomputable def deningerPrimeBaseRationalWittLift
    (p : Nat.Primes)
    (w0 : DeningerRationalWittAdditive (ZMod (p : ℕ))) :
    DeningerRationalWittRing (DeningerPrimeArithmeticClosure p) :=
  ⟨Additive.ofMul
    (deningerRationalWittAdditiveMap
      (algebraMap (ZMod (p : ℕ)) (DeningerPrimeArithmeticClosure p)) w0)⟩

theorem deningerPrimeBaseRationalWittLift_frobenius_fixed
    (p : Nat.Primes)
    (w0 : DeningerRationalWittAdditive (ZMod (p : ℕ))) :
    deningerPrimeLiteralRationalWittFrobenius p
        (deningerPrimeBaseRationalWittLift p w0) =
      deningerPrimeBaseRationalWittLift p w0 := by
  apply DeningerRationalWittRing.ext
  change (deningerPrimeLiteralRationalWittGaloisAction p
    (deningerPrimeArithmeticFrobenius p)
      (deningerPrimeBaseRationalWittLift p w0)).additiveVal = _
  rw [deningerPrimeLiteralRationalWittGaloisAction_additiveVal]
  change Additive.ofMul
      (deningerRationalWittAdditiveMap
        (deningerPrimeArithmeticFrobenius p).toRingEquiv.toRingHom
        (deningerRationalWittAdditiveMap
          (algebraMap (ZMod (p : ℕ))
            (DeningerPrimeArithmeticClosure p)) w0)) =
    Additive.ofMul
      (deningerRationalWittAdditiveMap
        (algebraMap (ZMod (p : ℕ))
          (DeningerPrimeArithmeticClosure p)) w0)
  congr 1
  rw [← MonoidHom.comp_apply, ← deningerRationalWittAdditiveMap_comp]
  congr 2
  ext a
  exact (deningerPrimeArithmeticFrobenius p).commutes a

theorem deningerPrimeLiteralRationalWitt_fixed_iff_exists_base
    (p : Nat.Primes)
    (w : DeningerRationalWittRing (DeningerPrimeArithmeticClosure p)) :
    deningerPrimeLiteralRationalWittFrobenius p w = w ↔
      ∃ w0 : DeningerRationalWittAdditive (ZMod (p : ℕ)),
        Additive.ofMul
            (deningerRationalWittAdditiveMap
              (algebraMap (ZMod (p : ℕ))
                (DeningerPrimeArithmeticClosure p)) w0) =
          w.additiveVal := by
  constructor
  · intro hw
    obtain ⟨w0, hw0⟩ :=
      deningerPrimeLiteralRationalWitt_fixed_exists_base p w hw
    refine ⟨w0, ?_⟩
    exact congrArg Additive.ofMul hw0
  · rintro ⟨w0, hw0⟩
    have heq : w = deningerPrimeBaseRationalWittLift p w0 := by
      apply DeningerRationalWittRing.ext
      exact hw0.symm
    rw [heq]
    exact deningerPrimeBaseRationalWittLift_frobenius_fixed p w0

end
end RHTower
