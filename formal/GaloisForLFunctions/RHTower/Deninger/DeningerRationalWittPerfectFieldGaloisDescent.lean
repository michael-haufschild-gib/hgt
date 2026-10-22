import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittBaseFieldDescent
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Perfect

/-!
# Perfect-field Galois descent for literal rational Witt vectors

This module proves the field case of Deninger's 2025 Theorem 1.2, equation (4).  For every perfect field
`K`, the absolute-Galois fixed points in the literal rational-Witt ring over
`AlgebraicClosure K` are exactly coefficient extensions of literal rational Witt vectors
over `K`.

The proof uses canonical positive/negative Teichmüller multiplicities.  Galois-stable atom
multisets yield invariant normalized numerator and denominator polynomials.  Infinite Galois
theory descends every coefficient to `K`, after which literal localized-polynomial
functoriality reconstructs the base rational Witt vector.  No descent axiom or fixed-field premise
is exposed in the theorem statement.
-/

namespace RHTower

noncomputable section

abbrev DeningerRationalWittAbsoluteGalois (K : Type*) [Field K] :=
  AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

noncomputable def deningerRationalWittIntegralGaloisAction
    (K : Type*) [Field K] (g : DeningerRationalWittAbsoluteGalois K) :
    MonoidAlgebra ℤ (AlgebraicClosure K)ˣ ≃+*
      MonoidAlgebra ℤ (AlgebraicClosure K)ˣ :=
  (MonoidAlgebra.domCongr ℤ ℤ
    (Units.mapEquiv g.toRingEquiv.toMulEquiv)).toRingEquiv

noncomputable def deningerRationalWittLiteralGaloisAction
    (K : Type*) [Field K] (g : DeningerRationalWittAbsoluteGalois K) :
    DeningerRationalWittRing (AlgebraicClosure K) ≃+*
      DeningerRationalWittRing (AlgebraicClosure K) :=
  ((deningerRationalWittReducedMonoidAlgebraRingEquiv
      (AlgebraicClosure K)).symm.trans
    (deningerRationalWittIntegralGaloisAction K g)).trans
      (deningerRationalWittReducedMonoidAlgebraRingEquiv
        (AlgebraicClosure K))

noncomputable def deningerRationalWittUnitGaloisEquiv
    (K : Type*) [Field K] (g : DeningerRationalWittAbsoluteGalois K) :
    (AlgebraicClosure K)ˣ ≃ (AlgebraicClosure K)ˣ :=
  (Units.mapEquiv g.toRingEquiv.toMulEquiv).toEquiv

theorem deningerRationalWitt_galoisFixed_exists_base
    (K : Type*) [Field K] [PerfectField K]
    (x : AlgebraicClosure K) (hx : ∀ g : DeningerRationalWittAbsoluteGalois K, g x = x) :
    ∃ y : K, algebraMap K (AlgebraicClosure K) y = x := by
  letI : IsGalois K (AlgebraicClosure K) :=
    isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hx

theorem deningerRationalWittPolynomial_galoisFixed_exists_base
    (K : Type*) [Field K] [PerfectField K]
    (P : Polynomial (AlgebraicClosure K))
    (hP : ∀ g : DeningerRationalWittAbsoluteGalois K, P.map g.toRingEquiv.toRingHom = P) :
    ∃ P0 : Polynomial K,
      P0.map (algebraMap K (AlgebraicClosure K)) = P := by
  have hlifts : P ∈ Polynomial.lifts
      (algebraMap K (AlgebraicClosure K)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    apply deningerRationalWitt_galoisFixed_exists_base K
    intro g
    have hc := congrArg
      (fun Q : Polynomial (AlgebraicClosure K) => Q.coeff n) (hP g)
    simpa using hc
  obtain ⟨P0, hmap, _⟩ := Polynomial.exists_support_eq_of_mem_lifts hlifts
  exact ⟨P0, hmap⟩

theorem deningerRationalWittIntegralGaloisAction_coeff
    (K : Type*) [Field K] (g : DeningerRationalWittAbsoluteGalois K)
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ)
    (hx : deningerRationalWittIntegralGaloisAction K g x = x)
    (a : (AlgebraicClosure K)ˣ) :
    x.coeff ((deningerRationalWittUnitGaloisEquiv K g).symm a) =
      x.coeff a := by
  have hc := congrArg
    (fun y : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ => y.coeff a) hx
  simpa [deningerRationalWittIntegralGaloisAction, deningerRationalWittUnitGaloisEquiv] using hc

theorem deningerRationalWittPositiveAtoms_galois
    (K : Type*) [Field K] (g : DeningerRationalWittAbsoluteGalois K)
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ)
    (hx : deningerRationalWittIntegralGaloisAction K g x = x) :
    (deningerRationalWittPositiveAtoms x).map
        (deningerRationalWittUnitGaloisEquiv K g) =
      deningerRationalWittPositiveAtoms x := by
  rw [deningerRationalWittPositiveAtoms, Finsupp.toMultiset_map,
    ← Finsupp.equivMapDomain_eq_mapDomain
      (deningerRationalWittUnitGaloisEquiv K g)]
  congr 1
  apply Finsupp.ext
  intro a
  simp only [Finsupp.equivMapDomain_apply,
    deningerRationalWittPositiveCoefficients, Finsupp.mapRange_apply]
  rw [deningerRationalWittIntegralGaloisAction_coeff K g x hx a]

theorem deningerRationalWittNegativeAtoms_galois
    (K : Type*) [Field K] (g : DeningerRationalWittAbsoluteGalois K)
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ)
    (hx : deningerRationalWittIntegralGaloisAction K g x = x) :
    (deningerRationalWittNegativeAtoms x).map
        (deningerRationalWittUnitGaloisEquiv K g) =
      deningerRationalWittNegativeAtoms x := by
  rw [deningerRationalWittNegativeAtoms, Finsupp.toMultiset_map,
    ← Finsupp.equivMapDomain_eq_mapDomain
      (deningerRationalWittUnitGaloisEquiv K g)]
  congr 1
  apply Finsupp.ext
  intro a
  simp only [Finsupp.equivMapDomain_apply,
    deningerRationalWittNegativeCoefficients, Finsupp.mapRange_apply]
  rw [deningerRationalWittIntegralGaloisAction_coeff K g x hx a]

theorem deningerRationalWittPositiveAtomPolynomial_galois
    (K : Type*) [Field K] (g : DeningerRationalWittAbsoluteGalois K)
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ)
    (hx : deningerRationalWittIntegralGaloisAction K g x = x) :
    (deningerRationalWittAtomPolynomial
      (deningerRationalWittPositiveAtoms x)).map
        g.toRingEquiv.toRingHom =
      deningerRationalWittAtomPolynomial
        (deningerRationalWittPositiveAtoms x) := by
  rw [deningerRationalWittAtomPolynomial_map]
  exact congrArg deningerRationalWittAtomPolynomial
    (deningerRationalWittPositiveAtoms_galois K g x hx)

theorem deningerRationalWittNegativeAtomPolynomial_galois
    (K : Type*) [Field K] (g : DeningerRationalWittAbsoluteGalois K)
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ)
    (hx : deningerRationalWittIntegralGaloisAction K g x = x) :
    (deningerRationalWittAtomPolynomial
      (deningerRationalWittNegativeAtoms x)).map
        g.toRingEquiv.toRingHom =
      deningerRationalWittAtomPolynomial
        (deningerRationalWittNegativeAtoms x) := by
  rw [deningerRationalWittAtomPolynomial_map]
  exact congrArg deningerRationalWittAtomPolynomial
    (deningerRationalWittNegativeAtoms_galois K g x hx)

theorem deningerRationalWittLiteralGaloisAction_additiveVal
    (K : Type*) [Field K] (g : DeningerRationalWittAbsoluteGalois K)
    (w : DeningerRationalWittRing (AlgebraicClosure K)) :
    (deningerRationalWittLiteralGaloisAction K g w).additiveVal =
      Additive.ofMul
        (deningerRationalWittAdditiveMap g.toRingEquiv.toRingHom
          (Additive.toMul w.additiveVal)) := by
  let e := deningerRationalWittReducedMonoidAlgebraRingEquiv
    (AlgebraicClosure K)
  let x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ := e.symm w
  change (e (deningerRationalWittIntegralGaloisAction K g x)).additiveVal = _
  dsimp only [e]
  rw [deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal]
  change deningerRationalWittReducedMonoidAlgebraToAdditive
      (AlgebraicClosure K)
      ((MonoidAlgebra.domCongr ℤ ℤ
        (Units.mapEquiv g.toRingEquiv.toMulEquiv)) x) = _
  calc
    deningerRationalWittReducedMonoidAlgebraToAdditive
        (AlgebraicClosure K)
        ((MonoidAlgebra.domCongr ℤ ℤ
          (Units.mapEquiv g.toRingEquiv.toMulEquiv)) x) =
      Additive.ofMul
        (deningerRationalWittAdditiveMap g.toRingEquiv.toRingHom
          (Additive.toMul
            (deningerRationalWittReducedMonoidAlgebraToAdditive
              (AlgebraicClosure K) x))) :=
      deningerRationalWittComparison_natural g.toRingEquiv x
    _ = Additive.ofMul
        (deningerRationalWittAdditiveMap g.toRingEquiv.toRingHom
          (Additive.toMul w.additiveVal)) := by
      congr 3
      calc
        deningerRationalWittReducedMonoidAlgebraToAdditive
            (AlgebraicClosure K) x = (e x).additiveVal :=
          (deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal x).symm
        _ = w.additiveVal := by simp [x]

theorem deningerRationalWittLiteral_galoisFixed_exists_base
    (K : Type*) [Field K] [PerfectField K]
    (w : DeningerRationalWittRing (AlgebraicClosure K))
    (hw : ∀ g : DeningerRationalWittAbsoluteGalois K, deningerRationalWittLiteralGaloisAction K g w = w) :
    ∃ w0 : DeningerRationalWittAdditive K,
      deningerRationalWittAdditiveMap
          (algebraMap K (AlgebraicClosure K)) w0 =
        Additive.toMul w.additiveVal := by
  let e := deningerRationalWittReducedMonoidAlgebraRingEquiv
    (AlgebraicClosure K)
  let x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ := e.symm w
  have hx : ∀ g : DeningerRationalWittAbsoluteGalois K, deningerRationalWittIntegralGaloisAction K g x = x := by
    intro g
    have hw' := congrArg e.symm (hw g)
    simpa [e, x, deningerRationalWittLiteralGaloisAction] using hw'
  let P := deningerRationalWittAtomPolynomial
    (deningerRationalWittPositiveAtoms x)
  let Q := deningerRationalWittAtomPolynomial
    (deningerRationalWittNegativeAtoms x)
  have hP : P.coeff 0 = 1 := by simp [P]
  have hQ : Q.coeff 0 = 1 := by simp [Q]
  obtain ⟨P0, hP0map⟩ :=
    deningerRationalWittPolynomial_galoisFixed_exists_base K P
      (fun g => deningerRationalWittPositiveAtomPolynomial_galois K g x (hx g))
  obtain ⟨Q0, hQ0map⟩ :=
    deningerRationalWittPolynomial_galoisFixed_exists_base K Q
      (fun g => deningerRationalWittNegativeAtomPolynomial_galois K g x (hx g))
  have hP0 : P0.coeff 0 = 1 := by
    apply (algebraMap K (AlgebraicClosure K)).injective
    have hc := congrArg
      (fun R : Polynomial (AlgebraicClosure K) => R.coeff 0) hP0map
    simpa [P] using hc
  have hQ0 : Q0.coeff 0 = 1 := by
    apply (algebraMap K (AlgebraicClosure K)).injective
    have hc := congrArg
      (fun R : Polynomial (AlgebraicClosure K) => R.coeff 0) hQ0map
    simpa [Q] using hc
  refine ⟨deningerRationalWittNormalizedFraction P0 Q0 hP0 hQ0, ?_⟩
  rw [deningerRationalWittNormalizedFraction_map]
  have hcomparison :
      Additive.toMul
          (deningerRationalWittReducedMonoidAlgebraToAdditive
            (AlgebraicClosure K) x) =
        Additive.toMul w.additiveVal := by
    congr 1
    calc
      deningerRationalWittReducedMonoidAlgebraToAdditive
          (AlgebraicClosure K) x = (e x).additiveVal :=
        (deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal x).symm
      _ = w.additiveVal := by simp [x]
  calc
    deningerRationalWittNormalizedFraction
        (P0.map (algebraMap K (AlgebraicClosure K)))
        (Q0.map (algebraMap K (AlgebraicClosure K))) _ _ =
        deningerRationalWittNormalizedFraction P Q hP hQ := by
      simp only [deningerRationalWittNormalizedFraction]
      rw [deningerRationalWittNormalizedPolynomial_congr hP0map,
        deningerRationalWittNormalizedPolynomial_congr hQ0map]
    _ = Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive
          (AlgebraicClosure K) x) := by
      simpa [P, Q] using deningerRationalWittNormalizedFraction_eq_comparison x
    _ = Additive.toMul w.additiveVal := hcomparison

noncomputable def deningerRationalWittPerfectBaseLift
    (K : Type*) [Field K] (w0 : DeningerRationalWittAdditive K) :
    DeningerRationalWittRing (AlgebraicClosure K) :=
  ⟨Additive.ofMul
    (deningerRationalWittAdditiveMap
      (algebraMap K (AlgebraicClosure K)) w0)⟩

theorem deningerRationalWittPerfectBaseLift_galoisFixed
    (K : Type*) [Field K] (w0 : DeningerRationalWittAdditive K)
    (g : DeningerRationalWittAbsoluteGalois K) :
    deningerRationalWittLiteralGaloisAction K g (deningerRationalWittPerfectBaseLift K w0) =
      deningerRationalWittPerfectBaseLift K w0 := by
  apply DeningerRationalWittRing.ext
  rw [deningerRationalWittLiteralGaloisAction_additiveVal]
  change Additive.ofMul
      (deningerRationalWittAdditiveMap g.toRingEquiv.toRingHom
        (deningerRationalWittAdditiveMap
          (algebraMap K (AlgebraicClosure K)) w0)) =
    Additive.ofMul
      (deningerRationalWittAdditiveMap
        (algebraMap K (AlgebraicClosure K)) w0)
  congr 1
  rw [← MonoidHom.comp_apply, ← deningerRationalWittAdditiveMap_comp]
  congr 2
  ext a
  exact g.commutes a

theorem deningerRationalWittLiteral_galoisFixed_iff_exists_base
    (K : Type*) [Field K] [PerfectField K]
    (w : DeningerRationalWittRing (AlgebraicClosure K)) :
    (∀ g : DeningerRationalWittAbsoluteGalois K, deningerRationalWittLiteralGaloisAction K g w = w) ↔
      ∃ w0 : DeningerRationalWittAdditive K,
        Additive.ofMul
            (deningerRationalWittAdditiveMap
              (algebraMap K (AlgebraicClosure K)) w0) =
          w.additiveVal := by
  constructor
  · intro hw
    obtain ⟨w0, hw0⟩ := deningerRationalWittLiteral_galoisFixed_exists_base K w hw
    exact ⟨w0, congrArg Additive.ofMul hw0⟩
  · rintro ⟨w0, hw0⟩ g
    have heq : w = deningerRationalWittPerfectBaseLift K w0 := by
      apply DeningerRationalWittRing.ext
      exact hw0.symm
    rw [heq]
    exact deningerRationalWittPerfectBaseLift_galoisFixed K w0 g

end
end RHTower
