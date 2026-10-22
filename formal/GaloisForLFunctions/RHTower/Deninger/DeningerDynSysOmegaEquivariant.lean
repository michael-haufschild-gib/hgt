import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysInsepSubringDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysPerfectClosureFixed
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# `ω` is equivariant, and the image of `W_rat (κ₀)` in `ℤ̲κ` is `(ℤ̲κ / κ₀)^H`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`).

The comparison `ω : ℤ̲κ ≅ W_rat (κ)` intertwines the action of a ring endomorphism of `κ` on the
monoid algebra — relabelling the atoms — with its action on rational Witt vectors, because it does
so on Teichmüller generators.  Combining this with the two rows already proved, a class in `ℤ̲κ`
comes from `W_rat (κ₀)` exactly when it is `H`-invariant and lies in `ℤ̲κ / κ₀`.
-/

namespace RHTower

noncomputable section

open MonoidAlgebra

/-- The ring homomorphism of integral monoid algebras induced by a monoid homomorphism. -/
def deningerMonoidAlgebraMap {G H : Type*} [CommMonoid G] [CommMonoid H] (φ : G →* H) :
    MonoidAlgebra ℤ G →+* MonoidAlgebra ℤ H :=
  liftNCRingHom (Int.castRingHom (MonoidAlgebra ℤ H)) ((MonoidAlgebra.of ℤ H).comp φ)
    (fun _ _ => Commute.all _ _)

@[simp] theorem deningerMonoidAlgebraMap_single {G H : Type*} [CommMonoid G] [CommMonoid H]
    (φ : G →* H) (g : G) (n : ℤ) :
    deningerMonoidAlgebraMap φ (MonoidAlgebra.single g n)
      = MonoidAlgebra.single (φ g) n := by
  rw [deningerMonoidAlgebraMap, liftNCRingHom_single]
  show (MonoidAlgebra.single (1 : H) n) * (MonoidAlgebra.single (φ g) (1 : ℤ)) = _
  rw [MonoidAlgebra.single_mul_single, one_mul, mul_one]

variable {E : Type*} [Field E] [IsAlgClosed E]

omit [IsAlgClosed E] in
/-- **Deninger, Proposition 1.3 (`t26n`).**  `ω` intertwines relabelling of atoms with the induced
map of rational Witt rings. -/
theorem deningerOmega_equivariant (f : E →+* E) (ξ : MonoidAlgebra ℤ Eˣ) :
    deningerCanonicalRationalWittMap f (deningerOmegaAddHom E ξ)
      = deningerOmegaAddHom E (deningerMonoidAlgebraMap (Units.map (f : E →* E)) ξ) := by
  have h : ((deningerCanonicalRationalWittMap f : DeningerCanonicalRationalWittRing E →+*
        DeningerCanonicalRationalWittRing E) : DeningerCanonicalRationalWittRing E →+
        DeningerCanonicalRationalWittRing E).comp (deningerOmegaAddHom E)
      = (deningerOmegaAddHom E).comp
        ((deningerMonoidAlgebraMap (Units.map (f : E →* E)) :
          MonoidAlgebra ℤ Eˣ →+* MonoidAlgebra ℤ Eˣ) :
          MonoidAlgebra ℤ Eˣ →+ MonoidAlgebra ℤ Eˣ) := by
    refine MonoidAlgebra.addMonoidHom_ext ?_
    intro a n
    show deningerCanonicalRationalWittMap f (deningerOmegaAddHom E (MonoidAlgebra.single a n))
      = deningerOmegaAddHom E (deningerMonoidAlgebraMap (Units.map (f : E →* E))
        (MonoidAlgebra.single a n))
    rw [deningerOmegaAddHom_single, deningerMonoidAlgebraMap_single, deningerOmegaAddHom_single,
      map_zsmul, deningerCanonicalRationalWittMap_teichmuller]
    rfl
  exact congrArg (fun F : MonoidAlgebra ℤ Eˣ →+ DeningerCanonicalRationalWittRing E => F ξ) h

end

end RHTower

namespace RHTower

noncomputable section

open MonoidAlgebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [IsAlgClosure F E]

open scoped DeningerWittRing in
/-- **Deninger, Proposition 1.3 (`t26n`), the lower row in the form `(ℤ̲κ / κ₀)^H ≅ W_rat (κ₀)`.**
A class in `ℤ̲κ` comes from `W_rat (κ₀)` exactly when it is `H`-invariant and lies in the subring
`ℤ̲κ / κ₀` of combinations whose coefficients are divisible by the degrees of inseparability. -/
theorem deningerOmega_mem_image_iff (q : ℕ) [ExpChar F q] [DecidableEq Eˣ]
    [DecidableEq (Polynomial (perfectClosure F E))] (ξ : MonoidAlgebra ℤ Eˣ) :
    (∃ w₀ : DeningerCanonicalRationalWittRing F,
        deningerCanonicalRationalWittMap (algebraMap F E) w₀ = deningerOmegaAddHom E ξ)
      ↔ ((∀ σ : E ≃ₐ[F] E,
            deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E)) ξ = ξ)
          ∧ ξ ∈ deningerInsepSubring F E q) := by
  classical
  haveI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F E := IsAlgClosure.isAlgebraic
  set L := perfectClosure F E with hL
  have hinj : Function.Injective (deningerOmegaAddHom E) := (deningerOmegaRingEquiv E).injective
  constructor
  · rintro ⟨w₀, hw₀⟩
    constructor
    · intro σ
      have hcomm : ((σ : E →+* E).comp (algebraMap F E)) = algebraMap F E :=
        RingHom.ext fun a => σ.commutes a
      refine hinj ?_
      rw [← deningerOmega_equivariant, ← hw₀, ← deningerCanonicalRationalWittMap_comp, hcomm]
    · obtain ⟨P₀, Q₀, hP₀, hQ₀, hw₀eq⟩ :=
        deningerCanonicalRationalWitt_eq_normalizedFraction w₀
      subst hw₀eq
      rw [deningerCanonicalRationalWittMap_normalizedFraction] at hw₀
      have hmapP₀ : (P₀.map (algebraMap F E)).coeff 0 = 1 := by
        rw [Polynomial.coeff_map, hP₀, map_one]
      have hmapQ₀ : (Q₀.map (algebraMap F E)).coeff 0 = 1 := by
        rw [Polynomial.coeff_map, hQ₀, map_one]
      have hatom : deningerRationalWittAtomSum
            (deningerNormalizedPolynomialRootUnits (P₀.map (algebraMap F E)) hmapP₀)
          - deningerRationalWittAtomSum
            (deningerNormalizedPolynomialRootUnits (Q₀.map (algebraMap F E)) hmapQ₀) = ξ := by
        refine hinj ?_
        rw [map_sub, deningerOmega_atomSum_normalizedPolynomial,
          deningerOmega_atomSum_normalizedPolynomial, ← deningerFraction_eq_sub, hw₀]
      rw [← hatom]
      exact Subring.sub_mem _
        (deningerAtomSum_map_mem_insepSubring q P₀ hP₀ hmapP₀)
        (deningerAtomSum_map_mem_insepSubring q Q₀ hQ₀ hmapQ₀)
  · rintro ⟨hinv, hmem⟩
    -- the class is `H`-invariant, so it comes from the perfect closure
    have hfix : ∀ σ : E ≃ₐ[F] E, σ • deningerOmegaAddHom E ξ = deningerOmegaAddHom E ξ := by
      intro σ
      show deningerCanonicalRationalWittMap
        (MulSemiringAction.toRingHom (E ≃ₐ[F] E) E σ) (deningerOmegaAddHom E ξ) = _
      rw [deningerOmega_equivariant]
      exact congrArg (deningerOmegaAddHom E) (hinv σ)
    obtain ⟨w₁, hw₁⟩ :=
      deningerWittRing_fixed_eq_perfectClosure F E (deningerOmegaAddHom E ξ) hfix
    obtain ⟨P, Q, hP, hQ, hw₁eq⟩ := deningerCanonicalRationalWitt_eq_normalizedFraction w₁
    subst hw₁eq
    have hmapP : (P.map (algebraMap L E)).coeff 0 = 1 := by
      rw [Polynomial.coeff_map, hP, map_one]
    have hmapQ : (Q.map (algebraMap L E)).coeff 0 = 1 := by
      rw [Polynomial.coeff_map, hQ, map_one]
    have hatom : deningerRationalWittAtomSum
          (deningerNormalizedPolynomialRootUnits (P.map (algebraMap L E)) hmapP)
        - deningerRationalWittAtomSum
          (deningerNormalizedPolynomialRootUnits (Q.map (algebraMap L E)) hmapQ) = ξ := by
      refine hinj ?_
      rw [deningerOmega_fraction_map (E := E) P Q hP hQ hmapP hmapQ, hw₁]
    obtain ⟨w₀, hw₀⟩ :=
      (deningerWittFraction_descends_iff (F := F) (L := L) (E := E) q P Q hP hQ hmapP hmapQ).2
        (by rw [hatom]; exact hmem)
    refine ⟨w₀, ?_⟩
    have hcomp : deningerCanonicalRationalWittMap (algebraMap F E) w₀
        = deningerCanonicalRationalWittMap (algebraMap L E)
          (deningerCanonicalRationalWittMap (algebraMap F L) w₀) := by
      rw [← deningerCanonicalRationalWittMap_comp, ← IsScalarTower.algebraMap_eq F L E]
    rw [hcomp, hw₀, hw₁]

end

end RHTower
