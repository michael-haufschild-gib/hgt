import GaloisForLFunctions.RHTower.DeningerDynSysWittAtomDescent
import GaloisForLFunctions.RHTower.DeningerDynSysOmegaAtomBridge

/-!
# `W_rat (κ₀)` inside `ℤ̲κ` is exactly `ℤ̲κ / κ₀`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), the lower row.

Transporting a rational Witt vector over the perfect closure to `ℤ̲κ` by `ω`, its atom datum is the
difference of the atom multisets of numerator and denominator.  The vector descends to `κ₀` exactly
when that datum lies in Deninger's subring `ℤ̲κ / κ₀`, i.e. when every coefficient is divisible by
the corresponding degree of inseparability.
-/

namespace RHTower

open Polynomial

variable {F L E : Type*} [Field F] [Field L] [Field E]
variable [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
variable [IsPurelyInseparable F L] [IsAlgClosed E] [PerfectField L]

omit [PerfectField L] in
/-- `ω` sends the atom datum of a normalized fraction to the corresponding rational Witt
vector. -/
theorem deningerOmega_fraction_map (P Q : Polynomial L) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1)
    (hmapP : (P.map (algebraMap L E)).coeff 0 = 1)
    (hmapQ : (Q.map (algebraMap L E)).coeff 0 = 1) :
    deningerOmegaAddHom E
        (deningerRationalWittAtomSum
            (deningerNormalizedPolynomialRootUnits (P.map (algebraMap L E)) hmapP)
          - deningerRationalWittAtomSum
            (deningerNormalizedPolynomialRootUnits (Q.map (algebraMap L E)) hmapQ))
      = deningerCanonicalRationalWittMap (algebraMap L E)
          (deningerCanonicalRationalWittNormalizedFraction P Q hP hQ) := by
  rw [map_sub, deningerOmega_atomSum_normalizedPolynomial,
    deningerOmega_atomSum_normalizedPolynomial,
    deningerCanonicalRationalWittMap_normalizedFraction,
    deningerFraction_eq_sub]

/-- **Deninger, Proposition 1.3 (`t26n`), the lower row.**  A rational Witt vector over the perfect
closure descends to `κ₀` exactly when its atom datum lies in `ℤ̲κ / κ₀`. -/
theorem deningerWittFraction_descends_iff (q : ℕ) [ExpChar F q] [Algebra.IsAlgebraic F E]
    [DecidableEq Eˣ] [DecidableEq (Polynomial L)]
    (P Q : Polynomial L) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1)
    (hmapP : (P.map (algebraMap L E)).coeff 0 = 1)
    (hmapQ : (Q.map (algebraMap L E)).coeff 0 = 1) :
    (∃ w₀ : DeningerCanonicalRationalWittRing F,
        deningerCanonicalRationalWittMap (algebraMap F L) w₀
          = deningerCanonicalRationalWittNormalizedFraction P Q hP hQ)
      ↔ deningerRationalWittAtomSum
            (deningerNormalizedPolynomialRootUnits (P.map (algebraMap L E)) hmapP)
          - deningerRationalWittAtomSum
            (deningerNormalizedPolynomialRootUnits (Q.map (algebraMap L E)) hmapQ)
        ∈ deningerInsepSubring F E q := by
  classical
  have hcoeff : ∀ u : Eˣ,
      (deningerRationalWittAtomSum
          (deningerNormalizedPolynomialRootUnits (P.map (algebraMap L E)) hmapP)
        - deningerRationalWittAtomSum
          (deningerNormalizedPolynomialRootUnits (Q.map (algebraMap L E)) hmapQ)).coeff u
      = (Multiset.count u (deningerNormalizedPolynomialRootUnits
            (P.map (algebraMap L E)) hmapP) : ℤ)
        - (Multiset.count u (deningerNormalizedPolynomialRootUnits
            (Q.map (algebraMap L E)) hmapQ) : ℤ) := by
    intro u
    show (deningerRationalWittAtomSum _).coeff u - (deningerRationalWittAtomSum _).coeff u = _
    rw [deningerAtomSum_coeff, deningerAtomSum_coeff]
  constructor
  · rintro ⟨w₀, hw₀⟩
    obtain ⟨P₀, Q₀, hP₀, hQ₀, hw₀eq⟩ :=
      deningerCanonicalRationalWitt_eq_normalizedFraction w₀
    subst hw₀eq
    rw [deningerCanonicalRationalWittMap_normalizedFraction] at hw₀
    -- both sides have the same atom datum, because `ω` is injective
    have hmapP₀ : ((P₀.map (algebraMap F L)).map (algebraMap L E)).coeff 0 = 1 := by
      rw [Polynomial.coeff_map, Polynomial.coeff_map, hP₀, map_one, map_one]
    have hmapQ₀ : ((Q₀.map (algebraMap F L)).map (algebraMap L E)).coeff 0 = 1 := by
      rw [Polynomial.coeff_map, Polynomial.coeff_map, hQ₀, map_one, map_one]
    have hP₀L : (P₀.map (algebraMap F L)).coeff 0 = 1 := by
      rw [Polynomial.coeff_map, hP₀, map_one]
    have hQ₀L : (Q₀.map (algebraMap F L)).coeff 0 = 1 := by
      rw [Polynomial.coeff_map, hQ₀, map_one]
    have hOmegaEq :
        deningerOmegaAddHom E
            (deningerRationalWittAtomSum
                (deningerNormalizedPolynomialRootUnits
                  ((P₀.map (algebraMap F L)).map (algebraMap L E)) hmapP₀)
              - deningerRationalWittAtomSum
                (deningerNormalizedPolynomialRootUnits
                  ((Q₀.map (algebraMap F L)).map (algebraMap L E)) hmapQ₀))
          = deningerOmegaAddHom E
            (deningerRationalWittAtomSum
                (deningerNormalizedPolynomialRootUnits (P.map (algebraMap L E)) hmapP)
              - deningerRationalWittAtomSum
                (deningerNormalizedPolynomialRootUnits (Q.map (algebraMap L E)) hmapQ)) := by
      rw [deningerOmega_fraction_map (E := E) (P₀.map (algebraMap F L))
          (Q₀.map (algebraMap F L)) hP₀L hQ₀L hmapP₀ hmapQ₀,
        deningerOmega_fraction_map (E := E) P Q hP hQ hmapP hmapQ]
      congr 1
    have hinj : Function.Injective (deningerOmegaAddHom E) :=
      (deningerOmegaRingEquiv E).injective
    have hEq := hinj hOmegaEq
    rw [← hEq]
    -- the descended data lie in the subring
    have hPmem : deningerRationalWittAtomSum
        (deningerNormalizedPolynomialRootUnits
          ((P₀.map (algebraMap F L)).map (algebraMap L E)) hmapP₀)
        ∈ deningerInsepSubring F E q := by
      have hcomp : (P₀.map (algebraMap F L)).map (algebraMap L E)
          = P₀.map (algebraMap F E) := by
        rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq F L E]
      have hmapP₀' : (P₀.map (algebraMap F E)).coeff 0 = 1 := by
        rw [Polynomial.coeff_map, hP₀, map_one]
      have hc := deningerRootUnits_congr
        (P := (P₀.map (algebraMap F L)).map (algebraMap L E))
        (Q := P₀.map (algebraMap F E)) hmapP₀ hmapP₀' hcomp
      rw [hc]
      exact deningerAtomSum_map_mem_insepSubring q P₀ hP₀ hmapP₀'
    have hQmem : deningerRationalWittAtomSum
        (deningerNormalizedPolynomialRootUnits
          ((Q₀.map (algebraMap F L)).map (algebraMap L E)) hmapQ₀)
        ∈ deningerInsepSubring F E q := by
      have hcomp : (Q₀.map (algebraMap F L)).map (algebraMap L E)
          = Q₀.map (algebraMap F E) := by
        rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq F L E]
      have hmapQ₀' : (Q₀.map (algebraMap F E)).coeff 0 = 1 := by
        rw [Polynomial.coeff_map, hQ₀, map_one]
      have hc := deningerRootUnits_congr
        (P := (Q₀.map (algebraMap F L)).map (algebraMap L E))
        (Q := Q₀.map (algebraMap F E)) hmapQ₀ hmapQ₀' hcomp
      rw [hc]
      exact deningerAtomSum_map_mem_insepSubring q Q₀ hQ₀ hmapQ₀'
    exact Subring.sub_mem _ hPmem hQmem
  · intro hmem
    refine deningerWittFraction_descends_of_atom_dvd (E := E) q P Q hP hQ hmapP hmapQ ?_
    intro u
    have := hmem u
    rwa [hcoeff u] at this

end RHTower
