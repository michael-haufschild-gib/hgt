import GaloisForLFunctions.HTGeometry.AffineExponentialSymmetricProductSource
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Integral finite-type principal-open localizations

This file proves that inverting one element preserves finite type by an explicit surjective
polynomial presentation.  It also packages domain preservation for a nonzero denominator and the
Kähler fact that a denominator-torsion differential vanishes on the corresponding principal open.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- A principal localization of a domain at a nonzero element remains a domain. -/
theorem localizationAway_isDomain_of_ne_zero
    {R : Type u} [CommRing R] [IsDomain R] {s : R} (hs : s ≠ 0) :
    IsDomain (Localization.Away s) := by
  exact IsLocalization.isDomain_of_le_nonZeroDivisors
    (Localization.Away s)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hs)

/-- Evaluate a polynomial at the distinguished inverse in a principal localization. -/
def awayPolynomialEvalAlgHom
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (s : R) : Polynomial R →ₐ[k] Localization.Away s :=
  (Polynomial.aeval (IsLocalization.Away.invSelf s : Localization.Away s)).restrictScalars k

/-- Original-ring elements together with the distinguished inverse generate the localization. -/
theorem awayPolynomialEvalAlgHom_surjective
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (s : R) : Function.Surjective (awayPolynomialEvalAlgHom (k := k) s) := by
  intro z
  obtain ⟨n, a, hza⟩ := IsLocalization.Away.surj s z
  refine ⟨Polynomial.C a * Polynomial.X ^ n, ?_⟩
  rw [awayPolynomialEvalAlgHom, AlgHom.restrictScalars_apply,
    map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  rw [← hza, mul_assoc]
  rw [← mul_pow, IsLocalization.Away.mul_invSelf]
  simp

/-- Inverting one element preserves finite type over the base ring. -/
theorem localizationAway_finiteType
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (s : R) :
    Algebra.FiniteType k (Localization.Away s) := by
  letI : Algebra.FiniteType k (Polynomial R) :=
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType k R)
      (inferInstance : Algebra.FiniteType R (Polynomial R))
  exact Algebra.FiniteType.of_surjective (awayPolynomialEvalAlgHom (k := k) s)
    (awayPolynomialEvalAlgHom_surjective (k := k) s)

/-- Canonical principal-localization map as an algebra homomorphism over a smaller base. -/
def localizationAwayAlgHom
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (s : R) : R →ₐ[k] Localization.Away s :=
  (Algebra.ofId R (Localization.Away s)).restrictScalars k

/-- A differential killed by the inverted denominator vanishes on the principal open. -/
theorem algHomKaehlerMap_localizationAway_eq_zero_of_smul_eq_zero
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (s : R) (w : Ω[R⁄k]) (h : s • w = 0) :
    algHomKaehlerMap (localizationAwayAlgHom (k := k) s) w = 0 := by
  have hmap := congrArg
    (algHomKaehlerMap (localizationAwayAlgHom (k := k) s)) h
  rw [map_zero, algHomKaehlerMap_smul] at hmap
  exact (IsLocalization.Away.algebraMap_isUnit s).smul_eq_zero.mp hmap

end

end GaloisForLFunctions.HTGeometry
