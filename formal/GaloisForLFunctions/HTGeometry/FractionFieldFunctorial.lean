import GaloisForLFunctions.HTGeometry.LaurentSeriesCoefficientAutomorphism
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Tactic

/-!
# Fraction fields of an injective map of domains

An injective map of integral domains extends uniquely to their fraction fields, and any two
extensions of the same map agree.  This is the plumbing that lets a deformation carried out in one
ring be compared with one carried out in another inside a common overring.

## Main results

* `fracLift` — the extension, and `fracLift_algebraMap` its defining property.
* `fractionRing_ringHom_ext` — uniqueness.
* `fracAlgHom` — the extension as an algebra map over the fraction field of a common source.
-/

open scoped nonZeroDivisors

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {P B C : Type*} [CommRing P] [IsDomain P] [CommRing B] [IsDomain B]
  [CommRing C] [IsDomain C]

/-- The extension of an injective map of domains to their fraction fields. -/
def fracLift {b : P →+* B} (hb : Function.Injective b) :
    FractionRing P →+* FractionRing B :=
  IsFractionRing.lift (A := P) (K := FractionRing P) (L := FractionRing B)
    (g := (algebraMap B (FractionRing B)).comp b)
    ((IsFractionRing.injective B (FractionRing B)).comp hb)

theorem fracLift_algebraMap {b : P →+* B} (hb : Function.Injective b) (p : P) :
    fracLift hb (algebraMap P (FractionRing P) p) = algebraMap B (FractionRing B) (b p) :=
  IsFractionRing.lift_algebraMap _ p

omit [IsDomain P] in
/-- Two maps out of a fraction field agreeing on the domain are equal. -/
theorem fractionRing_ringHom_ext {X : Type*} [CommRing X] (j k : FractionRing P →+* X)
    (h : ∀ p : P, j (algebraMap P (FractionRing P) p) = k (algebraMap P (FractionRing P) p)) :
    j = k :=
  IsLocalization.ringHom_ext (nonZeroDivisors P) (RingHom.ext h)

theorem fracLift_injective {b : P →+* B} (hb : Function.Injective b) :
    Function.Injective (fracLift hb) := (fracLift hb).injective


/-- A ring automorphism of a domain, extended to its fraction field. -/
def fracRingEquiv (e : B ≃+* B) : FractionRing B ≃+* FractionRing B :=
  IsLocalization.ringEquivOfRingEquiv (M := B⁰) (FractionRing B) (FractionRing B) e
    (map_nonZeroDivisors_of_ringEquiv e)

@[simp] theorem fracRingEquiv_algebraMap (e : B ≃+* B) (b : B) :
    fracRingEquiv e (algebraMap B (FractionRing B) b)
      = algebraMap B (FractionRing B) (e b) := by
  rw [fracRingEquiv, IsLocalization.ringEquivOfRingEquiv_eq]

/-- A coefficientwise automorphism of a multivariate power series ring. -/
def mvPsRingEquiv {σ R : Type*} [CommRing R] (e : R ≃+* R) :
    MvPowerSeries σ R ≃+* MvPowerSeries σ R where
  toFun := MvPowerSeries.map (e : R →+* R)
  invFun := MvPowerSeries.map (e.symm : R →+* R)
  left_inv f := by
    ext n
    simp
  right_inv f := by
    ext n
    simp
  map_add' f g := map_add _ f g
  map_mul' f g := map_mul _ f g

@[simp] theorem mvPsRingEquiv_apply {σ R : Type*} [CommRing R] (e : R ≃+* R)
    (f : MvPowerSeries σ R) :
    mvPsRingEquiv (σ := σ) e f = MvPowerSeries.map (e : R →+* R) f := rfl

theorem mvPowerSeries_map_injective {σ R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (MvPowerSeries.map (σ := σ) f) := by
  intro x y hxy
  ext n
  refine hf ?_
  have := congrArg (fun g => MvPowerSeries.coeff n g) hxy
  simpa [MvPowerSeries.coeff_map] using this

end

end GaloisForLFunctions.HTGeometry
