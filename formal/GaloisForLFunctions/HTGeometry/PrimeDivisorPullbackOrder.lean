import GaloisForLFunctions.HTGeometry.PrimeDivisorOrder
import GaloisForLFunctions.HTGeometry.LocalRamificationOrderLaw

/-!
# Pullback of orders along prime divisors

A ring homomorphism carrying one prime divisor to another induces a homomorphism of the local
rings there, and both local rings are discrete valuation rings on a normal Noetherian base.  The
ramification index of that induced homomorphism therefore scales the order of every element:

`ord (pullback of a) at P = e * ord a at Q`,

where `Q` is the prime divisor below `P`.  This is the ring-level form of the statement that the
order of vanishing of a pullback along a prime divisor is the ramification index times the order
downstairs, which mathlib does not provide in any form.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {A B : Type*}
variable [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]

omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [IsDomain B] [IsNoetherianRing B]
  [IsIntegrallyClosed B] in
/-- A homomorphism carrying `P` back to `Q` carries the complement of `Q` into the complement of
`P`, so it induces a map of local rings. -/
theorem primeCompl_le_comap (φ : A →+* B) (P : PrimeDivisor B) (Q : PrimeDivisor A)
    (hQ : Q.1 = Ideal.comap φ P.1) :
    Q.1.primeCompl ≤ (P.1.primeCompl).comap φ := by
  intro x hx
  have hx' : x ∉ Q.1 := hx
  refine Submonoid.mem_comap.mpr ?_
  show φ x ∉ P.1
  intro hmem
  apply hx'
  rw [hQ]
  exact Ideal.mem_comap.mpr hmem

/-- The induced homomorphism of local rings at prime divisors. -/
noncomputable def localMapAt (φ : A →+* B) (P : PrimeDivisor B) (Q : PrimeDivisor A)
    (hQ : Q.1 = Ideal.comap φ P.1) :
    Localization.AtPrime Q.1 →+* Localization.AtPrime P.1 :=
  IsLocalization.map _ φ (primeCompl_le_comap φ P Q hQ)

omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [IsDomain B] [IsNoetherianRing B]
  [IsIntegrallyClosed B] in
@[simp] theorem localMapAt_algebraMap (φ : A →+* B) (P : PrimeDivisor B) (Q : PrimeDivisor A)
    (hQ : Q.1 = Ideal.comap φ P.1) (a : A) :
    localMapAt φ P Q hQ (algebraMap A (Localization.AtPrime Q.1) a) =
      algebraMap B (Localization.AtPrime P.1) (φ a) :=
  IsLocalization.map_eq _ a

omit [IsNoetherianRing A] [IsIntegrallyClosed A] in
theorem algebraMap_localization_ne_zero (Q : PrimeDivisor A) {a : A} (ha : a ≠ 0) :
    algebraMap A (Localization.AtPrime Q.1) a ≠ 0 := by
  intro h
  refine ha ?_
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime Q.1)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors Q.1)
  exact hinj (by rw [h, map_zero])

/-- **The order of a pullback scales by the ramification index at a prime divisor.** -/
theorem orderAt_map_eq_mul_ramification (φ : A →+* B) (P : PrimeDivisor B) (Q : PrimeDivisor A)
    (hQ : Q.1 = Ideal.comap φ P.1)
    {π : Localization.AtPrime Q.1} (hπ : Irreducible π) (e : ℕ)
    (he : addVal (Localization.AtPrime P.1) (localMapAt φ P Q hQ π) = (e : ℕ∞))
    (a : A) (ha : a ≠ 0) :
    orderAt P (φ a) = (e : ℕ∞) * orderAt Q a := by
  have h := addVal_map_eq_mul_ramification (localMapAt φ P Q hQ) hπ e he
    (algebraMap A (Localization.AtPrime Q.1) a) (algebraMap_localization_ne_zero Q ha)
  rw [localMapAt_algebraMap] at h
  exact h

end GaloisForLFunctions.HTGeometry
