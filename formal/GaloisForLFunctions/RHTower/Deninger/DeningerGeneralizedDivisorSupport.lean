import GaloisForLFunctions.RHTower.Deninger.DeningerPullbackStalk
import GaloisForLFunctions.RHTower.Deninger.DeningerSUnitEndpointPage

/-!
# The generalized divisor of a prime and the support of the Kummer residue

The divisor of a rational unit, as a set of points of the arithmetic curve, is the set of primes
where its valuation is nonzero; for a prime it is that prime's closed point.  A generalized-divisor
law — the identity `div [β] = pr⁻¹(div β)` — therefore identifies the generalized divisor of `[p]`
with the preimage of the closed point of `p`, which is exactly the support of the `p`-summand of the
pulled back Kummer sequence.

* `deningerDivisorSet`, `deningerDivisorSet_primeUnit` : the divisor of a rational unit as a set.
* `DeningerGeneralizedDivisorLaw` : the generalized-divisor identity as an interface.
* `deningerGeneralizedDivisor_eq_stalkSupport` : the generalized divisor of `[p]` is the support of
  the `p`-summand.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

/-- The divisor of a rational unit as a set of points of the arithmetic curve. -/
def deningerDivisorSet (u : ℚˣ) : Set deningerArithBase :=
  {z : deningerArithBase | ∃ p : Nat.Primes,
    z = deningerClosedPt p ∧ padicValRat ((p : ℕ)) ((u : ℚ)) ≠ 0}

/-- **The divisor of a prime is its closed point.** -/
theorem deningerDivisorSet_primeUnit (p : Nat.Primes) :
    deningerDivisorSet (deningerPrimeUnit p) = {deningerClosedPt p} := by
  ext z
  constructor
  · rintro ⟨q, rfl, hq⟩
    rw [deningerPadicValRat_primeUnit q p] at hq
    by_cases h : p = q
    · rw [h]
      rfl
    · exact absurd (if_neg h) hq
  · rintro rfl
    refine ⟨p, rfl, ?_⟩
    rw [deningerPadicValRat_primeUnit p p, if_pos rfl]
    exact one_ne_zero

/-- The support of a sheaf of abelian groups: the points where its stalk is nonzero. -/
def deningerStalkSupport {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X) : Set X :=
  {x : X | ¬ IsZero (TopCat.Presheaf.stalk F.1 x)}

theorem deningerZ_not_isZero : ¬ IsZero (AddCommGrpCat.of ℤ) := by
  intro h
  rw [IsZero.iff_id_eq_zero] at h
  have h1 : (1 : ℤ) = 0 := congrArg (fun w => (ConcreteCategory.hom w : ℤ → ℤ) 1) h
  exact one_ne_zero h1

/-- **The support of the pulled back `p`-summand is the preimage of the closed point of `p`.** -/
theorem deningerPullbackResidue_stalkSupport {X : TopCat.{0}} (a : X ⟶ deningerArithBase)
    (p : Nat.Primes) :
    deningerStalkSupport ((TopCat.Sheaf.pullback AddCommGrpCat.{0} a).obj
      (deningerResidueAddSheaf {p} ℤ)) = deningerPullbackSupport a p := by
  ext x
  constructor
  · intro hx
    by_contra hxs
    exact hx (deningerPullbackResidueStalk_isZero a {p} x (by
      intro q hq
      rw [Finset.mem_singleton] at hq
      rw [hq]
      exact hxs))
  · intro hx hzero
    refine deningerZ_not_isZero ?_
    exact IsZero.of_iso hzero
      (deningerPullbackResidueStalk_iso a {p} (Finset.mem_singleton_self p) x hx).symm

/-- **Deninger's generalized-divisor identity**, as an interface: the generalized divisor of a
rational unit is the preimage of its divisor on the arithmetic curve. -/
structure DeningerGeneralizedDivisorLaw {X : TopCat.{0}} (a : X ⟶ deningerArithBase) where
  /-- The generalized divisor. -/
  gdiv : ℚˣ → Set X
  /-- It is the preimage of the divisor on the base. -/
  pullback_law : ∀ u : ℚˣ, gdiv u = (ConcreteCategory.hom a) ⁻¹' (deningerDivisorSet u)

/-- **The generalized divisor of a prime is the preimage of its closed point.** -/
theorem DeningerGeneralizedDivisorLaw.gdiv_primeUnit {X : TopCat.{0}}
    {a : X ⟶ deningerArithBase} (law : DeningerGeneralizedDivisorLaw a) (p : Nat.Primes) :
    law.gdiv (deningerPrimeUnit p) = deningerPullbackSupport a p := by
  rw [law.pullback_law, deningerDivisorSet_primeUnit]
  rfl

/-- **The generalized divisor of `[p]` is the support of the `p`-summand of the pulled back Kummer
sequence.** -/
theorem DeningerGeneralizedDivisorLaw.gdiv_eq_stalkSupport {X : TopCat.{0}}
    {a : X ⟶ deningerArithBase} (law : DeningerGeneralizedDivisorLaw a) (p : Nat.Primes) :
    law.gdiv (deningerPrimeUnit p) =
      deningerStalkSupport ((TopCat.Sheaf.pullback AddCommGrpCat.{0} a).obj
        (deningerResidueAddSheaf {p} ℤ)) := by
  rw [law.gdiv_primeUnit p, deningerPullbackResidue_stalkSupport a p]

end RHTower
