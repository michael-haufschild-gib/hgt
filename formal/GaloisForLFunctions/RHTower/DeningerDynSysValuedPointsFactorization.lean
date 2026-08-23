import GaloisForLFunctions.RHTower.DeningerDynSysValuedPointsAffine
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The second factorization and the pair of points of an `𝒪`-valued point

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 13.5 (`t45`).

Condition a) of Corollary 13.5 gives the factorization of `Q` through `R / Q⁻¹(0)`; condition b)
gives the factorization of `Q mod 𝔪` through `R / Q⁻¹(𝔪)`, which is what is proved here.  The two
primes satisfy `Q⁻¹(0) ⊆ Q⁻¹(𝔪)`, so the second point of `Spec R` is a specialization of the
first — this is the relation `y ∈ closure {x}` in Deninger's triples.
-/

namespace RHTower

open IsLocalRing

variable {R O : Type*} [CommRing R] [CommRing O]

/-- **Deninger, Corollary 13.5 (`t45`): the factorization of b).**  A pointed multiplicative map
satisfying b') induces, after reduction modulo the maximal ideal, a pointed multiplicative map on
the quotient by `Q⁻¹(𝔪)`. -/
noncomputable def deningerMaxQuotientLift [IsLocalRing O] (Q : R →*₀ O)
    (hb : DeningerAdditiveModMax Q) :
    (R ⧸ deningerMaxIdeal Q hb) →*₀ ResidueField O where
  toFun := Quotient.lift (fun f => residue O (Q f)) (by
    intro a b hab
    have h : Q (a - b) ∈ maximalIdeal O := (Submodule.quotientRel_def _).1 hab
    have h2 : Q a - Q b ∈ maximalIdeal O := (deningerAdditiveModMax_iff Q).1 hb a b h
    exact Ideal.Quotient.eq.2 h2)
  map_zero' := by
    show residue O (Q 0) = 0
    rw [map_zero, map_zero]
  map_one' := by
    show residue O (Q 1) = 1
    rw [map_one, map_one]
  map_mul' := by
    intro x y
    refine Quotient.inductionOn₂ x y fun a b => ?_
    show residue O (Q (a * b)) = residue O (Q a) * residue O (Q b)
    rw [map_mul, map_mul]

@[simp] theorem deningerMaxQuotientLift_mk [IsLocalRing O] (Q : R →*₀ O)
    (hb : DeningerAdditiveModMax Q) (f : R) :
    deningerMaxQuotientLift Q hb (Ideal.Quotient.mk _ f) = residue O (Q f) := rfl

/-- The point of `Spec R` cut out by the zero set of `Q`. -/
def deningerZeroPoint [IsDomain O] (Q : R →*₀ O) (ha : DeningerAdditiveOnZeros Q) :
    PrimeSpectrum R :=
  ⟨deningerZeroIdeal Q ha, deningerZeroIdeal_isPrime Q ha⟩

/-- The point of `Spec R` cut out by the preimage of the maximal ideal. -/
def deningerMaxPoint [IsLocalRing O] (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q) :
    PrimeSpectrum R :=
  ⟨deningerMaxIdeal Q hb, deningerMaxIdeal_isPrime Q hb⟩

/-- **Deninger, Corollary 13.5 (`t45`), the pair of points.**  The point cut out by `Q⁻¹(𝔪)` lies
in the closure of the point cut out by `Q⁻¹(0)`, which is Deninger's condition `y ∈ closure {x}`. -/
theorem deningerMaxPoint_mem_closure [IsDomain O] [IsLocalRing O] (Q : R →*₀ O)
    (ha : DeningerAdditiveOnZeros Q) (hb : DeningerAdditiveModMax Q) :
    deningerMaxPoint Q hb ∈ closure ({deningerZeroPoint Q ha} : Set (PrimeSpectrum R)) := by
  rw [PrimeSpectrum.closure_singleton]
  intro f hf
  exact deningerZeroIdeal_le_maxIdeal Q ha hb hf

/-- **Deninger, Corollary 13.5 (`t45`), the pair of points.**  Equivalently, the first point
specialises to the second. -/
theorem deningerZeroPoint_specializes [IsDomain O] [IsLocalRing O] (Q : R →*₀ O)
    (ha : DeningerAdditiveOnZeros Q) (hb : DeningerAdditiveModMax Q) :
    deningerZeroPoint Q ha ⤳ deningerMaxPoint Q hb :=
  (PrimeSpectrum.le_iff_specializes _ _).1 (deningerZeroIdeal_le_maxIdeal Q ha hb)

end RHTower
