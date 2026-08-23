import GaloisForLFunctions.RHTower.DeningerDynSysTiltAdditive
import GaloisForLFunctions.RHTower.DeningerDynSysPerfectionLocal
import GaloisForLFunctions.RHTower.DeningerDynSysAdicLocal

/-!
# Locality of the tilt of a completed `𝒪`-valued point

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.16
(`t1213n`), the locality clause.

A homomorphism of tilts `χ♭ : A♭ → 𝒪♭` of local rings is a local homomorphism exactly when the
pointed multiplicative map `χ = ♯ ∘ χ♭` it induces carries the maximal ideal of `A♭` into the
maximal ideal of `𝒪`.  Indeed an element of a perfection lies in the maximal ideal exactly when
its zeroth coefficient does, the zeroth coefficient of `χ♭ x` is the reduction of `χ x` modulo
`p`, and reduction modulo `p` reflects the maximal ideal because it is a surjection of local
rings.
-/

namespace RHTower

open Perfection

universe u

variable {p : ℕ} [Fact p.Prime]

/-- The quotient `R / p` of a local ring in which `p` is not a unit is again local. -/
instance deningerModP_isLocalRing {R : Type u} [CommRing R] [IsLocalRing R]
    [Fact (¬ IsUnit (p : R))] : IsLocalRing (ModP R p) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- Reduction modulo `p` reflects the maximal ideal of a local ring. -/
theorem deningerModP_mk_mem_maximalIdeal_iff {R : Type u} [CommRing R] [IsLocalRing R]
    [Fact (¬ IsUnit (p : R))] (a : R) :
    (Ideal.Quotient.mk (Ideal.span {(p : R)}) a : ModP R p)
        ∈ IsLocalRing.maximalIdeal (ModP R p) ↔ a ∈ IsLocalRing.maximalIdeal R := by
  rw [deningerMaximalIdeal_eq_comap (Ideal.Quotient.mk (Ideal.span {(p : R)}))
    Ideal.Quotient.mk_surjective]
  exact Iff.rfl

/-- The tilt of a local ring in which `p` is not a unit is again local. -/
instance deningerPreTilt_isLocalRing {R : Type u} [CommRing R] [IsLocalRing R]
    [Fact (¬ IsUnit (p : R))] : IsLocalRing (PreTilt R p) :=
  inferInstanceAs (IsLocalRing (Perfection (ModP R p) p))

/-- An element of the tilt lies in the maximal ideal exactly when its zeroth coefficient does. -/
theorem deningerPreTilt_mem_maximalIdeal_iff {R : Type u} [CommRing R] [IsLocalRing R]
    [Fact (¬ IsUnit (p : R))] (x : PreTilt R p) :
    x ∈ IsLocalRing.maximalIdeal (PreTilt R p)
      ↔ PreTilt.coeff 0 x ∈ IsLocalRing.maximalIdeal (ModP R p) :=
  deningerPerfection_mem_maximalIdeal_iff (R := ModP R p) x

variable {A O : Type u} [CommRing A] [CommRing O]
variable [Fact (¬ IsUnit (p : A))] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- **Deninger, Proposition 14.16 (`t1213n`), the locality clause.**  A homomorphism of tilts is
local as soon as the pointed multiplicative map it induces sends the maximal ideal of `A♭` into
the maximal ideal of `𝒪`. -/
theorem deningerTiltChar_isLocalHom [IsLocalRing A] [IsLocalRing O]
    (χflat : PreTilt A p →+* PreTilt O p)
    (h : ∀ f : PreTilt A p, f ∈ IsLocalRing.maximalIdeal (PreTilt A p) →
      deningerTiltChar χflat f ∈ IsLocalRing.maximalIdeal O) :
    IsLocalHom χflat := by
  refine ((IsLocalRing.local_hom_TFAE χflat).out 1 0).mp ?_
  rintro _ ⟨f, hf, rfl⟩
  rw [SetLike.mem_coe] at hf ⊢
  rw [deningerPreTilt_mem_maximalIdeal_iff] at hf ⊢
  have hval : PreTilt.coeff 0 (χflat f)
      = Ideal.Quotient.mk (Ideal.span {(p : O)}) (deningerTiltChar χflat f) :=
    (deningerTiltChar_reduction χflat f).symm
  rw [hval, deningerModP_mk_mem_maximalIdeal_iff]
  refine h f ?_
  rw [deningerPreTilt_mem_maximalIdeal_iff]
  exact hf

variable [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- **Deninger, Proposition 14.16 (`t1213n`), the locality clause on `lim_{()^p} A`.**  Through the
identification `lim_{()^p} A ≅ A♭` the criterion reads: the zeroth coefficient lies in the maximal
ideal of `A` only if the value lies in the maximal ideal of `𝒪`. -/
theorem deningerLimChar_isLocalHom [IsLocalRing A] [IsLocalRing O]
    (χflat : PreTilt A p →+* PreTilt O p)
    (h : ∀ z : Perfection A p, coeffMonoidHom A p 0 z ∈ IsLocalRing.maximalIdeal A →
      deningerLimChar χflat z ∈ IsLocalRing.maximalIdeal O) :
    IsLocalHom χflat := by
  have hsurj : ∀ g : PreTilt A p, ∃ z : Perfection A p, deningerTiltComparison z = g :=
    fun g => deningerTiltComparison_surjective (A := A) (p := p) g
  refine deningerTiltChar_isLocalHom χflat fun f hf => ?_
  obtain ⟨z, rfl⟩ := hsurj f
  have hz : coeffMonoidHom A p 0 z ∈ IsLocalRing.maximalIdeal A := by
    rw [deningerPreTilt_mem_maximalIdeal_iff] at hf
    have hc : PreTilt.coeff 0 (deningerTiltComparison z : PreTilt A p)
        = Ideal.Quotient.mk (Ideal.span {(p : A)}) (coeffMonoidHom A p 0 z) := rfl
    rw [hc, deningerModP_mk_mem_maximalIdeal_iff] at hf
    exact hf
  exact h z hz

end RHTower
