import GaloisForLFunctions.RHTower.DeningerQ8ActualGroupRepresentation
import GaloisForLFunctions.RHTower.ArtinNumberFieldEulerProductAnalytic

/-!
# Q8 Artin representations on actual number-field Galois groups

The standard complex symplectic representation of `QuaternionGroup 2` becomes
a literal Artin representation as soon as an actual number-field Galois group
is identified with `Q₈`.  This module makes that pullback and its finite-place
Euler product explicit.  In particular, it does not posit an analytic
continuation, a global epsilon factor, or an example of a `Q₈` extension.

Those are the still-separate arithmetic inputs in Deninger's no-go theorem.
-/

open scoped NumberField

noncomputable section

namespace RHTower

open GaloisForLFunctions

section

variable {G : Type} [Group G]

/-- The literal two-dimensional symplectic Artin representation obtained by
pulling the standard `Q₈` representation back along a Galois-group
identification. -/
def deningerQ8ArtinRepresentation (e : G ≃* QuaternionGroup 2) :
    Representation ℂ G Q8Carrier :=
  deningerQ8Representation.comp e.toMonoidHom

/-- Pointwise description of the pulled-back Artin action. -/
theorem deningerQ8ArtinRepresentation_apply
    (e : G ≃* QuaternionGroup 2) (g : G) (v : Q8Carrier) :
    deningerQ8ArtinRepresentation e g v = deningerQ8Representation (e g) v :=
  rfl

/-- The pulled-back Artin representation preserves Deninger's nondegenerate
alternating form. -/
theorem deningerQ8ArtinRepresentation_preserves_symplectic
    (e : G ≃* QuaternionGroup 2) (g : G) (p q : Q8Carrier) :
    deningerQ8TransitionSymplectic (deningerQ8ArtinRepresentation e g p)
      (deningerQ8ArtinRepresentation e g q) = deningerQ8TransitionSymplectic p q := by
  exact deningerQ8Representation_preserves_symplectic (e g) p q

/-- The distinguished central involution has scalar action `-1` in every
`Q₈` Artin realization. -/
theorem deningerQ8ArtinRepresentation_central_apply
    (e : G ≃* QuaternionGroup 2) (g : G)
    (hg : e g = QuaternionGroup.a 2) (v : Q8Carrier) :
    deningerQ8ArtinRepresentation e g v = -v := by
  rw [deningerQ8ArtinRepresentation_apply, hg]
  exact deningerQ8Representation_central_apply v

/-- The Artin carrier has complex dimension two. -/
theorem deningerQ8ArtinRepresentation_finrank :
    Module.finrank ℂ Q8Carrier = 2 := by
  change Module.finrank ℂ (ℂ × ℂ) = 2
  rw [Module.finrank_prod]
  norm_num

end

section

variable {K L G : Type}
variable [Field K] [Field L] [Algebra K L]
variable [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- Any field Galois extension whose group is `Q₈` has degree eight.  This is
the field-theoretic part of a `Q₈` realization; it does not produce such an
extension. -/
theorem deningerQ8Galois_finrank_eq_eight (e : G ≃* QuaternionGroup 2) :
    Module.finrank K L = 8 := by
  letI : Fintype G := Fintype.ofFinite G
  calc
    Module.finrank K L = Nat.card G := (IsGaloisGroup.card_eq_finrank G K L).symm
    _ = Fintype.card G := Nat.card_eq_fintype_card
    _ = Fintype.card (QuaternionGroup 2) := Fintype.card_congr e.toEquiv
    _ = 8 := by
      rw [QuaternionGroup.card]

end

/-- The canonical finite-place Euler product of the pulled-back `Q₈` Artin
representation. -/
noncomputable def deningerQ8ArtinEulerProduct
    (K L G : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
    (e : G ≃* QuaternionGroup 2) : ℂ → ℂ :=
  numberFieldFinitePlaceArtinEulerReciprocalProduct
    (K := K) (L := L) (deningerQ8ArtinRepresentation e)

section

variable {K L G : Type}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- The actual finite-place `Q₈` Artin Euler product is holomorphic in its
absolute-convergence half-plane.  No continuation to the central point is
claimed. -/
theorem differentiableOn_deningerQ8ArtinEulerProduct
    (e : G ≃* QuaternionGroup 2) :
    DifferentiableOn ℂ (deningerQ8ArtinEulerProduct K L G e)
      artinEulerAbsoluteHalfPlane := by
  exact differentiableOn_numberFieldFinitePlaceArtinEulerReciprocalProduct
    (K := K) (L := L) (deningerQ8ArtinRepresentation e)

/-- The finite-place `Q₈` Artin Euler product has no zero in its absolute
convergence half-plane. -/
theorem deningerQ8ArtinEulerProduct_ne_zero_of_mem_artinEulerAbsoluteHalfPlane
    (e : G ≃* QuaternionGroup 2) {s : ℂ} (hs : s ∈ artinEulerAbsoluteHalfPlane) :
    deningerQ8ArtinEulerProduct K L G e s ≠ 0 := by
  exact numberFieldFinitePlaceArtinEulerReciprocalProduct_ne_zero_of_mem_artinEulerAbsoluteHalfPlane
    (K := K) (L := L) (deningerQ8ArtinRepresentation e) hs

end

end RHTower
