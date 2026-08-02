import Mathlib.RingTheory.Kaehler.Polynomial
import GaloisForLFunctions.RHTower.DeningerPrincipalConormal

/-!
# The differential line of a monic hypersurface

The relative differential module of a univariate polynomial algebra is free of rank one on the
differential of the coordinate, so its base change along any quotient is free of rank one on the
same class.  For the quotient by a monic polynomial this is the second of the two trivializations
that orient the fundamental class of a monic hypersurface, the first being the conormal
trivialization by the class of the polynomial.

Under the trivialization the differential of a polynomial is its derivative, so the two-term
presentation of the cotangent complex of a monic hypersurface has both terms free of rank one and
its differential is multiplication by the derivative of the polynomial.

* `deningerKaehlerBaseChangeEquiv` : **the base-changed differential module is free of rank one.**
* `deningerKaehlerBaseChangeEquiv_D` : the differential of a polynomial goes to its derivative.
* `deningerKaehlerBaseChangeEquiv_D_X` : **the trivialization by the class of the coordinate.**
-/

open Polynomial TensorProduct KaehlerDifferential

namespace RHTower

section KaehlerLine

variable {A : Type*} [CommRing A] (P : Polynomial A)

/-- The quotient of the polynomial algebra by a principal ideal, as the target of the base
change. -/
abbrev DeningerMonicQuotient : Type _ :=
  Polynomial A ⧸ Ideal.span ({P} : Set (Polynomial A))

/-- **The base-changed differential module is free of rank one.**  The relative differential module
of `A[X]` is free of rank one on `dX`, so its base change to the quotient is free of rank one on the
same class. -/
noncomputable def deningerKaehlerBaseChangeEquiv :
    (Ω[Polynomial A⁄A] ⊗[Polynomial A] DeningerMonicQuotient P)
      ≃ₗ[Polynomial A] DeningerMonicQuotient P :=
  (LinearEquiv.rTensor (DeningerMonicQuotient P) (KaehlerDifferential.polynomialEquiv A)).trans
    (TensorProduct.lid (Polynomial A) (DeningerMonicQuotient P))

@[simp]
theorem deningerKaehlerBaseChangeEquiv_D (Q : Polynomial A) (b : DeningerMonicQuotient P) :
    deningerKaehlerBaseChangeEquiv P
        ((KaehlerDifferential.D A (Polynomial A) Q) ⊗ₜ[Polynomial A] b)
      = Polynomial.derivative Q • b := by
  show TensorProduct.lid (Polynomial A) (DeningerMonicQuotient P)
      ((KaehlerDifferential.polynomialEquiv A
        (KaehlerDifferential.D A (Polynomial A) Q)) ⊗ₜ[Polynomial A] b) = _
  rw [KaehlerDifferential.polynomialEquiv_D, TensorProduct.lid_tmul]

/-- **The trivialization by the class of the coordinate.**  The differential of the coordinate
generates the base-changed differential module: it is sent to the unit. -/
theorem deningerKaehlerBaseChangeEquiv_D_X :
    deningerKaehlerBaseChangeEquiv P
        ((KaehlerDifferential.D A (Polynomial A) Polynomial.X) ⊗ₜ[Polynomial A]
          (1 : DeningerMonicQuotient P))
      = 1 := by
  rw [deningerKaehlerBaseChangeEquiv_D, Polynomial.derivative_X, one_smul]

/-- The differential of the defining polynomial is its derivative: under the two trivializations —
the conormal one by the class of `P` and the differential one by the class of `X` — the two-term
presentation of the cotangent complex of a monic hypersurface has differential multiplication by
`P'`. -/
theorem deningerKaehlerBaseChangeEquiv_D_self (b : DeningerMonicQuotient P) :
    deningerKaehlerBaseChangeEquiv P
        ((KaehlerDifferential.D A (Polynomial A) P) ⊗ₜ[Polynomial A] b)
      = Polynomial.derivative P • b :=
  deningerKaehlerBaseChangeEquiv_D P P b

end KaehlerLine

end RHTower
