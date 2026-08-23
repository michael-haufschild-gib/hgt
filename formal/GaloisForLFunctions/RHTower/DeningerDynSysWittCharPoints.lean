import GaloisForLFunctions.RHTower.DeningerDynSysWittValuedPoint
import GaloisForLFunctions.RHTower.DeningerDynSysCharacterPoints

/-!
# The `C`-valued points of `W_rat (X)`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), equation (26).

A `C`-valued point of `W_rat (X)` is a point `x` of `X` together with a ring homomorphism
`W_rat (κ (x)) → C`.  When `κ (x)` is algebraically closed the Teichmüller comparison
`ω : ℤ̲κ (x) ≅ W_rat (κ (x))` turns such a homomorphism into a pointed multiplicative map
`κ (x) → C`, equivalently into a character of `κ (x)ˣ`.  This is Deninger's identification
`W_rat (X)(C) = X̂ (C)`.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C]

/-- **Deninger, §3.**  A `C`-valued point of `W_rat (X)`: a point together with a ring
homomorphism out of the rational Witt ring of its residue field. -/
abbrev DeningerWittCharPoints (X : Scheme.{u}) (C : Type u) [Field C] : Type u :=
  Σ x : X, (DeningerCanonicalRationalWittRing (X.residueField x) →+* C)

variable [∀ x : X, IsAlgClosed (X.residueField x)]

/-- **Deninger, (26).**  The `C`-valued points of `W_rat (X)` are the character points of `X`. -/
def deningerWittCharPointsEquiv :
    DeningerWittCharPoints X C ≃ DeningerCharPoints X C :=
  Equiv.sigmaCongrRight fun x =>
    (deningerWittFieldHomEquivPointed (X.residueField x) C).trans
      (deningerFieldPointedEquivChar (X.residueField x) C)

@[simp] theorem deningerWittCharPointsEquiv_fst (P : DeningerWittCharPoints X C) :
    (deningerWittCharPointsEquiv P).1 = P.1 := rfl

theorem deningerWittCharPointsEquiv_snd (P : DeningerWittCharPoints X C)
    (u : (X.residueField P.1)ˣ) :
    ((deningerWittCharPointsEquiv P).2 u : Cˣ) = P.2 (deningerCanonicalRationalWittTeichmuller
      (u : X.residueField P.1)) := by
  show ((deningerFieldPointedEquivChar (X.residueField P.1) C
    (deningerWittFieldHomEquivPointed (X.residueField P.1) C P.2) u : Cˣ) : C) = _
  show deningerWittFieldHomEquivPointed (X.residueField P.1) C P.2
    (u : X.residueField P.1) = _
  rw [deningerWittFieldHomEquivPointed_apply]

end

end RHTower
