import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysTwistedNorm
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCharacterPoints

/-!
# The isotropy condition on character points

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Theorem 5.2,
equation (48).

`F_ν` acts on a character point by raising the character to the `ν`-th power, so the condition
`F_ν (x , P) = F_{ν'} (x , P ∘ σ)` is the identity `P^ν = (P ∘ σ)^{ν'}` of characters, which says
exactly that the image of Deninger's twisted norm lies in the kernel of `P`.
-/

namespace RHTower

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C]

/-- Two Frobenius twists of character points at the same point of `X` agree exactly when the
corresponding powers of the characters agree. -/
theorem deningerCharFrobenius_eq_iff (x : X) (P Q : (X.residueField x)ˣ →* Cˣ) (ν ν' : ℕ) :
    deningerCharFrobenius ν (⟨x, P⟩ : DeningerCharPoints X C)
        = deningerCharFrobenius ν' (⟨x, Q⟩ : DeningerCharPoints X C)
      ↔ P ^ ν = Q ^ ν' := by
  constructor
  · intro h
    have h' : (⟨x, P ^ ν⟩ : DeningerCharPoints X C) = ⟨x, Q ^ ν'⟩ := h
    exact eq_of_heq (Sigma.mk.injEq _ _ _ _ ▸ h' |>.2)
  · intro h
    exact congrArg (Sigma.mk x) h

/-- **Deninger, Theorem 5.2, equation (48).**  The isotropy condition on a character point is
exactly that the image of the twisted norm lies in the kernel of the character. -/
theorem deningerCharFrobenius_eq_iff_twistHom (x : X) (P : (X.residueField x)ˣ →* Cˣ)
    (σ : (X.residueField x)ˣ ≃* (X.residueField x)ˣ) (ν ν' : ℕ) :
    deningerCharFrobenius ν (⟨x, P⟩ : DeningerCharPoints X C)
        = deningerCharFrobenius ν' (⟨x, P.comp σ.toMonoidHom⟩ : DeningerCharPoints X C)
      ↔ (deningerTwistHom σ ν ν').range ≤ P.ker := by
  rw [deningerCharFrobenius_eq_iff, deningerTwistHom_range_le_ker_iff]

end RHTower
