import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Abel

/-!
# The exact cutoff identity for the Suzuki tail equation

Let `F` solve the carrier-valued homogeneous tail equation

`(2L + R - T)F' + F = 0`

and put `W = χF`.  Because `R` commutes with differentiation and `T` commutes with multiplication by
the scalar cutoff, the cutoff of a solution solves the same equation with an explicit residual:

`(2L + R - T)W' + W = ([R,χ]F)' + (2L + R - T)(χ'F) - [R,χ']F`.

The identity is exact and purely algebraic: it needs only the Leibniz rule for the cutoff, the
commutation of the jump operator with differentiation, and the commutation of the operator and the
coefficient with the scalar cutoff.  Its point is that **no derivative of `F` appears inside a
commutator**: the only derivative on the right is the outer one applied to `[R,χ]F`, and the two
remaining terms are supported where `χ'` is.
-/

namespace GaloisForLFunctions.RHTower

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- **`(51)`: the exact cutoff identity.**  Cutting a solution of the homogeneous tail equation
produces exactly the derivative of the cutoff commutator plus terms carried by `χ'`. -/
theorem cutoff_forcing_identity (D Rop Top Mχ Mχ' M2L : V →ₗ[R] V) (F : V)
    (hLeibniz : ∀ v : V, D (Mχ v) = Mχ' v + Mχ (D v))
    (hRD : ∀ v : V, Rop (D v) = D (Rop v))
    (hTχ : ∀ v : V, Top (Mχ v) = Mχ (Top v))
    (h2Lχ : ∀ v : V, M2L (Mχ v) = Mχ (M2L v))
    (heq : M2L (D F) + Rop (D F) - Top (D F) + F = 0) :
    M2L (D (Mχ F)) + Rop (D (Mχ F)) - Top (D (Mχ F)) + Mχ F
      = D (Rop (Mχ F) - Mχ (Rop F))
        + (M2L (Mχ' F) + Rop (Mχ' F) - Top (Mχ' F))
        - (Rop (Mχ' F) - Mχ' (Rop F)) := by
  have hexp : (M2L (D (Mχ F)) + Rop (D (Mχ F)) - Top (D (Mχ F)) + Mχ F)
      - (D (Rop (Mχ F) - Mχ (Rop F))
        + (M2L (Mχ' F) + Rop (Mχ' F) - Top (Mχ' F))
        - (Rop (Mχ' F) - Mχ' (Rop F)))
      = Mχ (M2L (D F) + Rop (D F) - Top (D F) + F) := by
    simp only [hLeibniz F, hLeibniz (Rop F), map_add, map_sub, h2Lχ, hTχ, ← hRD]
    abel
  have hzero : (M2L (D (Mχ F)) + Rop (D (Mχ F)) - Top (D (Mχ F)) + Mχ F)
      - (D (Rop (Mχ F) - Mχ (Rop F))
        + (M2L (Mχ' F) + Rop (Mχ' F) - Top (Mχ' F))
        - (Rop (Mχ' F) - Mχ' (Rop F))) = 0 := by
    rw [hexp, heq, map_zero]
  exact sub_eq_zero.mp hzero

/-- The cutoff commutator, in the operator form used by the identity. -/
def cutoffCommutatorOp (Rop Mχ : V →ₗ[R] V) : V →ₗ[R] V := Rop ∘ₗ Mχ - Mχ ∘ₗ Rop

theorem cutoffCommutatorOp_apply (Rop Mχ : V →ₗ[R] V) (v : V) :
    cutoffCommutatorOp Rop Mχ v = Rop (Mχ v) - Mχ (Rop v) := rfl

/-- **`(51)` in commutator notation.** -/
theorem cutoff_forcing_identity_commutator (D Rop Top Mχ Mχ' M2L : V →ₗ[R] V) (F : V)
    (hLeibniz : ∀ v : V, D (Mχ v) = Mχ' v + Mχ (D v))
    (hRD : ∀ v : V, Rop (D v) = D (Rop v))
    (hTχ : ∀ v : V, Top (Mχ v) = Mχ (Top v))
    (h2Lχ : ∀ v : V, M2L (Mχ v) = Mχ (M2L v))
    (heq : M2L (D F) + Rop (D F) - Top (D F) + F = 0) :
    M2L (D (Mχ F)) + Rop (D (Mχ F)) - Top (D (Mχ F)) + Mχ F
      = D (cutoffCommutatorOp Rop Mχ F)
        + (M2L (Mχ' F) + Rop (Mχ' F) - Top (Mχ' F))
        - cutoffCommutatorOp Rop Mχ' F := by
  rw [cutoffCommutatorOp_apply, cutoffCommutatorOp_apply]
  exact cutoff_forcing_identity D Rop Top Mχ Mχ' M2L F hLeibniz hRD hTχ h2Lχ heq

end GaloisForLFunctions.RHTower
