import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The quantized-differential cocycle and its trace additivity

For a fixed polarization `F` in a ring `A`, the quantized differential of an element is the
commutator `δ(U) = F U − U F`, and the logarithmic quantized differential of a **unit** is
`ω(U) = U⁻¹ δ(U)`.  The Leibniz rule `δ(x y) = δ(x) y + x δ(y)` gives the exact cocycle identity

`ω(U V) = V⁻¹ ω(U) V + ω(V)`,

valid for arbitrary — in particular noncommuting — units, and with no hypothesis on `F`.  Modulo
conjugation coboundaries `X ↦ V⁻¹ X V − X` the assignment is therefore additive.

Against a cyclic additive trace `τ` and a test element commuting with every factor, the
conjugations disappear and the pairing is **exactly additive over an ordered factorization**.  This
is the algebraic content behind factorization-independence of a degree-one orbital source class.
-/

namespace HTGeometry

section Cocycle

variable {A : Type*} [Ring A]

/-- The quantized differential `δ(U) = F U − U F`. -/
def quantizedDelta (F U : A) : A := F * U - U * F

/-- **Leibniz rule for the quantized differential.**  No units and no condition on `F`. -/
theorem quantizedDelta_mul (F x y : A) :
    quantizedDelta F (x * y) = quantizedDelta F x * y + x * quantizedDelta F y := by
  simp only [quantizedDelta]
  noncomm_ring

/-- The logarithmic quantized differential `ω(U) = U⁻¹ δ(U)` of a unit. -/
def quantizedOmega (F : A) (U : Aˣ) : A := (↑U⁻¹ : A) * quantizedDelta F (U : A)

/-- **The Leibniz cocycle identity.** -/
theorem quantizedOmega_mul (F : A) (U V : Aˣ) :
    quantizedOmega F (U * V) = (↑V⁻¹ : A) * quantizedOmega F U * (V : A) + quantizedOmega F V := by
  have hU : (↑U⁻¹ : A) * (U : A) = 1 := U.inv_mul
  have hUV : (((U * V)⁻¹ : Aˣ) : A) = (↑V⁻¹ : A) * (↑U⁻¹ : A) := by
    rw [mul_inv_rev, Units.val_mul]
  calc quantizedOmega F (U * V)
      = (↑V⁻¹ : A) * (↑U⁻¹ : A) *
          (quantizedDelta F (U : A) * (V : A) + (U : A) * quantizedDelta F (V : A)) := by
        rw [quantizedOmega, Units.val_mul, quantizedDelta_mul, hUV]
    _ = (↑V⁻¹ : A) * ((↑U⁻¹ : A) * quantizedDelta F (U : A)) * (V : A)
          + (↑V⁻¹ : A) * ((↑U⁻¹ : A) * (U : A)) * quantizedDelta F (V : A) := by
        noncomm_ring
    _ = (↑V⁻¹ : A) * quantizedOmega F U * (V : A) + quantizedOmega F V := by
        rw [hU, mul_one, quantizedOmega, quantizedOmega]

end Cocycle

section TraceAdditivity

variable {A R : Type*} [Ring A] [AddCommGroup R]

/-- A test element commuting with every factor commutes with the ordered product. -/
theorem commute_units_listProd {a : A} :
    ∀ (L : List Aˣ), (∀ U ∈ L, Commute a (U : A)) → Commute a (L.prod : A)
  | [], _ => by simp
  | U :: T, h => by
      have hU : Commute a (U : A) := h U (by simp)
      have hT : Commute a (T.prod : A) := commute_units_listProd T fun V hV => h V (by simp [hV])
      have hp : (((U :: T).prod : Aˣ) : A) = (U : A) * (T.prod : A) := by
        rw [List.prod_cons, Units.val_mul]
      rw [hp]
      exact hU.mul_right hT

/-- **Trace additivity of the quantized-differential class over an ordered factorization.**  A
cyclic additive trace paired with a test element commuting with every factor does not see the
conjugation coboundaries, so the pairing is exactly the sum of the local pairings. -/
theorem trace_quantizedOmega_listProd (F : A) (tau : A → R)
    (htau_add : ∀ x y : A, tau (x + y) = tau x + tau y)
    (htau_cyc : ∀ x y : A, tau (x * y) = tau (y * x)) (a : A) :
    ∀ L : List Aˣ, (∀ U ∈ L, Commute a (U : A)) →
      tau (a * quantizedOmega F L.prod) = (L.map fun U => tau (a * quantizedOmega F U)).sum
  | [], _ => by
      have hzero : a * quantizedOmega F ([] : List Aˣ).prod = 0 := by
        simp [quantizedOmega, quantizedDelta]
      have h0 : tau (0 : A) = 0 := by
        have := htau_add 0 0
        simpa using this.symm
      rw [hzero, h0]
      simp
  | U :: T, h => by
      have hU : Commute a (U : A) := h U (by simp)
      have hmem : ∀ V ∈ T, Commute a (V : A) := fun V hV => h V (by simp [hV])
      have hT : Commute a (T.prod : A) := commute_units_listProd T hmem
      have hTi : Commute a ((↑(T.prod)⁻¹ : A)) := hT.units_inv_right
      have hprod : ((U :: T).prod : Aˣ) = U * T.prod := by rw [List.prod_cons]
      have hcancel : (T.prod : A) * (↑(T.prod)⁻¹ : A) = 1 := T.prod.mul_inv
      have hconj : tau (a * ((↑(T.prod)⁻¹ : A) * quantizedOmega F U * (T.prod : A)))
          = tau (a * quantizedOmega F U) := by
        have hstep : a * ((↑(T.prod)⁻¹ : A) * quantizedOmega F U * (T.prod : A))
            = ((↑(T.prod)⁻¹ : A) * (a * quantizedOmega F U)) * (T.prod : A) := by
          rw [← mul_assoc, ← mul_assoc, hTi.eq,
            mul_assoc (↑(T.prod)⁻¹ : A) a (quantizedOmega F U)]
        rw [hstep, htau_cyc, ← mul_assoc, hcancel, one_mul]
      rw [hprod, quantizedOmega_mul, mul_add, htau_add, hconj,
        trace_quantizedOmega_listProd F tau htau_add htau_cyc a T hmem]
      simp

end TraceAdditivity

end HTGeometry
