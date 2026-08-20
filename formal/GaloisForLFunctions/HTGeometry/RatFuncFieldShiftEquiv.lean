import GaloisForLFunctions.HTGeometry.RatFuncFieldShift

/-!
# The unit shift is a ring automorphism of the rational-function field

Translations `r(X) ↦ r(X + c)` compose additively in `c` and reduce to the identity at `c = 0`, so
the unit shift is invertible with inverse the translation by `-1`.
-/

namespace GaloisForLFunctions.HTGeometry.FieldShift

open Polynomial nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F]

/-- The translation `p(X) ↦ p(X + c)` on polynomials, valued in the rational-function field. -/
def shiftCompHomOf (c : F) : Polynomial F →+* RatFunc F :=
  (algebraMap (Polynomial F) (RatFunc F)).comp
    (Polynomial.eval₂RingHom Polynomial.C (X + C c))

theorem shiftCompHomOf_apply (c : F) (p : Polynomial F) :
    shiftCompHomOf c p = algebraMap (Polynomial F) (RatFunc F) (p.comp (X + C c)) := rfl

theorem comp_X_add_C_ne_zero {c : F} {p : Polynomial F} (hp : p ≠ 0) :
    p.comp (X + C c) ≠ 0 := by
  intro h0
  exact hp ((Polynomial.comp_eq_zero_iff.mp h0).resolve_right
    (fun hh => by simpa using hh.2))

theorem shiftCompHomOf_mem_nonZeroDivisors (c : F) :
    (Polynomial F)⁰ ≤ (RatFunc F)⁰.comap (shiftCompHomOf c) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [shiftCompHomOf_apply]
  intro h0
  exact comp_X_add_C_ne_zero hp
    (RatFunc.algebraMap_injective F (by rw [h0, map_zero]))

/-- The translation `r(X) ↦ r(X + c)` of the rational-function field. -/
def ratShiftOf (c : F) : RatFunc F →+* RatFunc F :=
  RatFunc.liftRingHom (shiftCompHomOf c) (shiftCompHomOf_mem_nonZeroDivisors c)

theorem ratShiftOf_algebraMap (c : F) (p : Polynomial F) :
    ratShiftOf c (algebraMap (Polynomial F) (RatFunc F) p)
      = algebraMap (Polynomial F) (RatFunc F) (p.comp (X + C c)) := by
  have h := RatFunc.liftRingHom_apply_div (shiftCompHomOf c)
    (shiftCompHomOf_mem_nonZeroDivisors c) p 1
  simp only [map_one, div_one] at h
  exact h

theorem ratShiftOf_one_eq (r : RatFunc F) : ratShiftOf 1 r = ratShift r := by
  induction r using RatFunc.induction_on with
  | _ p q hq =>
      have hq' : algebraMap (Polynomial F) (RatFunc F) q ≠ 0 :=
        algebraMap_poly_ne_zero hq
      rw [map_div₀, map_div₀, ratShiftOf_algebraMap, ratShiftOf_algebraMap,
        ratShift_algebraMap, ratShift_algebraMap]

theorem ratShiftOf_ratShiftOf (c d : F) (r : RatFunc F) :
    ratShiftOf c (ratShiftOf d r) = ratShiftOf (c + d) r := by
  induction r using RatFunc.induction_on with
  | _ p q hq =>
      have hcomp : ∀ s : Polynomial F,
          (s.comp (X + C d)).comp (X + C c) = s.comp (X + C (c + d)) := by
        intro s
        rw [Polynomial.comp_assoc]
        congr 1
        simp [Polynomial.C_add]
        ring
      rw [map_div₀, map_div₀, map_div₀, ratShiftOf_algebraMap, ratShiftOf_algebraMap,
        ratShiftOf_algebraMap, ratShiftOf_algebraMap, ratShiftOf_algebraMap,
        ratShiftOf_algebraMap, hcomp, hcomp]

theorem ratShiftOf_zero (r : RatFunc F) : ratShiftOf 0 r = r := by
  induction r using RatFunc.induction_on with
  | _ p q hq =>
      have hcomp : ∀ s : Polynomial F, s.comp (X + C (0 : F)) = s := by
        intro s
        simp
      rw [map_div₀, ratShiftOf_algebraMap, ratShiftOf_algebraMap, hcomp, hcomp]

/-- The unit shift, as a ring automorphism of the rational-function field. -/
def ratShiftEquiv : RatFunc F ≃+* RatFunc F where
  toFun := ratShift
  invFun := ratShiftOf (-1)
  left_inv r := by
    rw [← ratShiftOf_one_eq, ratShiftOf_ratShiftOf]
    simpa using ratShiftOf_zero r
  right_inv r := by
    rw [← ratShiftOf_one_eq, ratShiftOf_ratShiftOf]
    simpa using ratShiftOf_zero r
  map_mul' := map_mul ratShift
  map_add' := map_add ratShift

@[simp] theorem ratShiftEquiv_apply (r : RatFunc F) : ratShiftEquiv r = ratShift r := rfl

@[simp] theorem ratShiftEquiv_symm_apply (r : RatFunc F) :
    (ratShiftEquiv : RatFunc F ≃+* RatFunc F).symm r = ratShiftOf (-1) r := rfl

end

end GaloisForLFunctions.HTGeometry.FieldShift
