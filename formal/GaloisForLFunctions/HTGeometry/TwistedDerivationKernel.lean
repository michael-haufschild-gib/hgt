import GaloisForLFunctions.HTGeometry.DerivationPrescription
import Mathlib.Analysis.Complex.Basic

/-!
# Derivations along a field map, their kernels, and algebraic closures

Let `ι : B → L` be a map of fields and `D : B → L` additive with `D(xy) = ι(x) D(y) + ι(y) D(x)`
(the difference of two derivations compatible along `ι`).  Its kernel is a subfield, and in
characteristic zero it contains every element algebraic over a subfield it contains: differentiating
the minimal polynomial gives `ι(p'(v)) D(v) = 0` with `p'(v) ≠ 0`.  So two derivations compatible
along `ι` on a subfield `F` are compatible on every algebraic extension of `F` inside `B`.

Also: every `ℂ`-derivation of a field of characteristic zero extends to its algebraic closure, and
Jacobians `det(∂_j δ^i U)` are carried along compatible field maps.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

section Twisted

variable {B L : Type*} [Field B] [Field L] (ι : B →+* L) (D : B → L)
  (hadd : ∀ x y, D (x + y) = D x + D y) (hmul : ∀ x y, D (x * y) = ι x * D y + ι y * D x)

include hadd in
theorem twisted_map_zero : D 0 = 0 := by
  have h := hadd 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

include hmul in
theorem twisted_map_one : D 1 = 0 := by
  have h := hmul 1 1
  rw [mul_one, map_one, one_mul] at h
  exact left_eq_add.mp h

include hadd in
theorem twisted_map_neg (x : B) : D (-x) = -D x := by
  have h := hadd (-x) x
  rw [neg_add_cancel, twisted_map_zero D hadd] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The kernel of a derivation along a field map is a subfield. -/
def twistedKernel : Subfield B where
  carrier := {x | D x = 0}
  mul_mem' {x y} hx hy := by
    change D (x * y) = 0
    change D x = 0 at hx
    change D y = 0 at hy
    rw [hmul, hx, hy, mul_zero, mul_zero, add_zero]
  one_mem' := twisted_map_one ι D hmul
  add_mem' {x y} hx hy := by
    change D (x + y) = 0
    change D x = 0 at hx
    change D y = 0 at hy
    rw [hadd, hx, hy, add_zero]
  zero_mem' := twisted_map_zero D hadd
  neg_mem' {x} hx := by
    change D (-x) = 0
    change D x = 0 at hx
    rw [twisted_map_neg D hadd, hx, neg_zero]
  inv_mem' x hx := by
    change D x⁻¹ = 0
    change D x = 0 at hx
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      exact twisted_map_zero D hadd
    · have h := hmul x x⁻¹
      rw [mul_inv_cancel₀ hx0, twisted_map_one ι D hmul, hx, mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left ((map_ne_zero ι).mpr hx0)

theorem mem_twistedKernel {x : B} : x ∈ twistedKernel ι D hadd hmul ↔ D x = 0 := Iff.rfl

include hmul in
theorem twisted_map_pow_succ (v : B) (n : ℕ) :
    D (v ^ (n + 1)) = ((n : L) + 1) * ι v ^ n * D v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, hmul, ih, map_pow]
      push_cast
      ring

include hadd hmul in
/-- A polynomial with coefficients in a field `S → B` killed by `D` differentiates by the chain
rule. -/
theorem twisted_map_aeval {S : Type*} [Field S] [Algebra S B]
    (hS : ∀ s : S, D (algebraMap S B s) = 0) (q : Polynomial S) (v : B) :
    D (aeval v q) = ι (aeval v (derivative q)) * D v := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [map_add, hadd, hp, hr, derivative_add, map_add, map_add, add_mul]
  | monomial n a =>
      have ha : D (algebraMap S B a) = 0 := hS a
      rw [aeval_monomial, derivative_monomial, aeval_monomial]
      cases n with
      | zero =>
          simp only [pow_zero, mul_one, Nat.cast_zero, mul_zero, map_zero, zero_mul]
          exact ha
      | succ n =>
          rw [hmul, ha, mul_zero, add_zero, twisted_map_pow_succ ι D hmul, Nat.add_sub_cancel]
          simp only [map_mul, map_pow, map_natCast]
          push_cast
          ring

include hadd hmul in
/-- **Algebraic elements are killed.**  In characteristic zero, `D` vanishes on every element
integral over a field `S → B` on which it vanishes. -/
theorem twisted_eq_zero_of_isIntegral {S' : Type*} [Field S'] [CharZero S'] [Algebra S' B]
    (hS : ∀ s : S', D (algebraMap S' B s) = 0) {v : B} (hv : IsIntegral S' v) : D v = 0 := by
  have hsep : (minpoly S' v).Separable := (minpoly.irreducible hv).separable
  have hroot : aeval v (minpoly S' v) = 0 := minpoly.aeval S' v
  have hder : aeval v (derivative (minpoly S' v)) ≠ 0 := hsep.aeval_derivative_ne_zero hroot
  have h := twisted_map_aeval ι D hadd hmul hS (minpoly S' v) v
  rw [hroot, twisted_map_zero D hadd] at h
  exact (mul_eq_zero.mp h.symm).resolve_left ((map_ne_zero ι).mpr hder)

end Twisted

/-! ## Extension to the algebraic closure and transport of Jacobians -/

/-- Every `ℂ`-derivation of a field of characteristic zero extends to its algebraic closure. -/
theorem exists_derivation_algebraicClosure {L : Type*} [Field L] [Algebra ℂ L] [CharZero L]
    (D : Derivation ℂ L L) :
    ∃ D' : Derivation ℂ (AlgebraicClosure L) (AlgebraicClosure L),
      ∀ a : L, D' (algebraMap L (AlgebraicClosure L) a) =
        algebraMap L (AlgebraicClosure L) (D a) :=
  exists_derivation_extension D

/-- Jacobians `det(∂_j δ^i U)` are carried along ring maps compatible with the derivations. -/
theorem map_derivationJacobian_det {m : ℕ} {L C : Type*} [CommRing L] [CommRing C] (φ : L →+* C)
    (δL : L → L) (δC : C → C) (pL : Fin m → L → L) (pC : Fin m → C → C)
    (hδ : ∀ x, φ (δL x) = δC (φ x)) (hp : ∀ j x, φ (pL j x) = pC j (φ x)) (U : L) :
    φ (Matrix.of fun i j : Fin m => pL j ((δL^[(i : ℕ)]) U)).det =
      (Matrix.of fun i j : Fin m => pC j ((δC^[(i : ℕ)]) (φ U))).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  have hsemi : Function.Semiconj φ δL δC := fun x => hδ x
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, hp,
    (hsemi.iterate_right (i : ℕ)) U]

end GaloisForLFunctions.HTGeometry
