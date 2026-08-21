import GaloisForLFunctions.HTGeometry.RatFuncFieldShift

/-!
# A polynomial invariant under one nonzero translation is constant

Invariance under the unit shift already forces constancy in characteristic zero.  Invariance under
an arbitrary nonzero shift reduces to it by rescaling the variable: if `p(X + a) = p(X)` then
`q(X) = p(aX)` satisfies `q(X + 1) = q(X)`, so `q` is constant, and rescaling back makes `p`
constant.

This is the order-zero half of "translation-invariant functions on a connected group are constant",
which is what the pure-expanding case of an isogeny tail needs.

* `comp_X_add_C_eq_self`;
* `comp_X_add_one_eq_self_domain`, `comp_X_add_C_eq_self_domain` — the same over any
  characteristic-zero integral domain, which is what a coefficient ring of remaining variables is.
-/

namespace GaloisForLFunctions.HTGeometry

namespace FieldShift

open Polynomial

variable {F : Type*} [Field F] [CharZero F]

/-- **A polynomial invariant under one nonzero translation is constant.** -/
theorem comp_X_add_C_eq_self {p : Polynomial F} {a : F} (ha : a ≠ 0)
    (h : p.comp (X + C a) = p) : p = C (p.eval 0) := by
  set q : Polynomial F := p.comp (C a * X) with hq
  have hqshift : q.comp (X + C 1) = q := by
    rw [hq, Polynomial.comp_assoc]
    have hinner : (C a * X).comp (X + C 1) = (X + C a).comp (C a * X) := by
      simp [Polynomial.mul_comp, Polynomial.add_comp]
      ring
    rw [hinner, ← Polynomial.comp_assoc, h]
  have hqconst : q = C (q.eval 0) := comp_X_add_one_eq_self hqshift
  have hq0 : q.eval 0 = p.eval 0 := by
    rw [hq, Polynomial.eval_comp]
    simp
  have hback : p = q.comp (C a⁻¹ * X) := by
    rw [hq, Polynomial.comp_assoc]
    have hinner : (C a * X).comp (C a⁻¹ * X) = X := by
      simp [Polynomial.mul_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha]
    rw [hinner, Polynomial.comp_X]
  rw [hback, hqconst, hq0]
  simp

/-! ### Over an integral domain -/

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- **Invariance under the unit shift forces constancy over any characteristic-zero domain.** -/
theorem comp_X_add_one_eq_self_domain {p : Polynomial R} (h : p.comp (X + C 1) = p) :
    p = C (p.eval 0) := by
  have hval : ∀ n : ℕ, p.eval ((n : R)) = p.eval 0 := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
        have hk := congrArg (Polynomial.eval ((k : R))) h
        simp only [eval_comp, eval_add, eval_X, eval_C] at hk
        push_cast
        rw [hk, ih]
  have hroot : ∀ n : ℕ, (p - C (p.eval 0)).IsRoot ((n : R)) := by
    intro n
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, hval n, sub_self]
  have hinj : Function.Injective (fun n : ℕ => (n : R)) := Nat.cast_injective
  have hinf : {x : R | (p - C (p.eval 0)).IsRoot x}.Infinite := by
    refine Set.Infinite.mono (s := Set.range fun n : ℕ => (n : R)) ?_ ?_
    · rintro x ⟨n, rfl⟩
      exact hroot n
    · exact Set.infinite_range_of_injective hinj
  have hzero : p - C (p.eval 0) = 0 := Polynomial.eq_zero_of_infinite_isRoot _ hinf
  linear_combination hzero

/-- **A polynomial over a characteristic-zero domain invariant under one nonzero translation whose
rescaling is available is constant.** -/
theorem comp_X_add_C_eq_self_domain {p : Polynomial R} {a : R} (ha : IsUnit a)
    (h : p.comp (X + C a) = p) : p = C (p.eval 0) := by
  obtain ⟨u, rfl⟩ := ha
  set q : Polynomial R := p.comp (C (u : R) * X) with hq
  have hqshift : q.comp (X + C 1) = q := by
    rw [hq, Polynomial.comp_assoc]
    have hinner : (C (u : R) * X).comp (X + C 1) = (X + C (u : R)).comp (C (u : R) * X) := by
      simp [Polynomial.mul_comp, Polynomial.add_comp]
      ring
    rw [hinner, ← Polynomial.comp_assoc, h]
  have hqconst : q = C (q.eval 0) := comp_X_add_one_eq_self_domain hqshift
  have hq0 : q.eval 0 = p.eval 0 := by
    rw [hq, Polynomial.eval_comp]
    simp
  have hback : p = q.comp (C ((u⁻¹ : Rˣ) : R) * X) := by
    rw [hq, Polynomial.comp_assoc]
    have hinner : (C (u : R) * X).comp (C ((u⁻¹ : Rˣ) : R) * X) = X := by
      simp [Polynomial.mul_comp, ← mul_assoc, ← C_mul]
    rw [hinner, Polynomial.comp_X]
  rw [hback, hqconst, hq0]
  simp

end Domain

end FieldShift

end GaloisForLFunctions.HTGeometry
