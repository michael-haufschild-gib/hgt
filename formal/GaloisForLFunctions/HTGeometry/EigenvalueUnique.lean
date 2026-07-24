import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic.LinearCombination

/-!
# The scaling eigenvalue is a unique nonzero constant

If a `C`-algebra automorphism `σ` scales a nonzero element `q` by a base constant, `σ q = a·q`, that
constant is nonzero (`σ` is injective) and unique.  This is the `∃! a ∈ C^*` sharpening of the
charged clock-character conclusion (equation (4)): `Φ(q) = a·q` for a *unique* `a ∈ C^*`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {C E : Type*} [Field C] [Field E] [Algebra C E]

/-- A scaling eigenvalue of a nonzero vector under an automorphism is nonzero. -/
theorem algEquiv_eigenvalue_ne_zero (σ : E ≃ₐ[C] E) {q : E} (hq : q ≠ 0) {a : C}
    (ha : σ q = algebraMap C E a * q) : a ≠ 0 := by
  intro h0
  rw [h0, map_zero, zero_mul] at ha
  exact hq (σ.injective (ha.trans (map_zero σ).symm))

/-- The scaling eigenvalue of a nonzero vector is unique. -/
theorem algEquiv_eigenvalue_unique (σ : E ≃ₐ[C] E) {q : E} (hq : q ≠ 0) {a a' : C}
    (ha : σ q = algebraMap C E a * q) (ha' : σ q = algebraMap C E a' * q) : a = a' := by
  have h2 : algebraMap C E a = algebraMap C E a' := mul_right_cancel₀ hq (ha.symm.trans ha')
  have h3 : algebraMap C E (a - a') = 0 := by rw [map_sub, h2, sub_self]
  exact sub_eq_zero.mp (by rwa [map_eq_zero] at h3)

/-- **`∃! a ∈ C^*` (equation (4)).**  If `σ q = a·q` for some constant `a`, then there is a *unique*
nonzero constant scaling `q`, namely `a`. -/
theorem algEquiv_eigenvalue_existsUnique (σ : E ≃ₐ[C] E) {q : E} (hq : q ≠ 0) {a : C}
    (ha : σ q = algebraMap C E a * q) :
    a ≠ 0 ∧ ∃! b : C, σ q = algebraMap C E b * q := by
  refine ⟨algEquiv_eigenvalue_ne_zero σ hq ha, a, ha, ?_⟩
  intro b hb
  exact algEquiv_eigenvalue_unique σ hq hb ha

end GaloisForLFunctions.HTGeometry
