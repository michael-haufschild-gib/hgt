import Mathlib.RingTheory.Ideal.Maps

/-!
# Split coefficient rings preserve all ideal powers

A retraction linear over the embedded ring contracts every extended ideal
exactly. This pays the ideal-order requirement in the source Rees kernel
without requiring generators to have equal ambient degree.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A R : Type*} [CommRing A] [CommRing R]

/-- An additive retraction linear over the embedded coefficient ring. -/
structure PaperIdealRetraction (f : A →+* R) where
  retract : R →+ A
  retract_map : ∀ a, retract (f a) = a
  retract_mul : ∀ a x, retract (f a * x) = a * retract x

/-- Retraction sends every extended ideal back into the original ideal. -/
theorem PaperIdealRetraction.retract_mem_map {f : A →+* R}
    (D : PaperIdealRetraction f) (J : Ideal A) {x : R} (hx : x ∈ J.map f) :
    D.retract x ∈ J := by
  have haux : ∀ b : R, D.retract (b * x) ∈ J := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro b
      rw [mul_comm b (f a), D.retract_mul]
      exact J.mul_mem_right _ ha
    | zero => intro b; simp only [mul_zero, map_zero]; exact J.zero_mem
    | add y z hy hz ihy ihz =>
      intro b
      rw [mul_add, map_add]
      exact J.add_mem (ihy b) (ihz b)
    | smul c y hy ih =>
      intro b
      change D.retract (b * (c * y)) ∈ J
      rw [← mul_assoc]
      exact ih (b * c)
  simpa only [one_mul] using haux 1

/-- An element of the coefficient ring enters an extended ideal exactly when it was already in it. -/
theorem PaperIdealRetraction.mem_map_iff {f : A →+* R}
    (D : PaperIdealRetraction f) (J : Ideal A) (a : A) :
    f a ∈ J.map f ↔ a ∈ J := by
  constructor
  · intro h
    simpa only [D.retract_map] using D.retract_mem_map J h
  · exact Ideal.mem_map_of_mem f

/-- Extension followed by contraction is the identity on every ideal. -/
theorem PaperIdealRetraction.comap_map {f : A →+* R}
    (D : PaperIdealRetraction f) (J : Ideal A) :
    (J.map f).comap f = J := by
  ext a
  exact D.mem_map_iff J a

/-- The splitting preserves ideal order at every power, with no flatness premise. -/
theorem PaperIdealRetraction.mem_map_pow_iff {f : A →+* R}
    (D : PaperIdealRetraction f) (J : Ideal A) (n : ℕ) (a : A) :
    f a ∈ (J.map f) ^ n ↔ a ∈ J ^ n := by
  rw [← Ideal.map_pow]
  exact D.mem_map_iff (J ^ n) a

end GaloisForLFunctions.HTGeometry
