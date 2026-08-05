import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# The cyclic one-cocycle of a trace and a derivation

Let `A` be an associative (possibly non-unital) ring, `τ` an additive trace on `A`, and `D` an
additive derivation of `A`.  Whenever `τ` annihilates the image of `D`, the bilinear form

```text
φ(a₀, a₁) = τ (a₀ · D a₁)
```

is a cyclic Hochschild one-cocycle: it is antisymmetric and it kills every degree-two Hochschild
boundary `a·b ⊗ c - a ⊗ b·c + c·a ⊗ b`.  Antisymmetry is in fact *equivalent* to `τ ∘ D = 0` on
products, so the annihilation hypothesis is not an accident of any particular model.

The second half is the transport law.  A ring homomorphism that intertwines the two derivations and
pulls the target trace back to the source trace also pulls the target cocycle back to the source
cocycle.  Consequently a comparison of this kind cannot erase any element on which the source
cocycle is nonzero: non-erasure of a distinguished atom is reduced to two intertwining identities,
with no further information about the comparison required.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A B K : Type*} [NonUnitalRing A] [NonUnitalRing B] [AddCommGroup K]

/-- A trace: an additive map that is invariant under cyclic rotation of a product. -/
def IsAlgebraTrace (τ : A →+ K) : Prop := ∀ a b : A, τ (a * b) = τ (b * a)

/-- A derivation: an additive map satisfying the Leibniz rule. -/
def IsAlgebraDerivation (D : A →+ A) : Prop := ∀ a b : A, D (a * b) = D a * b + a * D b

/-- The bilinear form `φ(a₀, a₁) = τ (a₀ · D a₁)` attached to a trace and a derivation. -/
def traceDerivCocycle (τ : A →+ K) (D : A →+ A) (a b : A) : K := τ (a * D b)

@[simp]
theorem traceDerivCocycle_apply (τ : A →+ K) (D : A →+ A) (a b : A) :
    traceDerivCocycle τ D a b = τ (a * D b) := rfl

@[simp]
theorem traceDerivCocycle_zero_left (τ : A →+ K) (D : A →+ A) (b : A) :
    traceDerivCocycle τ D 0 b = 0 := by
  simp [traceDerivCocycle]

@[simp]
theorem traceDerivCocycle_zero_right (τ : A →+ K) (D : A →+ A) (a : A) :
    traceDerivCocycle τ D a 0 = 0 := by
  simp [traceDerivCocycle]

theorem traceDerivCocycle_add_left (τ : A →+ K) (D : A →+ A) (a a' b : A) :
    traceDerivCocycle τ D (a + a') b =
      traceDerivCocycle τ D a b + traceDerivCocycle τ D a' b := by
  simp [traceDerivCocycle, add_mul]

theorem traceDerivCocycle_add_right (τ : A →+ K) (D : A →+ A) (a b b' : A) :
    traceDerivCocycle τ D a (b + b') =
      traceDerivCocycle τ D a b + traceDerivCocycle τ D a b' := by
  simp [traceDerivCocycle, mul_add]

/-! ## The cocycle laws -/

/-- **Antisymmetry is exactly annihilation of the derivation by the trace.** -/
theorem traceDerivCocycle_antisymm_iff {τ : A →+ K} {D : A →+ A}
    (hτ : IsAlgebraTrace τ) (hD : IsAlgebraDerivation D) :
    (∀ a b : A, traceDerivCocycle τ D a b = -traceDerivCocycle τ D b a) ↔
      ∀ a b : A, τ (D (a * b)) = 0 := by
  constructor
  · intro h a b
    rw [hD a b, map_add, hτ (D a) b]
    have hval := h a b
    simp only [traceDerivCocycle] at hval
    rw [hval]
    simp
  · intro h a b
    have hab := h a b
    rw [hD a b, map_add, hτ (D a) b] at hab
    simp only [traceDerivCocycle]
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hab

/-- **Antisymmetry.**  If the trace annihilates the derivation, the cocycle is antisymmetric. -/
theorem traceDerivCocycle_antisymm {τ : A →+ K} {D : A →+ A}
    (hτ : IsAlgebraTrace τ) (hD : IsAlgebraDerivation D) (hτD : ∀ a : A, τ (D a) = 0) (a b : A) :
    traceDerivCocycle τ D a b = -traceDerivCocycle τ D b a :=
  (traceDerivCocycle_antisymm_iff hτ hD).mpr (fun a b => hτD (a * b)) a b

/-- **Hochschild cocycle law.**  The form kills every pure degree-two Hochschild boundary.  Only
the trace property and the Leibniz rule are used; the trace need not annihilate the derivation. -/
theorem traceDerivCocycle_boundary {τ : A →+ K} {D : A →+ A}
    (hτ : IsAlgebraTrace τ) (hD : IsAlgebraDerivation D) (a b c : A) :
    traceDerivCocycle τ D (a * b) c - traceDerivCocycle τ D a (b * c) +
      traceDerivCocycle τ D (c * a) b = 0 := by
  have hsplit : traceDerivCocycle τ D a (b * c) =
      traceDerivCocycle τ D (c * a) b + traceDerivCocycle τ D (a * b) c := by
    simp only [traceDerivCocycle]
    rw [hD b c, mul_add]
    rw [map_add]
    congr 1
    · rw [← mul_assoc, hτ (a * D b) c, ← mul_assoc]
    · rw [← mul_assoc]
  rw [hsplit]
  abel

/-! ## Transport along a comparison -/

/-- **Naturality.**  A multiplicative map that intertwines the derivations and pulls back the trace
also pulls back the cocycle. -/
theorem traceDerivCocycle_comp {τA : A →+ K} {DA : A →+ A} {τB : B →+ K} {DB : B →+ B}
    (f : A →+ B) (hmul : ∀ a a' : A, f (a * a') = f a * f a')
    (hD : ∀ a : A, DB (f a) = f (DA a)) (hτ : ∀ a : A, τB (f a) = τA a) (a b : A) :
    traceDerivCocycle τB DB (f a) (f b) = traceDerivCocycle τA DA a b := by
  simp only [traceDerivCocycle]
  rw [hD b, ← hmul a (DA b), hτ (a * DA b)]

/-- **Non-erasure of the left argument.**  A comparison satisfying the transport hypotheses cannot
kill an element on which the source cocycle is nonzero. -/
theorem ne_zero_of_traceDerivCocycle_ne_zero_left {τA : A →+ K} {DA : A →+ A} {τB : B →+ K}
    {DB : B →+ B} (f : A →+ B) (hmul : ∀ a a' : A, f (a * a') = f a * f a')
    (hD : ∀ a : A, DB (f a) = f (DA a)) (hτ : ∀ a : A, τB (f a) = τA a) {a b : A}
    (hab : traceDerivCocycle τA DA a b ≠ 0) : f a ≠ 0 := by
  intro hfa
  apply hab
  rw [← traceDerivCocycle_comp f hmul hD hτ a b, hfa, traceDerivCocycle_zero_left]

/-- **Non-erasure of the right argument.** -/
theorem ne_zero_of_traceDerivCocycle_ne_zero_right {τA : A →+ K} {DA : A →+ A} {τB : B →+ K}
    {DB : B →+ B} (f : A →+ B) (hmul : ∀ a a' : A, f (a * a') = f a * f a')
    (hD : ∀ a : A, DB (f a) = f (DA a)) (hτ : ∀ a : A, τB (f a) = τA a) {a b : A}
    (hab : traceDerivCocycle τA DA a b ≠ 0) : f b ≠ 0 := by
  intro hfb
  apply hab
  rw [← traceDerivCocycle_comp f hmul hD hτ a b, hfb, traceDerivCocycle_zero_right]

/-- **Transported nonvanishing.**  The target cocycle is nonzero on the image of any pair carrying
a nonzero source value. -/
theorem traceDerivCocycle_image_ne_zero {τA : A →+ K} {DA : A →+ A} {τB : B →+ K} {DB : B →+ B}
    (f : A →+ B) (hmul : ∀ a a' : A, f (a * a') = f a * f a')
    (hD : ∀ a : A, DB (f a) = f (DA a)) (hτ : ∀ a : A, τB (f a) = τA a) {a b : A}
    (hab : traceDerivCocycle τA DA a b ≠ 0) :
    traceDerivCocycle τB DB (f a) (f b) ≠ 0 := by
  rw [traceDerivCocycle_comp f hmul hD hτ a b]
  exact hab

end GaloisForLFunctions.HTGeometry
