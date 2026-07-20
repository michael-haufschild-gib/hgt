import Mathlib.Tactic

/-!
# Halving additive reflection cocycles

Over a field of characteristic zero, every additive cocycle for a reflection is the coboundary of
its half. Consequently a value which changes by such a cocycle has a canonical reflection-fixed
centering, and centered invariance is exactly equivalent to the original value relation.

This is the divisible-coefficient counterpart to the integral parity obstruction in
`ReflectionTateAnomaly`: complex-valued reflection defects cannot retain that two-torsion anomaly.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X K : Type*} [Field K]

/-- An additive cocycle for a reflection acts by sign under reflection. -/
def IsAdditiveReflectionCocycle (r : X → X) (c : X → K) : Prop :=
  ∀ x, c (r x) = -c x

/-- The defect of any value under an involution is an additive reflection cocycle. -/
theorem isAdditiveReflectionCocycle_defect
    {r : X → X} (hr : Function.Involutive r) (f : X → K) :
    IsAdditiveReflectionCocycle r (fun x ↦ f (r x) - f x) := by
  intro x
  change f (r (r x)) - f (r x) = -(f (r x) - f x)
  rw [hr x]
  ring

/-- **Characteristic-zero reflection cohomology vanishes.** Every additive reflection cocycle is
the coboundary of its half. -/
theorem half_sub_half_reflection_eq
    [CharZero K] {r : X → X} {c : X → K}
    (hc : IsAdditiveReflectionCocycle r c) (x : X) :
    (1 / 2 : K) * c x - (1 / 2 : K) * c (r x) = c x := by
  rw [hc x]
  ring

/-- A characteristic-zero additive reflection cocycle vanishes on the fixed locus. -/
theorem IsAdditiveReflectionCocycle.eq_zero_of_fixed
    [CharZero K] {r : X → X} {c : X → K}
    (hc : IsAdditiveReflectionCocycle r c) {x : X} (hx : r x = x) :
    c x = 0 := by
  have h := hc x
  rw [hx] at h
  linear_combination (1 / 2 : K) * h

/-- The half-cocycle is the unique anti-invariant primitive of an additive reflection cocycle. -/
theorem eq_half_of_sub_reflection_eq
    [CharZero K] {r : X → X} {c b : X → K}
    (hb : IsAdditiveReflectionCocycle r b)
    (hboundary : ∀ x, b x - b (r x) = c x) (x : X) :
    b x = (1 / 2 : K) * c x := by
  have h := hboundary x
  rw [hb x] at h
  linear_combination (1 / 2 : K) * h

/-- **Exact half-centering interface.** Centered reflection invariance is equivalent to the
original value changing by the prescribed additive cocycle. -/
theorem add_half_reflection_fixed_iff
    [CharZero K] {r : X → X} {f c : X → K}
    (hc : IsAdditiveReflectionCocycle r c) (x : X) :
    f (r x) + (1 / 2 : K) * c (r x) = f x + (1 / 2 : K) * c x ↔
      f (r x) = f x + c x := by
  rw [hc x]
  constructor <;> intro h <;> linear_combination h

/-- Half-centering trivializes every additive reflection value law. -/
theorem add_half_reflection_fixed
    [CharZero K] {r : X → X} {f c : X → K}
    (hc : IsAdditiveReflectionCocycle r c)
    (hvalue : ∀ x, f (r x) = f x + c x) (x : X) :
    f (r x) + (1 / 2 : K) * c (r x) = f x + (1 / 2 : K) * c x :=
  (add_half_reflection_fixed_iff hc x).2 (hvalue x)

end


end GaloisForLFunctions.HTGeometry
