import GaloisForLFunctions.RHTower.Deninger.DeningerRelationKernelTransgression

/-!
# Hasse descent through the Baumslag relation kernel

A normalized cocycle on a rational vector group is globally a coboundary exactly when a primitive
on its free rational cover vanishes on every relation.  Equivalently, failure of global descent is
detected on some relation by every cover primitive.  The relation kernel acts here as a family of
local obstruction probes.
-/

namespace RHTower

open DeningerNormalizedCocycle

section RelationKernelHasse

variable {ι A M : Type}
  [AddCommGroup A] [Module ℚ A] [AddCommGroup M]

/-- A cocycle is globally a coboundary exactly when it has a free-cover primitive trivial on every
arithmetic relation. -/
theorem deningerBauFree_isCoboundary_iff_exists_relation_trivial_primitive
    (basis : Module.Basis ι ℚ A)
    (c : DeningerNormalizedCocycle (Multiplicative A) M) :
    c.IsCoboundary ↔
      ∃ b : DeningerBau (FreeGroup ι) → M,
        (c.pullback (deningerBauFreeMap (⇑basis))).IsPrimitive b ∧
          ∀ k : (deningerBauFreeMap (⇑basis)).ker, b k = 0 := by
  constructor
  · intro hc
    exact exists_primitive_kernelTransgression_eq_one_of_isCoboundary
      c (deningerBauFreeMap (⇑basis)) hc
  · rintro ⟨b, hb, hker⟩
    exact isCoboundary_of_kernelTransgression_eq_one
      c (deningerBauFreeMap (⇑basis))
      (deningerBauFree_surjective (⇑basis) basis.span_eq) hb hker

/-- Failure of global coboundary descent is equivalent to every free-cover primitive carrying a
nonzero obstruction on at least one arithmetic relation. -/
theorem deningerBauFree_not_isCoboundary_iff_every_primitive_detected_on_relation
    (basis : Module.Basis ι ℚ A)
    (c : DeningerNormalizedCocycle (Multiplicative A) M) :
    ¬ c.IsCoboundary ↔
      ∀ b : DeningerBau (FreeGroup ι) → M,
        (c.pullback (deningerBauFreeMap (⇑basis))).IsPrimitive b →
          ∃ k : (deningerBauFreeMap (⇑basis)).ker, b k ≠ 0 := by
  rw [deningerBauFree_isCoboundary_iff_exists_relation_trivial_primitive basis c]
  push Not
  rfl

end RelationKernelHasse

end RHTower
