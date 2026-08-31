import Mathlib

/-!
# The dimension criterion for injectivity

```text
ker_eq_bot_of_finrank_quotient_range   ** the quotient by the image having the dimension
                                          rank-nullity predicts for an injective map forces
                                          injectivity **
injective_of_finrank_quotient_range
```

This is the linear-algebra core of the Hilbert-function criterion for a linear form to be a
nonzerodivisor on a graded ring: in each degree, multiplication by the form is a map from one graded
piece to the next, and the quotient is the corresponding piece of the ring modulo the form.  When the
dimensions add up exactly, no kernel is left in that degree.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- **The dimension criterion for injectivity.**  If the quotient by the image has exactly the
dimension the rank-nullity formula predicts for an injective map, the map is injective. -/
theorem ker_eq_bot_of_finrank_quotient_range [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W)
    (h : finrank K (W ⧸ LinearMap.range f) + finrank K V = finrank K W) :
    LinearMap.ker f = ⊥ := by
  have h1 : finrank K (W ⧸ LinearMap.range f) + finrank K (LinearMap.range f) = finrank K W :=
    Submodule.finrank_quotient_add_finrank _
  have h2 : finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V :=
    LinearMap.finrank_range_add_finrank_ker f
  have h3 : finrank K (LinearMap.range f) = finrank K V := by omega
  have h4 : finrank K (LinearMap.ker f) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp h4

/-- The same statement as injectivity. -/
theorem injective_of_finrank_quotient_range [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W)
    (h : finrank K (W ⧸ LinearMap.range f) + finrank K V = finrank K W) :
    Function.Injective f :=
  LinearMap.ker_eq_bot.mp (ker_eq_bot_of_finrank_quotient_range f h)

end GaloisForLFunctions.HTGeometry
