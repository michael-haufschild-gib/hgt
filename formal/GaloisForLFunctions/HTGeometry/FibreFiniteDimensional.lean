import GaloisForLFunctions.HTGeometry.FibreDimensionCalculus
import GaloisForLFunctions.HTGeometry.FreeFibreDimension

/-!
# The fibres over the base line are finite dimensional

```text
finiteDimensional_freeFibre          from the basis of the free fibre
finiteDimensional_quotient_X_sub_C   the quotient by the ideal of a point is the base field
finiteDimensional_quotient_sup       so any further quotient of it is finite dimensional
finiteDimensional_cyclicFibre        ** hence so is the fibre of a cyclic module **
```

These are the side conditions the additivity lemmas carry: `finrank` is only additive across a
product when the factors are finite dimensional.  Each fibre here is: the free one has an explicit
basis, and the cyclic one is a quotient of `K[X] ⧸ (X - lam)`, which is the base field.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open Module Polynomial

variable {K : Type*} [Field K]

instance finiteDimensional_freeFibre (lam : K) (n : ℕ) :
    FiniteDimensional K ((Fin n →₀ K[X]) ⧸
      (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] (Fin n →₀ K[X])))) :=
  Module.Finite.of_basis (freeFibreBasis lam n)

instance finiteDimensional_quotient_X_sub_C (lam : K) :
    FiniteDimensional K (K[X] ⧸ Ideal.span {(X - C lam : K[X])}) :=
  Module.Finite.equiv (Polynomial.quotientSpanXSubCAlgEquiv lam).symm.toLinearEquiv

instance finiteDimensional_quotient_sup (q : K[X]) (lam : K) :
    FiniteDimensional K (K[X] ⧸ (Ideal.span {q} ⊔ Ideal.span {(X - C lam : K[X])})) := by
  have hle : Ideal.span {(X - C lam : K[X])}
      ≤ Ideal.span {q} ⊔ Ideal.span {(X - C lam : K[X])} := le_sup_right
  refine Module.Finite.of_surjective
    ((Submodule.mapQ (Ideal.span {(X - C lam : K[X])})
      (Ideal.span {q} ⊔ Ideal.span {(X - C lam : K[X])}) LinearMap.id hle).restrictScalars K) ?_
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H z => exact ⟨Submodule.Quotient.mk z, rfl⟩

instance finiteDimensional_cyclicFibre (q : K[X]) (lam : K) :
    FiniteDimensional K ((K[X] ⧸ Ideal.span {q}) ⧸
      (Ideal.span {(X - C lam : K[X])} •
        (⊤ : Submodule K[X] (K[X] ⧸ Ideal.span {q})))) :=
  Module.Finite.equiv ((quotSMulTopIdealEquiv (Ideal.span {q})
    (Ideal.span {(X - C lam : K[X])})).restrictScalars K).symm

end GaloisForLFunctions.HTGeometry
