import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Base change of the algebra trace and of the discriminant

For a finite free algebra `B` over a commutative ring `A` and any `A`-algebra `A'`, multiplication
by `1 ⊗ x` on `A' ⊗[A] B` is the base change of multiplication by `x` on `B`.  Hence the algebra
trace and the discriminant of a basis both commute with base change:

```text
trace A' (A' ⊗[A] B) (1 ⊗ x)  = algebraMap A A' (trace A B x)
discr A' (e.baseChange A')     = algebraMap A A' (discr A e)
```

The discriminant statement is the transport device used to move an étale hypothesis between
different base fields: over an algebraically closed field the discriminant of a split family is a
unit, and a unit is preserved by any ring homomorphism.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

section BaseChange

variable (A A' B : Type*) [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B] [Module.Free A B] [Module.Finite A B]

omit [Module.Free A B] [Module.Finite A B] in
/-- Multiplication by `1 ⊗ x` is the base change of multiplication by `x`. -/
theorem lmul_baseChange (x : B) :
    (Algebra.lmul A B x).baseChange A' = Algebra.lmul A' (A' ⊗[A] B) (1 ⊗ₜ x) := by
  ext b
  simp [Algebra.lmul, Algebra.TensorProduct.tmul_mul_tmul]

/-- **The algebra trace commutes with base change.** -/
theorem trace_tensor_one (x : B) :
    Algebra.trace A' (A' ⊗[A] B) (1 ⊗ₜ x) = algebraMap A A' (Algebra.trace A B x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← lmul_baseChange A A' B x,
    LinearMap.trace_baseChange]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The discriminant commutes with base change.** -/
theorem discr_baseChange (e : Module.Basis ι A B) :
    Algebra.discr A' (e.baseChange A' : Module.Basis ι A' (A' ⊗[A] B)) =
      algebraMap A A' (Algebra.discr A e) := by
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, Module.Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact trace_tensor_one A A' B _

end BaseChange

end GaloisForLFunctions.HTGeometry
