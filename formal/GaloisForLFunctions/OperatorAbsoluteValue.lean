/-
# The operator absolute value `|T| = √(T†T)`

The positive square root of the energy operator, through the continuous functional calculus of
the C⋆-algebra of bounded operators on a complex Hilbert space.  The absolute value is positive,
self-adjoint, squares to `T†T`, and is a partial isometry companion of `T` at the metric level:
`‖|T| x‖ = ‖T x‖` for every `x`.  Consequently `|T|` is Hilbert–Schmidt exactly when `T` is, with
the same Hilbert–Schmidt norm, and both share the same energy operator, hence the same singular
values.

Proved here:
* `absOp`, `absOp_nonneg`, `isSelfAdjoint_absOp` — the positive square root `√(T†T)`.
* `absOp_mul_self`, `absOp_comp_self` — `|T|² = T†T = energyOp T`.
* `norm_absOp_apply` — `‖|T| x‖ = ‖T x‖`.
* `isHilbertSchmidt_absOp_iff`, `hsNormSq_absOp` — `|T|` and `T` are simultaneously
  Hilbert–Schmidt with equal norms.
* `energyOp_absOp`, `singVal_absOp` — `|T|` and `T` share energy operator and singular values.
-/
import GaloisForLFunctions.SingularValues
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **absolute value** `|T| = √(T†T)`: the positive square root of the energy operator, via
the continuous functional calculus. -/
noncomputable def absOp (T : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (star T * T)

theorem absOp_nonneg (T : H →L[ℂ] H) : (0 : H →L[ℂ] H) ≤ absOp T := CFC.sqrt_nonneg _

theorem isSelfAdjoint_absOp (T : H →L[ℂ] H) : IsSelfAdjoint (absOp T) :=
  .of_nonneg (absOp_nonneg T)

theorem absOp_mul_self (T : H →L[ℂ] H) : absOp T * absOp T = star T * T :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg T)

/-- The square of the absolute value is the energy operator: `|T| ∘L |T| = T† ∘L T`. -/
theorem absOp_comp_self (T : H →L[ℂ] H) : absOp T ∘L absOp T = energyOp T :=
  absOp_mul_self T

/-- The absolute value is a metric companion of `T`: `‖|T| x‖ = ‖T x‖`. -/
theorem norm_absOp_apply (T : H →L[ℂ] H) (x : H) : ‖absOp T x‖ = ‖T x‖ := by
  have hsym : (absOp T).IsSymmetric :=
    isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_absOp T)
  have h1 : ‖absOp T x‖ ^ 2 = RCLike.re (inner ℂ x ((absOp T ∘L absOp T) x)) := by
    rw [comp_apply, ← inner_self_eq_norm_sq (𝕜 := ℂ) (absOp T x)]
    exact congrArg RCLike.re (hsym x (absOp T x))
  have h2 : ‖T x‖ ^ 2 = RCLike.re (inner ℂ x ((absOp T ∘L absOp T) x)) := by
    rw [absOp_comp_self, re_inner_energyOp_self]
  have h3 : ‖absOp T x‖ ^ 2 = ‖T x‖ ^ 2 := by rw [h1, ← h2]
  nlinarith [norm_nonneg (absOp T x), norm_nonneg (T x)]

/-- `|T|` is Hilbert–Schmidt exactly when `T` is. -/
theorem isHilbertSchmidt_absOp_iff (T : H →L[ℂ] H) :
    (absOp T).IsHilbertSchmidt ↔ T.IsHilbertSchmidt := by
  constructor
  · intro h
    refine isHilbertSchmidt_of_summable (hsBasis ℂ H) ?_
    refine (h.summable (hsBasis ℂ H)).congr fun i => ?_
    rw [norm_absOp_apply]
  · intro h
    refine isHilbertSchmidt_of_summable (hsBasis ℂ H) ?_
    refine (h.summable (hsBasis ℂ H)).congr fun i => ?_
    rw [norm_absOp_apply]

/-- `|T|` and `T` have the same Hilbert–Schmidt norm. -/
theorem hsNormSq_absOp (T : H →L[ℂ] H) : hsNormSq (absOp T) = hsNormSq T := by
  rw [hsNormSq, hsNormSq]
  exact tsum_congr fun i => by rw [norm_absOp_apply]

/-- `|T|` and `T` have the same energy operator. -/
theorem energyOp_absOp (T : H →L[ℂ] H) : energyOp (absOp T) = energyOp T := by
  rw [energyOp,
    show ContinuousLinearMap.adjoint (absOp T) = absOp T from isSelfAdjoint_absOp T]
  exact absOp_comp_self T

/-- `|T|` and `T` share their singular values. -/
theorem singVal_absOp (T : H →L[ℂ] H) (n : ℕ) : singVal (absOp T) n = singVal T n := by
  rw [singVal, singVal, energyOp_absOp]

end ContinuousLinearMap
