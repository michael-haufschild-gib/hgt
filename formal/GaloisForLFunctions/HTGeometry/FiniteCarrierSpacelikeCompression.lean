import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite-carrier spacelike compression debt

Two independently variable copies of a finite-dimensional carrier `V` have tensor carrier
`V ⊗[K] V`. Any linear compression of this tensor square back into `V` loses at least

`finrank K V * finrank K V - finrank K V`

dimensions. The bound is exact for surjective compressions. In particular, no carrier of dimension
at least two can encode its tensor square injectively back into itself.

This is the finite-capacity monoidal boundary left open by
`EventNetworkFixedCarrier.lean`: algebraic direct sums preserve arbitrary typed sequential
composition, while faithful independent self-composition forces tensor-product capacity. The
result is elementary rank-nullity infrastructure, not new scientific knowledge.
-/

namespace GaloisForLFunctions.HTGeometry

open Module
open scoped TensorProduct

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/--
Every linear compression of two independent copies back into the same finite carrier loses at
least `d² - d` dimensions, where `d = finrank K V`.
-/
theorem finiteCarrierTensorCompression_kernel_lower_bound
    (μ : (V ⊗[K] V) →ₗ[K] V) :
    finrank K V * finrank K V - finrank K V ≤
      finrank K (LinearMap.ker μ) := by
  have hRankNullity := μ.finrank_range_add_finrank_ker
  rw [Module.finrank_tensorProduct] at hRankNullity
  have hRange :
      finrank K (LinearMap.range μ) ≤ finrank K V :=
    (LinearMap.range μ).finrank_le
  omega

/-- A finite carrier of dimension at least two cannot faithfully contain its tensor square. -/
theorem finiteCarrierTensorCompression_not_injective
    (hV : 2 ≤ finrank K V)
    (μ : (V ⊗[K] V) →ₗ[K] V) :
    ¬ Function.Injective μ := by
  intro hμ
  have hDim := μ.finrank_le_finrank_of_injective hμ
  rw [Module.finrank_tensorProduct] at hDim
  have hPositive : 0 < finrank K V := by omega
  have hOne : 1 < finrank K V := by omega
  have hStrict :
      finrank K V < finrank K V * finrank K V :=
    lt_mul_of_one_lt_right hPositive hOne
  exact (not_lt_of_ge hDim) hStrict

/-- An injective self-compression of a finite tensor square forces carrier dimension at most one. -/
theorem finiteCarrierTensorCompression_injective_finrank_le_one
    (μ : (V ⊗[K] V) →ₗ[K] V)
    (hμ : Function.Injective μ) :
    finrank K V ≤ 1 := by
  by_contra h
  have hV : 2 ≤ finrank K V := by omega
  exact finiteCarrierTensorCompression_not_injective hV μ hμ

/-- A surjective tensor-square compression has exactly the minimal kernel dimension `d² - d`. -/
theorem finiteCarrierTensorCompression_kernel_eq_of_surjective
    (μ : (V ⊗[K] V) →ₗ[K] V)
    (hμ : Function.Surjective μ) :
    finrank K (LinearMap.ker μ) =
      finrank K V * finrank K V - finrank K V := by
  have hRankNullity := μ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hμ, Module.finrank_tensorProduct] at hRankNullity
  simp only [finrank_top] at hRankNullity
  omega

/-- In particular, a finite carrier linearly equivalent to its tensor square has dimension at most one. -/
theorem finiteCarrierTensorSelfEquiv_finrank_le_one
    (e : (V ⊗[K] V) ≃ₗ[K] V) :
    finrank K V ≤ 1 :=
  finiteCarrierTensorCompression_injective_finrank_le_one e.toLinearMap e.injective

end GaloisForLFunctions.HTGeometry
