/-
The square Hilbert--Schmidt kernel layer is the rectangular one with equal index types.

`IsHS (K : ι × ι → ℂ)` and `IsHSRect (K : κ × ι → ℂ)` are the same predicate
`Summable fun p => ‖K p‖ ^ 2`, the two norms are the same square root, and the two represented
operators are the same `LinearMap.mkContinuous` datum.  So at `κ = ι` the rectangular layer *is*
the square layer, and everything proved only on the rectangular side transfers.

What the square side was missing:

* `toOperator_eq_zero_iff`, `toOperator_ne_zero_iff` — the kernel-to-operator bridge is
  nondegenerate: the represented operator vanishes exactly when the kernel does;
* `isHS_rectTranspose` — the transpose of a square Hilbert--Schmidt kernel is Hilbert--Schmidt.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRectangular

namespace HilbertSchmidt

variable {ι : Type*}

/-- Square-summability of a square kernel is square-summability of it as a rectangular one. -/
theorem isHS_iff_isHSRect (K : ι × ι → ℂ) : IsHS K ↔ IsHSRect K := Iff.rfl

/-- A square Hilbert--Schmidt kernel is a rectangular Hilbert--Schmidt kernel. -/
theorem IsHS.toIsHSRect {K : ι × ι → ℂ} (hK : IsHS K) : IsHSRect K := hK

@[simp] theorem hsNormSq_eq_hsNormSqRect (K : ι × ι → ℂ) : hsNormSq K = hsNormSqRect K := rfl

@[simp] theorem hsNorm_eq_hsNormRect (K : ι × ι → ℂ) : hsNorm K = hsNormRect K := rfl

/-- **The two represented operators are the same operator.** -/
theorem toOperator_eq_toOperatorRect {K : ι × ι → ℂ} (hK : IsHS K) :
    toOperator hK = toOperatorRect hK.toIsHSRect := rfl

/-- **The square kernel-to-operator bridge is nondegenerate.**  The represented operator vanishes
exactly when the kernel does. -/
theorem toOperator_eq_zero_iff {K : ι × ι → ℂ} (hK : IsHS K) :
    toOperator hK = 0 ↔ K = 0 := by
  rw [toOperator_eq_toOperatorRect hK]
  exact toOperatorRect_eq_zero_iff hK.toIsHSRect

/-- Nondegeneracy in the contrapositive form. -/
theorem toOperator_ne_zero_iff {K : ι × ι → ℂ} (hK : IsHS K) :
    toOperator hK ≠ 0 ↔ K ≠ 0 :=
  not_congr (toOperator_eq_zero_iff hK)

/-- The transpose of a square Hilbert--Schmidt kernel is Hilbert--Schmidt. -/
theorem isHS_rectTranspose {K : ι × ι → ℂ} (hK : IsHS K) : IsHS (rectTranspose K) :=
  isHSRect_transpose hK.toIsHSRect

end HilbertSchmidt
