import GaloisForLFunctions.HTGeometry.SeibergWitten.Geometry

/-!
# Pointwise `Spinᶜ` Clifford infrastructure

This file supplies the exact four-dimensional Clifford relations between positive and negative
rank-two complex spinor fibers.  Combined with `SmoothSpinCBundlePrelude`, it is the local algebra
needed by a genuine `Spinᶜ` bundle.  `SeibergWitten.PrincipalSpinC` now supplies the algebraic
principal lift; its association to these fibers and smooth determinant compatibility remain a
distinct implementation layer.
-/

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Pointwise Clifford multiplication for a four-dimensional `Spinᶜ` spinor pair. -/
structure PointwiseSpinCCliffordData
    (M : Type u) (SPlus SMinus : M → Type v)
    [∀ x, AddCommGroup (SPlus x)] [∀ x, Module ℂ (SPlus x)]
    [∀ x, AddCommGroup (SMinus x)] [∀ x, Module ℂ (SMinus x)] where
  cliffordPlus : ∀ x, FourSpace → SPlus x →ₗ[ℂ] SMinus x
  cliffordMinus : ∀ x, FourSpace → SMinus x →ₗ[ℂ] SPlus x
  positiveClifford : ∀ x v w,
    (cliffordMinus x v).comp (cliffordPlus x w) +
        (cliffordMinus x w).comp (cliffordPlus x v) =
      ((-2 * inner ℝ v w : ℝ) : ℂ) • LinearMap.id
  negativeClifford : ∀ x v w,
    (cliffordPlus x v).comp (cliffordMinus x w) +
        (cliffordPlus x w).comp (cliffordMinus x v) =
      ((-2 * inner ℝ v w : ℝ) : ℂ) • LinearMap.id

/-- The positive-fiber Clifford relation exposed as a closed reusable theorem. -/
theorem PointwiseSpinCCliffordData.positive_relation
    {M : Type u} {SPlus SMinus : M → Type v}
    [∀ x, AddCommGroup (SPlus x)] [∀ x, Module ℂ (SPlus x)]
    [∀ x, AddCommGroup (SMinus x)] [∀ x, Module ℂ (SMinus x)]
    (data : PointwiseSpinCCliffordData M SPlus SMinus) (x : M) (v w : FourSpace) :
    (data.cliffordMinus x v).comp (data.cliffordPlus x w) +
        (data.cliffordMinus x w).comp (data.cliffordPlus x v) =
      ((-2 * inner ℝ v w : ℝ) : ℂ) • LinearMap.id :=
  data.positiveClifford x v w

/-- The negative-fiber Clifford relation exposed as a closed reusable theorem. -/
theorem PointwiseSpinCCliffordData.negative_relation
    {M : Type u} {SPlus SMinus : M → Type v}
    [∀ x, AddCommGroup (SPlus x)] [∀ x, Module ℂ (SPlus x)]
    [∀ x, AddCommGroup (SMinus x)] [∀ x, Module ℂ (SMinus x)]
    (data : PointwiseSpinCCliffordData M SPlus SMinus) (x : M) (v w : FourSpace) :
    (data.cliffordPlus x v).comp (data.cliffordMinus x w) +
        (data.cliffordPlus x w).comp (data.cliffordMinus x v) =
      ((-2 * inner ℝ v w : ℝ) : ℂ) • LinearMap.id :=
  data.negativeClifford x v w

end GaloisForLFunctions.HTGeometry.SeibergWitten
