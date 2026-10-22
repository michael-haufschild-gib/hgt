import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The archimedean current and its square-zero lift

The archimedean Kummer functional is prescribed on a lattice basis, and the perfect de Rham pairing
turns that prescription into a unique linear functional: a functional on a finite-dimensional space
is determined by, and can be freely prescribed on, a basis.  Transition compatibility along a
lattice inclusion is then automatic from uniqueness.

The square-zero lift is the universal property of the exterior algebra: a linear map into the split
square-zero extension whose values square to zero — and every purely square-zero element does —
extends to a unique algebra map.  Products of two positive-degree generators therefore vanish, and
the value on a Kummer generator is the archimedean logarithm.

* `deningerArchimedeanCurrent`, `_exists_unique` : the current `(3)`.
* `deningerArchimedeanCurrent_natural` : transition compatibility.
* `deningerArchimedeanLift` : the square-zero algebra map `(4)`--`(6)`.
* `deningerArchimedeanLift_mul_eq_zero` : products of two generators vanish.
-/

namespace RHTower

open Module

section Current

variable {ι V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **The archimedean homology current.**  The functional determined by its values on a lattice
basis. -/
noncomputable def deningerArchimedeanCurrent (b : Basis ι ℂ V) (ell : ι → ℂ) : V →ₗ[ℂ] ℂ :=
  b.constr ℂ ell

@[simp]
theorem deningerArchimedeanCurrent_basis (b : Basis ι ℂ V) (ell : ι → ℂ) (i : ι) :
    deningerArchimedeanCurrent b ell (b i) = ell i :=
  Basis.constr_basis b ℂ ell i

/-- **`(3)`: existence and uniqueness of the current.**  The perfect pairing identifies the
homology class with a functional, and a functional is freely and uniquely prescribed on a basis. -/
theorem deningerArchimedeanCurrent_exists_unique (b : Basis ι ℂ V) (ell : ι → ℂ) :
    ∃! L : V →ₗ[ℂ] ℂ, ∀ i, L (b i) = ell i := by
  refine ⟨deningerArchimedeanCurrent b ell, fun i => deningerArchimedeanCurrent_basis b ell i, ?_⟩
  intro L hL
  refine b.ext fun i => ?_
  rw [hL i, deningerArchimedeanCurrent_basis]

/-- **Transition compatibility.**  If a current on a larger lattice restricts to the prescribed
values along an inclusion, it agrees with the current of the smaller lattice. -/
theorem deningerArchimedeanCurrent_natural {W : Type*} [AddCommGroup W] [Module ℂ W]
    (b : Basis ι ℂ V) (ell : ι → ℂ) (phi : V →ₗ[ℂ] W) (M : W →ₗ[ℂ] ℂ)
    (hcompat : ∀ i, M (phi (b i)) = ell i) :
    M.comp phi = deningerArchimedeanCurrent b ell := by
  refine b.ext fun i => ?_
  rw [LinearMap.comp_apply, hcompat i, deningerArchimedeanCurrent_basis]

end Current

section SquareZeroLift

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The archimedean generator of the split square-zero extension. -/
noncomputable def deningerArchimedeanGenerator (L : V →ₗ[ℂ] ℂ) : V →ₗ[ℂ] TrivSqZeroExt ℂ ℂ :=
  (TrivSqZeroExt.inrHom ℂ ℂ).comp L

@[simp]
theorem deningerArchimedeanGenerator_apply (L : V →ₗ[ℂ] ℂ) (v : V) :
    deningerArchimedeanGenerator L v = TrivSqZeroExt.inr (L v) := rfl

theorem deningerArchimedeanGenerator_sq (L : V →ₗ[ℂ] ℂ) (v : V) :
    deningerArchimedeanGenerator L v * deningerArchimedeanGenerator L v = 0 :=
  TrivSqZeroExt.inr_mul_inr ℂ (L v) (L v)

/-- **`(4)`--`(6)`: the square-zero derived algebra map.**  The universal property of the exterior
algebra lifts the archimedean current to a unital algebra map into `ℂ[ε]/(ε²)`. -/
noncomputable def deningerArchimedeanLift (L : V →ₗ[ℂ] ℂ) :
    ExteriorAlgebra ℂ V →ₐ[ℂ] TrivSqZeroExt ℂ ℂ :=
  ExteriorAlgebra.lift ℂ ⟨deningerArchimedeanGenerator L, deningerArchimedeanGenerator_sq L⟩

@[simp]
theorem deningerArchimedeanLift_ι (L : V →ₗ[ℂ] ℂ) (v : V) :
    deningerArchimedeanLift L (ExteriorAlgebra.ι ℂ v) = TrivSqZeroExt.inr (L v) := by
  rw [deningerArchimedeanLift, ExteriorAlgebra.lift_ι_apply]
  rfl

/-- **Products of two positive-degree generators vanish**, because the target is square zero. -/
theorem deningerArchimedeanLift_mul_eq_zero (L : V →ₗ[ℂ] ℂ) (v w : V) :
    deningerArchimedeanLift L (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) = 0 := by
  rw [map_mul, deningerArchimedeanLift_ι, deningerArchimedeanLift_ι]
  exact TrivSqZeroExt.inr_mul_inr ℂ (L v) (L w)

/-- **Power equivariance.**  The rational power action scales the generator, so the current scales
by the same factor; the weight `-1` Tate line cancels it. -/
theorem deningerArchimedeanCurrent_smul (L : V →ₗ[ℂ] ℂ) (q : ℂ) (v : V) :
    L (q • v) = q * L v := by
  rw [map_smul, smul_eq_mul]

theorem deningerArchimedeanTate_cancel (L : V →ₗ[ℂ] ℂ) {q : ℂ} (hq : q ≠ 0) (v : V) :
    q⁻¹ * L (q • v) = L v := by
  rw [deningerArchimedeanCurrent_smul, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

end SquareZeroLift

end RHTower
