/-
# The spherical derivative — first brick of the Marty/Zalcman normality layer

The `J_c` natural boundary for nonexceptional interior `c` needs **density of repelling periodic
points in `J_c`**, whose analytic engine is **Montel's three-value theorem** (the fundamental
normality test). The standard from-scratch route to it runs through *spherical normality*: Marty's
criterion (a family is normal iff its spherical derivatives are locally bounded) and Zalcman's
rescaling lemma. mathlib has none of this layer.

This file lays its foundation: the **spherical derivative** `σf(z) = ‖f'(z)‖ / (1 + ‖f z‖²)`, the
infinitesimal `ℂ̂`-distortion of `f`. Its defining property is **inversion-invariance**
`σ(1/f) = σf` (the round metric on `ℂ̂` is invariant under `z ↦ 1/z`), which is exactly what makes the
spherical derivative — and hence Marty normality — well-defined across `∞`. We also record
non-negativity and continuity (the input to the compactness step of Marty's criterion).

New file (Montel/Julia lane — spherical normality foundation). General lemmas; Mathlib only.
-/
import Mathlib

open Complex

namespace Bottcher

/-- **Spherical derivative** `σf(z) = ‖f'(z)‖ / (1 + ‖f z‖²)`: the infinitesimal distortion of `f`
measured in the round (chordal) metric of the Riemann sphere `ℂ̂`. -/
noncomputable def sphericalDeriv (f : ℂ → ℂ) (z : ℂ) : ℝ := ‖deriv f z‖ / (1 + ‖f z‖ ^ 2)

/-- The spherical derivative is non-negative. -/
theorem sphericalDeriv_nonneg (f : ℂ → ℂ) (z : ℂ) : 0 ≤ sphericalDeriv f z := by
  unfold sphericalDeriv; positivity

/-- The spherical derivative is bounded above by the ordinary derivative norm. -/
theorem sphericalDeriv_le_norm_deriv (f : ℂ → ℂ) (z : ℂ) :
    sphericalDeriv f z ≤ ‖deriv f z‖ := by
  unfold sphericalDeriv
  have hdenpos : 0 < (1 : ℝ) + ‖f z‖ ^ 2 := by positivity
  rw [div_le_iff₀ hdenpos]
  nlinarith [sq_nonneg ‖f z‖, norm_nonneg (deriv f z)]

/-- **Inversion-invariance** `σ(1/f) = σf` — the characteristic symmetry of the spherical derivative.
Because the round metric on `ℂ̂` is invariant under `z ↦ 1/z`, the distortion of `1/f` equals that of
`f` (wherever `f ≠ 0`). This is what lets the spherical derivative, and Marty's normality criterion
built on it, extend across `∞`. -/
theorem sphericalDeriv_inv {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) (hfz : f z ≠ 0) :
    sphericalDeriv (fun w => (f w)⁻¹) z = sphericalDeriv f z := by
  unfold sphericalDeriv
  have hderiv : deriv (fun w => (f w)⁻¹) z = -deriv f z / (f z) ^ 2 :=
    (hf.hasDerivAt.inv hfz).deriv
  rw [hderiv, norm_div, norm_neg, norm_pow, norm_inv, inv_pow]
  have hfz' : ‖f z‖ ≠ 0 := norm_ne_zero_iff.mpr hfz
  have hb : ‖f z‖ ^ 2 ≠ 0 := pow_ne_zero 2 hfz'
  have hd : (1 : ℝ) + ‖f z‖ ^ 2 ≠ 0 := by positivity
  have hd2 : (1 : ℝ) + (‖f z‖ ^ 2)⁻¹ ≠ 0 := by positivity
  field_simp
  ring

/-- The spherical derivative of a function with continuous value and continuous derivative is
continuous (the denominator `1 + ‖f‖²` never vanishes). This feeds the compactness step of Marty's
criterion: a locally-bounded `σf` attains a finite sup on compact sets. -/
theorem continuous_sphericalDeriv {f : ℂ → ℂ} (hf : Continuous f) (hf' : Continuous (deriv f)) :
    Continuous (sphericalDeriv f) := by
  unfold sphericalDeriv
  exact hf'.norm.div (continuous_const.add (hf.norm.pow 2))
    (fun z => (by positivity : (0 : ℝ) < 1 + ‖f z‖ ^ 2).ne')

end Bottcher
