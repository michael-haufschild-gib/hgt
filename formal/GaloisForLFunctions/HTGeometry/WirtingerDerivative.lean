import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Wirtinger derivatives

A real-linear map `ℂ →L[ℝ] ℂ` splits uniquely as `v ↦ a * v + b * conj v`.  The coefficients are
the Wirtinger parts

`a = (f' 1 - i · f' i)/2`,   `b = (f' 1 + i · f' i)/2`,

and applying them to the real Fréchet derivative of a function gives the operators `∂` and `∂̄`.
The antiholomorphic part vanishes exactly for the complex-linear maps, so `∂̄f = 0` is the
Cauchy–Riemann condition and `∂f` is then the complex derivative.

The one computation everything downstream uses is the derivative of `f` along a curve: for a
real curve `γ` through `z`,

`(f ∘ γ)'(t) = ∂f(z) · γ'(t) + ∂̄f(z) · conj γ'(t)`.

* `HTGeometry.wirtingerHol`, `HTGeometry.wirtingerAntihol` : the two parts of a real-linear map.
* `HTGeometry.wirtinger_decomp` : `f' v = ∂ · v + ∂̄ · conj v`.
* `HTGeometry.wirtingerAntihol_eq_zero_iff` : `∂̄ = 0` is complex linearity.
* `HTGeometry.dz`, `HTGeometry.dzbar` : the operators `∂` and `∂̄` on functions.
* `HTGeometry.hasDerivAt_comp_wirtinger` : the derivative along a curve.
-/

open Complex

namespace HTGeometry

section LinearParts

/-- The holomorphic Wirtinger part of a real-linear endomorphism of `ℂ`. -/
noncomputable def wirtingerHol (f' : ℂ →L[ℝ] ℂ) : ℂ :=
  (f' 1 - Complex.I * f' Complex.I) / 2

/-- The antiholomorphic Wirtinger part of a real-linear endomorphism of `ℂ`. -/
noncomputable def wirtingerAntihol (f' : ℂ →L[ℝ] ℂ) : ℂ :=
  (f' 1 + Complex.I * f' Complex.I) / 2

/-- **The Wirtinger decomposition.**  A real-linear map is multiplication by its holomorphic part
plus multiplication of the conjugate by its antiholomorphic part. -/
theorem wirtinger_decomp (f' : ℂ →L[ℝ] ℂ) (v : ℂ) :
    f' v = wirtingerHol f' * v + wirtingerAntihol f' * (starRingEnd ℂ) v := by
  have key : ((v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I) = v := by
    simp [Complex.real_smul]
  have hcv : (starRingEnd ℂ) v = (v.re : ℂ) - (v.im : ℂ) * Complex.I := by
    simp [Complex.ext_iff]
  rw [wirtingerHol, wirtingerAntihol, ← key, map_add, map_smul, map_smul, Complex.real_smul,
    Complex.real_smul, key, hcv]
  set A : ℂ := (v.re : ℂ) with hA
  set B : ℂ := (v.im : ℂ) with hB
  have hv : v = A + B * Complex.I := by rw [hA, hB]; exact (Complex.re_add_im v).symm
  rw [hv]
  linear_combination B * (f' Complex.I) * Complex.I_sq

theorem wirtingerHol_add_wirtingerAntihol (f' : ℂ →L[ℝ] ℂ) :
    wirtingerHol f' + wirtingerAntihol f' = f' 1 := by
  rw [wirtingerHol, wirtingerAntihol]; ring

@[simp] theorem wirtingerHol_smul (c : ℂ) (f' : ℂ →L[ℝ] ℂ) :
    wirtingerHol (c • f') = c * wirtingerHol f' := by
  simp only [wirtingerHol, smul_apply, smul_eq_mul]; ring

@[simp] theorem wirtingerAntihol_smul (c : ℂ) (f' : ℂ →L[ℝ] ℂ) :
    wirtingerAntihol (c • f') = c * wirtingerAntihol f' := by
  simp only [wirtingerAntihol, smul_apply, smul_eq_mul]; ring

@[simp] theorem wirtingerHol_add (f' g' : ℂ →L[ℝ] ℂ) :
    wirtingerHol (f' + g') = wirtingerHol f' + wirtingerHol g' := by
  simp only [wirtingerHol, add_apply]; ring

@[simp] theorem wirtingerAntihol_add (f' g' : ℂ →L[ℝ] ℂ) :
    wirtingerAntihol (f' + g') = wirtingerAntihol f' + wirtingerAntihol g' := by
  simp only [wirtingerAntihol, add_apply]; ring

/-- **The antiholomorphic part vanishes exactly on complex-linear maps.**  This is the
Cauchy–Riemann condition in Wirtinger form. -/
theorem wirtingerAntihol_eq_zero_iff (f' : ℂ →L[ℝ] ℂ) :
    wirtingerAntihol f' = 0 ↔ ∀ v : ℂ, f' v = wirtingerHol f' * v := by
  constructor
  · intro h v
    rw [wirtinger_decomp f' v, h, zero_mul, add_zero]
  · intro h
    have h1 := h Complex.I
    rw [wirtingerHol] at h1
    rw [wirtingerAntihol]
    have := h 1
    rw [wirtingerHol] at this
    have h2 : f' 1 = (f' 1 - Complex.I * f' Complex.I) / 2 := by simpa using this
    linear_combination h2

end LinearParts

section Operators

variable (f : ℂ → ℂ)

/-- The Wirtinger operator `∂`. -/
noncomputable def dz (z : ℂ) : ℂ := wirtingerHol (fderiv ℝ f z)

/-- The Wirtinger operator `∂̄`. -/
noncomputable def dzbar (z : ℂ) : ℂ := wirtingerAntihol (fderiv ℝ f z)

variable {f}

theorem dz_eq_of_hasFDerivAt {f' : ℂ →L[ℝ] ℂ} {z : ℂ} (h : HasFDerivAt f f' z) :
    dz f z = wirtingerHol f' := by rw [dz, h.fderiv]

theorem dzbar_eq_of_hasFDerivAt {f' : ℂ →L[ℝ] ℂ} {z : ℂ} (h : HasFDerivAt f f' z) :
    dzbar f z = wirtingerAntihol f' := by rw [dzbar, h.fderiv]

/-- The real Fréchet derivative of a complex-differentiable function is multiplication by its
complex derivative. -/
theorem fderiv_real_apply_of_differentiableAt {z : ℂ} (h : DifferentiableAt ℂ f z) (v : ℂ) :
    fderiv ℝ f z v = deriv f z * v := by
  rw [h.fderiv_restrictScalars ℝ]
  show (fderiv ℂ f z) v = deriv f z * v
  rw [show v = v • (1 : ℂ) by simp, map_smul]
  simp only [smul_eq_mul, mul_one]
  rw [mul_comm]
  rfl

/-- **A complex-differentiable function has vanishing `∂̄`, and `∂` is its complex derivative.** -/
theorem dzbar_eq_zero_of_differentiableAt {z : ℂ} (h : DifferentiableAt ℂ f z) :
    dzbar f z = 0 ∧ dz f z = deriv f z := by
  constructor
  · rw [dzbar, wirtingerAntihol, fderiv_real_apply_of_differentiableAt h 1,
      fderiv_real_apply_of_differentiableAt h Complex.I]
    linear_combination (deriv f z / 2) * Complex.I_sq
  · rw [dz, wirtingerHol, fderiv_real_apply_of_differentiableAt h 1,
      fderiv_real_apply_of_differentiableAt h Complex.I]
    linear_combination (-(deriv f z) / 2) * Complex.I_sq

end Operators

section Curve

/-- **The derivative of a function along a real curve, in Wirtinger form.** -/
theorem hasDerivAt_comp_wirtinger {f : ℂ → ℂ} {f' : ℂ →L[ℝ] ℂ} {γ : ℝ → ℂ} {γ' : ℂ} {t : ℝ}
    (hf : HasFDerivAt f f' (γ t)) (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => f (γ s))
      (wirtingerHol f' * γ' + wirtingerAntihol f' * (starRingEnd ℂ) γ') t := by
  have h := hf.comp_hasDerivAt t hγ
  rwa [wirtinger_decomp f' γ'] at h


/-- **Uniqueness of the Wirtinger decomposition.** -/
theorem wirtinger_ext {a b c d : ℂ}
    (h : ∀ v : ℂ, a * v + b * (starRingEnd ℂ) v = c * v + d * (starRingEnd ℂ) v) :
    a = c ∧ b = d := by
  have h1 := h 1
  have h2 := h Complex.I
  simp only [map_one, mul_one, Complex.conj_I] at h1 h2
  have hsum : a + b = c + d := h1
  have hdiff : a * Complex.I - b * Complex.I = c * Complex.I - d * Complex.I := by
    linear_combination h2
  have hI : (a - b) * Complex.I = (c - d) * Complex.I := by
    rw [sub_mul, sub_mul]; exact hdiff
  have hab : a - b = c - d := mul_right_cancel₀ Complex.I_ne_zero hI
  constructor
  · linear_combination (hsum + hab) / 2
  · linear_combination (hsum - hab) / 2

/-- **Precomposition with the reflection `t ↦ z − t`.** -/
theorem hasFDerivAt_comp_const_sub {g : ℂ → ℂ} {g' : ℂ →L[ℝ] ℂ} {z w : ℂ}
    (hg : HasFDerivAt g g' (z - w)) :
    HasFDerivAt (fun t => g (z - t)) ((-1 : ℂ) • g') w := by
  have hsub : HasFDerivAt (fun t : ℂ => z - t) (-(ContinuousLinearMap.id ℝ ℂ)) w := by
    simpa using (hasFDerivAt_id w).const_sub z
  have hcomp := hg.comp w hsub
  have hEq : g'.comp (-(ContinuousLinearMap.id ℝ ℂ)) = (-1 : ℂ) • g' := by
    ext v
    simp
  rwa [hEq] at hcomp

/-- The reflection negates `∂̄`. -/
theorem dzbar_comp_const_sub {g : ℂ → ℂ} (hg : Differentiable ℝ g) (z w : ℂ) :
    dzbar (fun t => g (z - t)) w = -dzbar g (z - w) := by
  rw [dzbar_eq_of_hasFDerivAt (hasFDerivAt_comp_const_sub (hg (z - w)).hasFDerivAt),
    wirtingerAntihol_smul, dzbar]
  ring

/-- The reflection negates `∂`. -/
theorem dz_comp_const_sub {g : ℂ → ℂ} (hg : Differentiable ℝ g) (z w : ℂ) :
    dz (fun t => g (z - t)) w = -dz g (z - w) := by
  rw [dz_eq_of_hasFDerivAt (hasFDerivAt_comp_const_sub (hg (z - w)).hasFDerivAt),
    wirtingerHol_smul, dz]
  ring

end Curve

end HTGeometry
