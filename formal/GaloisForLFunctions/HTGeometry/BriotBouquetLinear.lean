import GaloisForLFunctions.HTGeometry.BriotBouquetPoincare

/-!
# The linear case of the Briot–Bouquet classification

An entire solution of the autonomous equation `f′ = a f + b` is `−b/a + c·exp(a z)` when `a ≠ 0`,
and affine when `a = 0`.  This is the degree-`≤ 1` case of the Briot–Bouquet normal form, and the
case in which the classification follows from an integrating factor rather than from the geometry of
the associated algebraic curve: multiplying by `exp(−a z)` turns the equation into the statement that
a derivative vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- **The kernel of `d/dz − a`.**  An entire solution of `f′ = a f` is a constant multiple of
`exp (a z)`. -/
theorem eq_exp_of_deriv_eq_const_mul {a : ℂ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ z, deriv f z = a * f z) (z : ℂ) : f z = f 0 * Complex.exp (a * z) := by
  have hderiv : ∀ w : ℂ, HasDerivAt (fun w : ℂ => f w * Complex.exp (-(a * w))) 0 w := by
    intro w
    have h1 : HasDerivAt f (a * f w) w := by
      have := (hf w).hasDerivAt
      rwa [h w] at this
    have h2 : HasDerivAt (fun x : ℂ => -(a * x)) (-a) w := by
      simpa [neg_mul] using (hasDerivAt_id w).const_mul (-a)
    have h4 := h1.mul h2.cexp
    have hz : a * f w * Complex.exp (-(a * w)) + f w * (Complex.exp (-(a * w)) * -a) = 0 := by ring
    rwa [hz] at h4
  have hgdiff : Differentiable ℂ fun w : ℂ => f w * Complex.exp (-(a * w)) :=
    fun w => (hderiv w).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hgdiff (fun w => (hderiv w).deriv) z 0
  simp only [mul_zero, neg_zero, Complex.exp_zero, mul_one] at hconst
  have hmul := congrArg (fun t => t * Complex.exp (a * z)) hconst
  simp only [mul_assoc, ← Complex.exp_add] at hmul
  simpa using hmul

/-- **The affine case is affine.**  An entire solution of `f′ = b` is `f 0 + b z`. -/
theorem eq_affine_of_deriv_eq_const {b : ℂ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ z, deriv f z = b) (z : ℂ) : f z = f 0 + b * z := by
  have hderiv : ∀ w : ℂ, HasDerivAt (fun w : ℂ => f w - b * w) 0 w := by
    intro w
    have h1 : HasDerivAt f b w := by
      have := (hf w).hasDerivAt
      rwa [h w] at this
    have h2 : HasDerivAt (fun x : ℂ => b * x) b w := by
      simpa using (hasDerivAt_id w).const_mul b
    have h3 : HasDerivAt (fun w : ℂ => f w - b * w) (b - b) w := h1.sub h2
    rwa [sub_self] at h3
  have hgdiff : Differentiable ℂ fun w : ℂ => f w - b * w :=
    fun w => (hderiv w).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hgdiff (fun w => (hderiv w).deriv) z 0
  simp only [mul_zero, sub_zero] at hconst
  linear_combination hconst

/-- **The Briot–Bouquet normal form in the linear case.**  An entire solution of `f′ = a f + b`
with `a ≠ 0` is `briotBouquetMap a 0 (f 0 + b/a) (−b/a)`. -/
theorem eq_briotBouquetMap_of_deriv_eq_affine {a b : ℂ} (ha : a ≠ 0) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h : ∀ z, deriv f z = a * f z + b) :
    f = briotBouquetMap a 0 (f 0 + b / a) (-(b / a)) := by
  set g : ℂ → ℂ := fun w => f w + b / a with hg
  have hgdiff : Differentiable ℂ g := hf.add_const _
  have hgderiv : ∀ z, deriv g z = a * g z := by
    intro z
    have : deriv g z = deriv f z := by
      rw [hg]
      exact deriv_add_const _
    rw [this, h z, hg]
    field_simp
  have hkey := fun z => eq_exp_of_deriv_eq_const_mul hgdiff hgderiv z
  funext z
  have hz := hkey z
  have h0 : g 0 = f 0 + b / a := rfl
  rw [h0] at hz
  have hfz : f z + b / a = (f 0 + b / a) * Complex.exp (a * z) := hz
  rw [briotBouquetMap]
  simp only [add_zero]
  linear_combination hfz

/-- The solution is nonconstant exactly when the exponential coefficient does not vanish. -/
theorem briotBouquet_coeff_ne_zero_of_ne {a b : ℂ} (ha : a ≠ 0) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h : ∀ z, deriv f z = a * f z + b) {z : ℂ} (hne : f z ≠ f 0) :
    f 0 + b / a ≠ 0 := by
  intro hzero
  have heq := congrFun (eq_briotBouquetMap_of_deriv_eq_affine ha hf h)
  have hz := heq z
  have h0 := heq 0
  rw [briotBouquetMap, hzero] at hz h0
  simp only [zero_mul, add_zero, add_zero] at hz h0
  exact hne (by rw [hz, h0])

end GaloisForLFunctions.HTGeometry
