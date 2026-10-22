import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Flow purity for a weight-graded conformal flow

A flow acting on reduced leafwise degree `n` as `e^{nt/2}` times a unitary has three elementary
consequences, all independent of the geometry that produces it: it scales norms by `e^{nt/2}`, its
unitary parts form a group, and every eigenvector of its generator has eigenvalue of real part
`n/2`.  The last is the critical-line purity statement, and it needs no infinitesimal generator:
comparing the two expressions for the norm of the flowed eigenvector already forces the real part.

The weight-one twisted form is the same computation for a positive form scaling by `e^t`: the
centered flow preserves it exactly.

Finally, on an oriented real surface leaf the degree-one Hodge operator squares to `-1`, so
composing it with coefficient conjugation gives an anti-linear operator of square `-1` whose cup
trace against a form is the sum of the squared norms of the real and imaginary parts, hence
positive.

* `deningerFlowPurity_norm`, `deningerFlowPurity_unitaryGroup` : the weight law and the group law.
* `deningerFlowPurity_re_eq` : `Re λ = n/2`.
* `deningerTwistedFlow_centered` : the centered weight-one flow preserves the positive form.
* `deningerLeafHodgeJ_sq`, `deningerLeafHodgeJ_conjLinear`, `deningerLeafHodgeJ_pos` : the odd
  leafwise Hodge operator.
-/

namespace RHTower

section FlowPurity

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- **The weight law.**  A flow acting as `e^{nt/2}` times a unitary scales norms by `e^{nt/2}`. -/
theorem deningerFlowPurity_norm {n : ℕ} {T U : ℝ → H →L[ℂ] H}
    (hT : ∀ t x, T t x = ((Real.exp ((n : ℝ) * t / 2) : ℝ) : ℂ) • U t x)
    (hU : ∀ t x, ‖U t x‖ = ‖x‖) (t : ℝ) (x : H) :
    ‖T t x‖ = Real.exp ((n : ℝ) * t / 2) * ‖x‖ := by
  rw [hT, norm_smul, hU]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- **The unitary parts form a group.**  The scalar factor is nonzero, so the group law of the
flow descends to the unitary parts. -/
theorem deningerFlowPurity_unitaryGroup {n : ℕ} {T U : ℝ → H →L[ℂ] H}
    (hT : ∀ t x, T t x = ((Real.exp ((n : ℝ) * t / 2) : ℝ) : ℂ) • U t x)
    (hgroup : ∀ t s x, T (t + s) x = T t (T s x)) (t s : ℝ) (x : H) :
    U (t + s) x = U t (U s x) := by
  have hscal : ((Real.exp ((n : ℝ) * (t + s) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.exp_pos _)
  have hkey : ((Real.exp ((n : ℝ) * (t + s) / 2) : ℝ) : ℂ) • U (t + s) x
      = ((Real.exp ((n : ℝ) * (t + s) / 2) : ℝ) : ℂ) • U t (U s x) := by
    rw [← hT, hgroup t s x, hT, hT, map_smul, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  exact smul_right_injective H hscal hkey

/-- **Purity.**  If the flow acts on an eigenvector of its generator by `e^{tλ}`, then the weight
law forces `Re λ = n/2`.  No infinitesimal generator and no Stone theorem are needed. -/
theorem deningerFlowPurity_re_eq {n : ℕ} {T U : ℝ → H →L[ℂ] H}
    (hT : ∀ t x, T t x = ((Real.exp ((n : ℝ) * t / 2) : ℝ) : ℂ) • U t x)
    (hU : ∀ t x, ‖U t x‖ = ‖x‖) {x : H} (hx : x ≠ 0) {lam : ℂ}
    (heig : ∀ t : ℝ, T t x = Complex.exp ((t : ℂ) * lam) • x) :
    lam.re = (n : ℝ) / 2 := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h1 : Real.exp (lam.re) * ‖x‖ = Real.exp ((n : ℝ) / 2) * ‖x‖ := by
    have hleft : ‖T 1 x‖ = Real.exp (lam.re) * ‖x‖ := by
      rw [heig 1, norm_smul, Complex.norm_exp]
      congr 2
      simp
    have hright := deningerFlowPurity_norm hT hU 1 x
    rw [hleft] at hright
    rw [hright]
    congr 2
    ring
  have h2 : Real.exp (lam.re) = Real.exp ((n : ℝ) / 2) :=
    mul_right_cancel₀ hnorm h1
  exact Real.exp_eq_exp.mp h2

end FlowPurity

section TwistedWeightOne

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- **The centered weight-one flow preserves the positive form.**  If the harmonic form scales by
`e^t`, then `e^{-t/2}` times the flow is an isometry of that form; this is the finite form of
`Θ₁ = 1/2 + S` with `S` skew. -/
theorem deningerTwistedFlow_centered {h : H →ₗ[ℝ] H →ₗ[ℝ] ℝ} {T : ℝ → H →ₗ[ℝ] H}
    (hscale : ∀ t x y, h (T t x) (T t y) = Real.exp t * h x y) (t : ℝ) (x y : H) :
    h (Real.exp (-t / 2) • T t x) (Real.exp (-t / 2) • T t y) = h x y := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hscale, ← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  have hzero : -t / 2 + -t / 2 + t = 0 := by ring
  rw [hzero, Real.exp_zero, one_mul]

end TwistedWeightOne

section LeafOddHodge

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The complex structure of the complexified leafwise one-forms: multiplication by `i`. -/
def deningerLeafMulI (a : V × V) : V × V := (-a.2, a.1)

/-- The odd leafwise Hodge operator `J = ⋆ c` on complexified one-forms. -/
def deningerLeafHodgeJ (star : V →ₗ[ℝ] V) (a : V × V) : V × V :=
  (star a.1, -star a.2)

/-- **The odd Hodge operator squares to `-1`.** -/
theorem deningerLeafHodgeJ_sq {star : V →ₗ[ℝ] V} (hstar : ∀ u, star (star u) = -u)
    (a : V × V) :
    deningerLeafHodgeJ star (deningerLeafHodgeJ star a) = -a := by
  refine Prod.ext ?_ ?_
  · show star (star a.1) = -a.1
    rw [hstar]
  · show -star (-star a.2) = -a.2
    rw [map_neg, neg_neg, hstar]

/-- **The odd Hodge operator is anti-linear**: it anticommutes with multiplication by `i`. -/
theorem deningerLeafHodgeJ_conjLinear (star : V →ₗ[ℝ] V) (a : V × V) :
    deningerLeafHodgeJ star (deningerLeafMulI a)
      = -deningerLeafMulI (deningerLeafHodgeJ star a) := by
  refine Prod.ext ?_ ?_
  · show star (-a.2) = -(-(-star a.2))
    rw [map_neg]
    simp
  · show -star a.1 = -star a.1
    rfl

/-- The complexified cup trace of two one-forms, in real and imaginary parts. -/
def deningerLeafCupTrace (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a b : V × V) : ℝ × ℝ :=
  (T a.1 b.1 - T a.2 b.2, T a.1 b.2 + T a.2 b.1)

/-- **Positivity of the odd Hodge form.**  With the real Hodge identity `T u (⋆v) = ⟪u,v⟫`, the cup
trace of a form against its `J`-image is real and equals the sum of the squared norms of the real
and imaginary parts. -/
theorem deningerLeafHodgeJ_pos {star : V →ₗ[ℝ] V} {T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (hT : ∀ u v : V, T u (star v) = inner ℝ u v) (a : V × V) :
    deningerLeafCupTrace T a (deningerLeafHodgeJ star a)
      = (‖a.1‖ ^ (2 : ℕ) + ‖a.2‖ ^ (2 : ℕ), 0) := by
  refine Prod.ext ?_ ?_
  · show T a.1 (star a.1) - T a.2 (-star a.2) = ‖a.1‖ ^ (2 : ℕ) + ‖a.2‖ ^ (2 : ℕ)
    rw [map_neg, hT, hT, sub_neg_eq_add, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  · show T a.1 (-star a.2) + T a.2 (star a.1) = 0
    rw [map_neg, hT, hT, real_inner_comm]
    ring

/-- The odd Hodge form is strictly positive on nonzero forms. -/
theorem deningerLeafHodgeJ_pos_of_ne {star : V →ₗ[ℝ] V} {T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (hT : ∀ u v : V, T u (star v) = inner ℝ u v) {a : V × V} (ha : a ≠ 0) :
    0 < (deningerLeafCupTrace T a (deningerLeafHodgeJ star a)).1 := by
  rw [deningerLeafHodgeJ_pos hT]
  by_cases h1 : a.1 = 0
  · have h2 : a.2 ≠ 0 := by
      intro h2
      exact ha (Prod.ext h1 h2)
    have hpos : 0 < ‖a.2‖ := norm_pos_iff.mpr h2
    positivity
  · have hpos : 0 < ‖a.1‖ := norm_pos_iff.mpr h1
    positivity

end LeafOddHodge

end RHTower
