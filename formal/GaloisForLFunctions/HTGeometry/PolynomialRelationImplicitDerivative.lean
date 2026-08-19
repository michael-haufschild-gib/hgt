/-
# Implicit differentiation of a polynomial relation along a curve

A quantity which is not a rational function of its parameters, but satisfies a polynomial relation
with differentiable coefficients, still has a computable derivative: differentiating the relation
along a curve gives a linear equation for it, solvable wherever the derivative in the unknown does
not vanish.

This is the differential half of the elimination step: it converts a vanishing tangential gradient
into the vanishing of an explicit polynomial expression in the parameters and the unknown.

Main results:
* `hasDerivAt_polyCurve` — the derivative of a polynomial relation along a curve.
* `polyCurve_relation` — **the implicit relation between the two partial derivatives**.
* `deriv_eq_of_polyCurve` — **the solved form**.
* `hasDerivAt_homogeneous_scaling` — **Euler's relation along the radial curve**.
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ} {a : ℕ → ℝ → ℝ} {a' : ℕ → ℝ} {u : ℝ → ℝ} {u' s : ℝ}

/-- The derivative of a polynomial expression whose coefficients and unknown both move. -/
theorem hasDerivAt_polyCurve (ha : ∀ n, HasDerivAt (a n) (a' n) s) (hu : HasDerivAt u u' s) :
    HasDerivAt (fun t => ∑ n ∈ Finset.range m, a n t * (u t) ^ n)
      ((∑ n ∈ Finset.range m, a' n * (u s) ^ n)
        + (∑ n ∈ Finset.range m, (n : ℝ) * a n s * (u s) ^ (n - 1)) * u') s := by
  have hterm : ∀ n ∈ Finset.range m, HasDerivAt (fun t => a n t * (u t) ^ n)
      (a' n * (u s) ^ n + a n s * ((n : ℝ) * (u s) ^ (n - 1) * u')) s := by
    intro n _
    exact (ha n).mul (hu.pow n)
  have hsum := HasDerivAt.sum hterm
  have hfun : (∑ n ∈ Finset.range m, fun t => a n t * (u t) ^ n)
      = fun t => ∑ n ∈ Finset.range m, a n t * (u t) ^ n := by
    funext t
    exact Finset.sum_apply t (Finset.range m) _
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  rw [Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **The implicit relation.**  If the polynomial relation holds along the curve, the two partial
derivatives are linked. -/
theorem polyCurve_relation (ha : ∀ n, HasDerivAt (a n) (a' n) s) (hu : HasDerivAt u u' s)
    (hzero : ∀ᶠ t in 𝓝 s, ∑ n ∈ Finset.range m, a n t * (u t) ^ n = 0) :
    (∑ n ∈ Finset.range m, a' n * (u s) ^ n)
      + (∑ n ∈ Finset.range m, (n : ℝ) * a n s * (u s) ^ (n - 1)) * u' = 0 := by
  have h1 := hasDerivAt_polyCurve (m := m) ha hu
  have heq : (fun t => ∑ n ∈ Finset.range m, a n t * (u t) ^ n) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := hzero
  have h2 : HasDerivAt (fun t => ∑ n ∈ Finset.range m, a n t * (u t) ^ n) 0 s :=
    (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq
  exact h1.unique h2

/-- **The solved form.**  Where the derivative in the unknown does not vanish, the derivative of the
unknown along the curve is determined. -/
theorem deriv_eq_of_polyCurve (ha : ∀ n, HasDerivAt (a n) (a' n) s) (hu : HasDerivAt u u' s)
    (hzero : ∀ᶠ t in 𝓝 s, ∑ n ∈ Finset.range m, a n t * (u t) ^ n = 0)
    (hne : (∑ n ∈ Finset.range m, (n : ℝ) * a n s * (u s) ^ (n - 1)) ≠ 0) :
    u' = -(∑ n ∈ Finset.range m, a' n * (u s) ^ n)
        / (∑ n ∈ Finset.range m, (n : ℝ) * a n s * (u s) ^ (n - 1)) := by
  have h := polyCurve_relation (m := m) ha hu hzero
  field_simp
  linarith [h]

/-- **Euler's relation along the radial curve.**  A positively homogeneous function of degree one
has radial derivative equal to its own value. -/
theorem hasDerivAt_homogeneous_scaling {E : Type*} [AddCommGroup E] [Module ℝ E]
    {φ : E → ℝ} (hhom : ∀ r : ℝ, 0 < r → ∀ x : E, φ (r • x) = r * φ x) (x : E) :
    HasDerivAt (fun t : ℝ => φ ((1 + t) • x)) (φ x) 0 := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (0 : ℝ) < 1 + t := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have habs := abs_lt.mp ht
    linarith [habs.1]
  have heq : (fun t : ℝ => φ ((1 + t) • x)) =ᶠ[𝓝 (0 : ℝ)] fun t : ℝ => (1 + t) * φ x := by
    filter_upwards [hev] with t ht
    exact hhom (1 + t) ht x
  have hbase : HasDerivAt (fun t : ℝ => (1 + t) * φ x) (φ x) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (1 : ℝ)
    simpa using h1.mul_const (φ x)
  exact hbase.congr_of_eventuallyEq heq

end

end GaloisForLFunctions.HTGeometry
