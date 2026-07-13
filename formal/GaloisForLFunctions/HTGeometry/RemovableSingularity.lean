import Mathlib

/-!
# Removable singularity from a simple zero

If `f` is differentiable at `a` with `f(a) = 0`, then `s ↦ f(s)/(s-a)` extends continuously across `a`
with limit `f'(a)`:

`f(s)/(s-a) → f'(a)`   as   `s → a`.

This is the workhorse behind polar-cancellation / removable-singularity arguments: when two meromorphic
terms have simple poles at `a` with canceling residues, their sum equals `N(s)/(s-a)` with the analytic
numerator `N` vanishing at `a`, and this lemma reads off the finite boundary value `N'(a)`.
-/

open Filter Topology

namespace HTGeometry

/-- **`f(s)/(s-a) → f'(a)` at a simple zero.**  For `f` differentiable at `a` with `f(a) = 0`, the
quotient `f(s)/(s-a)` has the finite limit `deriv f a` as `s → a` (the removable-singularity value). -/
theorem tendsto_div_sub_of_hasDerivAt_eq_zero {f : ℂ → ℂ} {a : ℂ}
    (hf : DifferentiableAt ℂ f a) (h0 : f a = 0) :
    Tendsto (fun s => f s / (s - a)) (𝓝[≠] a) (𝓝 (deriv f a)) := by
  have hd := hf.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s _
  rw [slope_def_field, h0, sub_zero, div_eq_inv_mul, mul_comm]

end HTGeometry
