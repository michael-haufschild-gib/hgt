import Mathlib

/-!
# Uniform limits of all derivatives

If a sequence of smooth functions on the line converges uniformly together with every one of its
derivatives, the limit is smooth and its derivatives are the limits.  This is the completeness
statement underlying every Fréchet space of smooth functions; mathlib has the one-step version
(`hasDerivAt_of_tendstoUniformlyOn`) but not the iterated one.

* `hasDerivAt_limit_of_tendstoUniformly` : each limit differentiates to the next.
* `iteratedDeriv_limit` : the limits are the iterated derivatives of the first.
* `contDiff_of_tendstoUniformly_iteratedDeriv` : **the limit is smooth.**
-/

namespace GaloisForLFunctions

open Filter Topology
open scoped ContDiff

variable {F : ℕ → ℝ → ℂ} {G : ℕ → ℝ → ℂ}

/-- Every finite order is below the smooth order. -/
theorem natLt_infty (r : ℕ) : ((r : ℕ) : WithTop ℕ∞) < ∞ := by
  exact_mod_cast WithTop.coe_lt_coe.2 (ENat.coe_lt_top r)

/-- **Each limit differentiates to the next.** -/
theorem hasDerivAt_limit_of_tendstoUniformly
    (hFsmooth : ∀ n, ContDiff ℝ ∞ (F n))
    (hconv : ∀ r, TendstoUniformly (fun n => iteratedDeriv r (F n)) (G r) atTop)
    (r : ℕ) (x : ℝ) : HasDerivAt (G r) (G (r + 1) x) x := by
  refine hasDerivAt_of_tendstoUniformly (f := fun n => iteratedDeriv r (F n))
    (f' := fun n z => iteratedDeriv (r + 1) (F n) z) (g := G r) (g' := G (r + 1))
    (hconv (r + 1)) ?_ ?_ x
  · refine Filter.Eventually.of_forall fun n z => ?_
    have hdiff : Differentiable ℝ (iteratedDeriv r (F n)) :=
      (hFsmooth n).differentiable_iteratedDeriv r (natLt_infty r)
    have hd := (hdiff z).hasDerivAt
    rwa [← iteratedDeriv_succ] at hd
  · intro z
    exact (hconv r).tendsto_at z

/-- **The limits are the iterated derivatives of the first.** -/
theorem iteratedDeriv_limit
    (hFsmooth : ∀ n, ContDiff ℝ ∞ (F n))
    (hconv : ∀ r, TendstoUniformly (fun n => iteratedDeriv r (F n)) (G r) atTop) :
    ∀ r, iteratedDeriv r (G 0) = G r := by
  intro r
  induction r with
  | zero => exact iteratedDeriv_zero
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_limit_of_tendstoUniformly hFsmooth hconv k x).deriv

/-- Every limit is smooth of every finite order. -/
theorem contDiff_limit_nat
    (hFsmooth : ∀ n, ContDiff ℝ ∞ (F n))
    (hconv : ∀ r, TendstoUniformly (fun n => iteratedDeriv r (F n)) (G r) atTop) :
    ∀ (m : ℕ) (r : ℕ), ContDiff ℝ (m : WithTop ℕ∞) (G r) := by
  intro m
  induction m with
  | zero =>
    intro r
    have hcont : Continuous (G r) := by
      refine (hconv r).continuous (Filter.Eventually.frequently ?_)
      exact Filter.Eventually.of_forall fun n =>
        ((hFsmooth n).differentiable_iteratedDeriv r (natLt_infty r)).continuous
    simpa using (contDiff_zero (𝕜 := ℝ) (f := G r)).2 hcont
  | succ k ih =>
    intro r
    have hcast : (((k + 1 : ℕ)) : WithTop ℕ∞) = ((k : ℕ) : WithTop ℕ∞) + 1 := by
      push_cast
      ring
    rw [hcast, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_limit_of_tendstoUniformly hFsmooth hconv r x).differentiableAt,
      fun hw => absurd hw (by simp), ?_⟩
    have hderiv : deriv (G r) = G (r + 1) := by
      funext x
      exact (hasDerivAt_limit_of_tendstoUniformly hFsmooth hconv r x).deriv
    rw [hderiv]
    exact ih (r + 1)

/-- **The uniform limit of smooth functions with all derivatives converging uniformly is
smooth.** -/
theorem contDiff_of_tendstoUniformly_iteratedDeriv
    (hFsmooth : ∀ n, ContDiff ℝ ∞ (F n))
    (hconv : ∀ r, TendstoUniformly (fun n => iteratedDeriv r (F n)) (G r) atTop) :
    ContDiff ℝ ∞ (G 0) := by
  rw [contDiff_infty]
  intro m
  exact contDiff_limit_nat hFsmooth hconv m 0

end GaloisForLFunctions
