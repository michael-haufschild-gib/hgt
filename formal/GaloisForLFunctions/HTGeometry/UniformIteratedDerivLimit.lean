import Mathlib

/-!
# Smoothness of a uniform limit of all iterated derivatives

If every member of a sequence of functions on the line is smooth and, for every order, the
sequence of iterated derivatives of that order converges uniformly, then the limits form a chain of
derivatives: the order-`m` limit is differentiable with derivative the order-`(m+1)` limit.  Hence
the order-zero limit is smooth and its iterated derivatives are exactly the limits.

* `hasDerivAt_of_tendstoUniformly_iteratedDeriv` : the chain of derivatives.
* `contDiff_infty_of_tendstoUniformly_iteratedDeriv` : the limit is smooth.
* `iteratedDeriv_eq_of_tendstoUniformly_iteratedDeriv` : its derivatives are the limits.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

section UniformIteratedDeriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {f : ℕ → ℝ → F} {g : ℕ → ℝ → F}

omit [CompleteSpace F] in
/-- The uniform limits form a chain of derivatives. -/
theorem hasDerivAt_of_tendstoUniformly_iteratedDeriv
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hg : ∀ m, TendstoUniformly (fun n => iteratedDeriv m (f n)) (g m) Filter.atTop)
    (m : ℕ) (x : ℝ) : HasDerivAt (g m) (g (m + 1) x) x := by
  refine hasDerivAt_of_tendstoUniformlyOn (l := Filter.atTop) (s := Set.univ)
    (f := fun n => iteratedDeriv m (f n))
    (f' := fun n => fun y => iteratedDeriv (m + 1) (f n) y)
    (g := g m) (g' := g (m + 1)) isOpen_univ ?_ ?_ ?_ (Set.mem_univ x)
  · exact (hg (m + 1)).tendstoUniformlyOn
  · refine Filter.Eventually.of_forall fun n y _ => ?_
    have hdiff : Differentiable ℝ (iteratedDeriv m (f n)) :=
      (hf n).differentiable_iteratedDeriv m (by exact_mod_cast ENat.coe_lt_top m)
    rw [iteratedDeriv_succ]
    exact (hdiff y).hasDerivAt
  · exact fun y _ => (hg m).tendsto_at y

omit [CompleteSpace F] in
theorem continuous_of_tendstoUniformly_iteratedDeriv
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hg : ∀ m, TendstoUniformly (fun n => iteratedDeriv m (f n)) (g m) Filter.atTop) (m : ℕ) :
    Continuous (g m) :=
  (hg m).continuous (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
    (hf n).continuous_iteratedDeriv m (by exact_mod_cast (ENat.coe_lt_top m).le)))

omit [CompleteSpace F] in
theorem contDiff_nat_of_tendstoUniformly_iteratedDeriv
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hg : ∀ m, TendstoUniformly (fun n => iteratedDeriv m (f n)) (g m) Filter.atTop) :
    ∀ (k m : ℕ), ContDiff ℝ k (g m) := by
  intro k
  induction k with
  | zero => intro m; exact contDiff_zero.2 (continuous_of_tendstoUniformly_iteratedDeriv hf hg m)
  | succ k ih =>
      intro m
      have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
      rw [hcast, contDiff_succ_iff_deriv]
      refine ⟨fun x => (hasDerivAt_of_tendstoUniformly_iteratedDeriv hf hg m x).differentiableAt,
        ?_, ?_⟩
      · intro hcon
        exact absurd hcon (by simp)
      · have hderiv : deriv (g m) = g (m + 1) :=
          funext fun x => (hasDerivAt_of_tendstoUniformly_iteratedDeriv hf hg m x).deriv
        rw [hderiv]
        exact ih (m + 1)

omit [CompleteSpace F] in
/-- **The uniform limit of a smooth sequence with all uniformly convergent derivatives is
smooth.** -/
theorem contDiff_infty_of_tendstoUniformly_iteratedDeriv
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hg : ∀ m, TendstoUniformly (fun n => iteratedDeriv m (f n)) (g m) Filter.atTop) :
    ContDiff ℝ (⊤ : ℕ∞) (g 0) :=
  contDiff_infty.2 fun k => contDiff_nat_of_tendstoUniformly_iteratedDeriv hf hg k 0

omit [CompleteSpace F] in
/-- **Its iterated derivatives are exactly the uniform limits.** -/
theorem iteratedDeriv_eq_of_tendstoUniformly_iteratedDeriv
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hg : ∀ m, TendstoUniformly (fun n => iteratedDeriv m (f n)) (g m) Filter.atTop) :
    ∀ m, iteratedDeriv m (g 0) = g m := by
  intro m
  induction m with
  | zero => rw [iteratedDeriv_zero]
  | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      exact funext fun x => (hasDerivAt_of_tendstoUniformly_iteratedDeriv hf hg m x).deriv

end UniformIteratedDeriv

end GaloisForLFunctions.HTGeometry
