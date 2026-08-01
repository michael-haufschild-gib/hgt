import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Smoothness of a uniform limit of all derivatives

If every iterated derivative of a sequence of smooth functions on the line converges uniformly,
the limit is smooth and its iterated derivatives are the limits.  mathlib has the one-derivative
statement (`hasDerivAt_of_tendstoUniformly`) but nothing at all orders, which is what completeness
of a space of test functions needs.

The argument is a chain: uniform convergence at order `m + 1` together with pointwise convergence
at order `m` makes the limit at order `m` differentiable with derivative the limit at order
`m + 1`.  Such a chain of derivatives forces smoothness by induction on the order.

* `hasDerivAt_of_tendstoUniformly_iteratedDeriv` : the chain.
* `contDiff_infty_of_hasDerivAt_chain` : a chain of derivatives is smooth.
* `contDiff_infty_of_tendstoUniformly_iteratedDeriv` : the limit is smooth, with
  `iteratedDeriv_eq_of_tendstoUniformly_iteratedDeriv` identifying its derivatives.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

section SmoothLimit

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A chain of derivatives: each member is differentiable with the next as its derivative. -/
theorem contDiff_of_hasDerivAt_chain {g : ℕ → ℝ → F}
    (h : ∀ (m : ℕ) (x : ℝ), HasDerivAt (g m) (g (m + 1) x) x) (n m : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞) (g m) := by
  induction n generalizing m with
  | zero =>
      rw [Nat.cast_zero, contDiff_zero]
      have hdiff : Differentiable ℝ (g m) := fun x => (h m x).differentiableAt
      exact hdiff.continuous
  | succ n ih =>
      have hd : deriv (g m) = g (m + 1) := funext fun x => (h m x).deriv
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
        push_cast
        ring
      rw [hcast, contDiff_succ_iff_deriv]
      refine ⟨fun x => (h m x).differentiableAt, ?_, ?_⟩
      · intro htop
        exact absurd htop (by simp)
      · rw [hd]
        exact ih (m + 1)

/-- **A chain of derivatives is smooth.** -/
theorem contDiff_infty_of_hasDerivAt_chain {g : ℕ → ℝ → F}
    (h : ∀ (m : ℕ) (x : ℝ), HasDerivAt (g m) (g (m + 1) x) x) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (g m) :=
  contDiff_infty.mpr fun n => contDiff_of_hasDerivAt_chain h n m

/-- Along a chain of derivatives, the `m`-th iterated derivative of the first member is the
`m`-th member. -/
theorem iteratedDeriv_of_hasDerivAt_chain {g : ℕ → ℝ → F}
    (h : ∀ (m : ℕ) (x : ℝ), HasDerivAt (g m) (g (m + 1) x) x) (m : ℕ) :
    iteratedDeriv m (g 0) = g m := by
  induction m with
  | zero => rw [iteratedDeriv_zero]
  | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      exact funext fun x => (h m x).deriv

/-- **The chain produced by uniform convergence of all derivatives.**  If every iterated
derivative of a sequence of smooth functions converges uniformly, the limits form a chain of
derivatives. -/
theorem hasDerivAt_of_tendstoUniformly_iteratedDeriv {f : ℕ → ℝ → F} {g : ℕ → ℝ → F}
    (hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hconv : ∀ m, TendstoUniformly (fun n => iteratedDeriv m (f n)) (g m) atTop)
    (m : ℕ) (x : ℝ) : HasDerivAt (g m) (g (m + 1) x) x := by
  refine hasDerivAt_of_tendstoUniformly (hconv (m + 1)) ?_ ((hconv m).tendsto_at) x
  refine Filter.Eventually.of_forall fun n y => ?_
  have hlt : ((m : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast ENat.coe_lt_top m
  have hdiff : Differentiable ℝ (iteratedDeriv m (f n)) :=
    (hsmooth n).differentiable_iteratedDeriv m hlt
  rw [iteratedDeriv_succ]
  exact (hdiff y).hasDerivAt

/-- **The uniform limit of all derivatives is smooth.** -/
theorem contDiff_infty_of_tendstoUniformly_iteratedDeriv {f : ℕ → ℝ → F} {g : ℕ → ℝ → F}
    (hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hconv : ∀ m, TendstoUniformly (fun n => iteratedDeriv m (f n)) (g m) atTop) :
    ContDiff ℝ (⊤ : ℕ∞) (g 0) :=
  contDiff_infty_of_hasDerivAt_chain
    (hasDerivAt_of_tendstoUniformly_iteratedDeriv hsmooth hconv) 0

/-- **The derivatives of the limit are the limits of the derivatives.** -/
theorem iteratedDeriv_eq_of_tendstoUniformly_iteratedDeriv {f : ℕ → ℝ → F} {g : ℕ → ℝ → F}
    (hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hconv : ∀ m, TendstoUniformly (fun n => iteratedDeriv m (f n)) (g m) atTop) (m : ℕ) :
    iteratedDeriv m (g 0) = g m :=
  iteratedDeriv_of_hasDerivAt_chain
    (hasDerivAt_of_tendstoUniformly_iteratedDeriv hsmooth hconv) m

end SmoothLimit

end GaloisForLFunctions.HTGeometry
