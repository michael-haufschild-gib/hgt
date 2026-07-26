import GaloisForLFunctions.RHTower.LocalizationScopeAndGuardrail

/-!
# Exact self-adjointness is unnecessary: asymptotic self-adjointness suffices

The determinant connectors of this development require approximants whose zeros are **all** real —
in the matrix realisations, characteristic polynomials of Hermitian matrices.  Exact hermiticity is
a rigid demand on a construction.  It can be relaxed to a limit.

**Numerical range.**  For an operator `A` on a complex inner product space, every eigenvalue is a
value of the quadratic form `⟨Ax, x⟩` at a unit vector, so its imaginary part is a value of the
quadratic form of the anti-Hermitian part `H = (A - A*)/(2i)`, and Cauchy–Schwarz gives

```text
|Im λ|  ≤  ‖H‖ .
```

So an eigenvalue can only be as far from the real axis as the anti-Hermitian part is large.

**Consequence with the localized transfer.**  Fix a point `z` off the real axis and a ball of radius
`R` about it.  If every zero of the approximant has imaginary part at most `ε` in modulus and
`R + ε < |Im z|`, the approximant is zero-free on that ball.  Since the localized criterion only asks
for zero-freeness on one ball per point, we may let `R` shrink with `z` and `ε` shrink with `n`:

> **The Riemann hypothesis follows from entire approximants converging locally uniformly to `XiC`
> whose zeros have imaginary parts tending uniformly to zero.  Exact reality of the zeros — exact
> self-adjointness of the source — is not needed.**

This is the operator-lane counterpart of the localization: a construction now only has to be
*asymptotically* self-adjoint, a condition stable under perturbation and truncation, rather than
exactly self-adjoint at every stage.

This file formalizes the numerical-range bound, the ball-exclusion step, and the resulting criterion.
-/

open Complex Metric Set Filter Topology

namespace RHTower

section NumericalRange

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Numerical-range bound.**  The quadratic form of a bounded operator at a unit vector has modulus
at most the operator norm. -/
theorem quadratic_form_norm_le (H : E →L[ℂ] E) {x : E} (hx : ‖x‖ = 1) :
    ‖(inner ℂ (H x) x : ℂ)‖ ≤ ‖H‖ := by
  calc ‖(inner ℂ (H x) x : ℂ)‖ ≤ ‖H x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ ‖H‖ * ‖x‖ * ‖x‖ := by
        have := H.le_opNorm x
        nlinarith [norm_nonneg x, norm_nonneg (H x)]
    _ = ‖H‖ := by rw [hx]; ring

/-- **Bendixson's bound.**  If the imaginary part of an eigenvalue is the real part of the quadratic
form of the anti-Hermitian part at a unit eigenvector, it is bounded by that part's norm. -/
theorem im_eigenvalue_le_antiHermitian (H : E →L[ℂ] E) {x : E} (hx : ‖x‖ = 1) {lam : ℂ}
    (hlam : lam.im = (inner ℂ (H x) x : ℂ).re) : |lam.im| ≤ ‖H‖ := by
  rw [hlam]
  exact le_trans (Complex.abs_re_le_norm _) (quadratic_form_norm_le H hx)

end NumericalRange

/-- **Ball exclusion.**  A point whose imaginary part is at most `ε` cannot lie in a ball of radius
`R` about `z` once `R + ε < |Im z|`. -/
theorem not_mem_closedBall_of_small_im {z w : ℂ} {R ε : ℝ}
    (hgap : R + ε < |z.im|) (hw : |w.im| ≤ ε) : w ∉ closedBall z R := by
  intro hmem
  have h := abs_im_ge_of_mem_closedBall hmem
  linarith

/-- **Zero-freeness from small imaginary parts.**  If every zero of `F` has imaginary part at most
`ε`, then `F` is zero-free on any ball with `R + ε < |Im z|`. -/
theorem zeroFree_closedBall_of_small_im {F : ℂ → ℂ} {z : ℂ} {R ε : ℝ}
    (hgap : R + ε < |z.im|) (hzero : ∀ w, F w = 0 → |w.im| ≤ ε) :
    ∀ w ∈ closedBall z R, F w ≠ 0 := by
  intro w hw hwzero
  exact not_mem_closedBall_of_small_im hgap (hzero w hwzero) hw

/-- **Asymptotic self-adjointness suffices.**  Entire approximants converging locally uniformly to
`XiC`, whose zeros have imaginary parts tending uniformly to zero, prove the hypothesis. -/
theorem riemannHypothesis_of_asymptotically_real_zeros
    {Fn : ℕ → ℂ → ℂ} {ε : ℕ → ℝ}
    (hconv : TendstoLocallyUniformly Fn XiC atTop)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hzero : ∀ᶠ n in atTop, ∀ w, Fn n w = 0 → |w.im| ≤ ε n)
    (hε : Tendsto ε atTop (nhds 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pointwise_zeroFree_approximants
  intro z hz
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  refine ⟨Fn, |z.im| / 4, by linarith, hconv, hFn, ?_⟩
  have hsmall : ∀ᶠ n in atTop, ε n < |z.im| / 2 := by
    have := hε.eventually (gt_mem_nhds (show (0:ℝ) < |z.im| / 2 by linarith))
    exact this
  filter_upwards [hzero, hsmall] with n hn hns
  intro w hw
  exact zeroFree_closedBall_of_small_im (z := z) (R := |z.im| / 4) (ε := ε n)
    (by linarith) hn w hw

/-- The exact criterion is the special case `ε = 0`. -/
theorem asymptotic_generalises_exact
    {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformly Fn XiC atTop)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hreal : ∀ᶠ n in atTop, ∀ w, Fn n w = 0 → w.im = 0) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_asymptotically_real_zeros (ε := fun _ => 0) hconv hFn ?_ ?_
  · filter_upwards [hreal] with n hn w hw
    rw [hn w hw]; simp
  · exact tendsto_const_nhds

end RHTower
