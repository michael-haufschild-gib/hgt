/-
# Algebraic branches are local analytic functions (natural-boundary route, analytic side)

The natural-boundary route to `q62` transcendence/independence (see `Bottcher/STATUS.md`): an algebraic
function over `ℂ(z)` continues analytically across every point except a finite branch/pole set, so its
singular set is finite — whereas `φ_c`'s singular set is its Julia set `J_c` (infinite). The analytic
keystone of that route, built here (no dynamics, pure complex analysis):

> A **simple root** of an analytic relation `f(z,w)=0` is a **local analytic branch**: there is `g`
> analytic near `z₀` with `g z₀ = w₀` and `f(z, g z) = 0` near `z₀`.

Proof: the analytic implicit function theorem (`ContDiffAt.implicitFunction`) gives a `ContDiffAt`
branch, which is analytic in `ℂ` (`ContDiffAt.analyticAt`). "Simple root" = the partial `w`-derivative
is non-zero (`isInvertible_partial_of_hasDerivAt`), the `IsInvertible` hypothesis the IFT consumes.
-/
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness

open Filter Topology

namespace Bottcher

/-- **A simple root of an analytic relation is a local analytic branch.** If `f : ℂ×ℂ → ℂ` is analytic
near `(z₀,w₀)`, `f(z₀,w₀)=0`, and the `w`-partial derivative is invertible at `(z₀,w₀)`, then there is
`g` analytic at `z₀` with `g z₀ = w₀` and `f(z, g z) = 0` for `z` near `z₀`. The analytic implicit
function theorem with the `ℂ`-upgrade `ContDiffAt ⊤ ⇒ AnalyticAt`. -/
theorem exists_analyticAt_branch {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ}
    (hf : ContDiffAt ℂ ⊤ f (z₀, w₀))
    (hroot : f (z₀, w₀) = 0)
    (hinv : (fderiv ℂ f (z₀, w₀) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = w₀ ∧ ∀ᶠ z in 𝓝 z₀, f (z, g z) = 0 := by
  have pn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hf.implicitFunction pn hinv, ?_, ?_, ?_⟩
  · exact (hf.contDiffAt_implicitFunction pn hinv).analyticAt
  · exact hf.implicitFunction_apply_self pn hinv
  · filter_upwards [hf.eventually_apply_implicitFunction pn hinv] with x hx
    rw [hx, hroot]

/-- **Non-zero partial derivative ⟹ the IFT invertibility hypothesis.** If `f` is differentiable at
`(z₀,w₀)` and the partial function `w ↦ f(z₀,w)` has a non-zero derivative `d` at `w₀` (a *simple*
root), then `fderiv f (z₀,w₀) ∘ inr` is invertible — the hypothesis `exists_analyticAt_branch`
consumes. The partial fderiv equals `smulRight 1 d = d • 1`, invertible since `d ≠ 0`. -/
theorem isInvertible_partial_of_hasDerivAt {f : ℂ × ℂ → ℂ} {z₀ w₀ d : ℂ}
    (hfd : DifferentiableAt ℂ f (z₀, w₀))
    (hpartial : HasDerivAt (fun w => f (z₀, w)) d w₀) (hd : d ≠ 0) :
    (fderiv ℂ f (z₀, w₀) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  have hinr : HasFDerivAt (fun w : ℂ => (z₀, w)) (ContinuousLinearMap.inr ℂ ℂ ℂ) w₀ := by
    simpa using ((ContinuousLinearMap.inr ℂ ℂ ℂ).hasFDerivAt (x := w₀)).add_const (z₀, (0 : ℂ))
  have hcomp : HasFDerivAt (fun w => f (z₀, w))
      (fderiv ℂ f (z₀, w₀) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) w₀ :=
    HasFDerivAt.comp w₀ hfd.hasFDerivAt hinr
  have heq : (fderiv ℂ f (z₀, w₀) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ)
      = (1 : ℂ →L[ℂ] ℂ).smulRight d := hcomp.unique hpartial.hasFDerivAt
  rw [heq, show (1 : ℂ →L[ℂ] ℂ).smulRight d = d • (1 : ℂ →L[ℂ] ℂ) from
    ContinuousLinearMap.ext fun t => by simp [mul_comm]]
  exact ⟨(Units.mk0 d hd) • ContinuousLinearEquiv.refl ℂ ℂ,
    ContinuousLinearMap.ext fun t => by simp⟩

/-- **Simple-root branch, packaged with the derivative hypothesis.** Combines the two lemmas: an
analytic relation `f(z,w)=0` with `f(z₀,w₀)=0` and non-zero `w`-derivative `d` there has a local
analytic branch through `(z₀,w₀)`. The directly-applicable form for "an algebraic function is locally
analytic at a non-branch point" in the natural-boundary transcendence argument. -/
theorem exists_analyticAt_branch_of_hasDerivAt {f : ℂ × ℂ → ℂ} {z₀ w₀ d : ℂ}
    (hf : ContDiffAt ℂ ⊤ f (z₀, w₀))
    (hroot : f (z₀, w₀) = 0)
    (hpartial : HasDerivAt (fun w => f (z₀, w)) d w₀) (hd : d ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = w₀ ∧ ∀ᶠ z in 𝓝 z₀, f (z, g z) = 0 :=
  exists_analyticAt_branch hf hroot
    (isInvertible_partial_of_hasDerivAt (hf.differentiableAt (by simp)) hpartial hd)

/-- **A polynomial relation with a simple root has a local analytic branch** (the concrete
`AlgebraicBranch` for an algebraic function over `ℂ(z)`). If `Σ_i (P.coeff i)(z)·w^i = 0` at `(z₀,w₀)`
and the `w`-derivative `d ≠ 0` (simple root), then there is `g` analytic at `z₀` with `g z₀ = w₀` and the
relation holding with `w = g z` near `z₀`. `f(z,w) = Σ_i (P.coeff i).aeval z · wⁱ` is a bivariate
polynomial, hence `ContDiff` (`contDiff_aeval` + `ContDiff.sum`); the rest is `exists_analyticAt_branch`.
For `P` = (cleared-denominator) minimal polynomial of an algebraic `φ_c` and `w₀ = lim φ_c`, this is the
analytic continuation of `φ_c` across a non-branch point in the natural-boundary transcendence argument. -/
theorem exists_analyticAt_branch_poly {z₀ w₀ d : ℂ} (P : Polynomial (Polynomial ℂ))
    (hroot : ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀)
    (hd : d ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = w₀ ∧
      ∀ᶠ z in 𝓝 z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g z) ^ i = 0 := by
  have hf : ContDiffAt ℂ ⊤ (fun p : ℂ × ℂ => ∑ i ∈ P.support, (P.coeff i).aeval p.1 * p.2 ^ i)
      (z₀, w₀) :=
    (ContDiff.sum fun i _ =>
      ((Polynomial.contDiff_aeval (𝕜 := ℂ) (P.coeff i) ⊤).comp contDiff_fst).mul
        (contDiff_snd.pow i)).contDiffAt
  exact exists_analyticAt_branch_of_hasDerivAt hf hroot hpartial hd

/-- **Local uniqueness of a simple-root branch (polynomial form).** If `g₁, g₂` are continuous at `z₀`,
both pass through the simple root `(z₀, w₀)` of `F(z,w) = Σ_i (P.coeff i)(z)·wⁱ` (the `w`-derivative
`d ≠ 0` there), and both satisfy the relation `F(z, gⱼ z) = 0` near `z₀`, then `g₁ = g₂` near `z₀`.

This is the matching step of the natural-boundary transcendence argument: the algebraic branch produced by
`exists_analyticAt_branch_poly` and the dynamical Böttcher branch agree wherever both are defined and pass
through the same simple root, so the algebraic continuation inherits the Böttcher modulus `‖·‖ = exp G_c`,
feeding the boundary engine (`DendriteBoundary` / `InteriorBoundary`).

Proof: pure algebra + continuity, no IFT internals. The polynomial factoring
`F(z,a) − F(z,b) = (a − b)·Q(z,a,b)` with cofactor `Q(z,a,b) = Σ_i (P.coeff i)(z)·Σ_{j<i} aʲ bⁱ⁻¹⁻ʲ`
satisfies `Q(z₀,w₀,w₀) = ∂_w F(z₀,w₀) = d ≠ 0` (`geom_sum₂_mul` for the factoring; `HasDerivAt.unique`
to identify the cofactor value with the derivative). Continuity makes `Q ≠ 0` near `z₀`, and on the locus
where both relations hold the difference `(g₁ − g₂)·Q = F(·,g₁) − F(·,g₂) = 0`, forcing `g₁ = g₂`. -/
theorem branch_unique_poly {z₀ w₀ d : ℂ} (P : Polynomial (Polynomial ℂ))
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    {g₁ g₂ : ℂ → ℂ} (hg₁ : ContinuousAt g₁ z₀) (hg₂ : ContinuousAt g₂ z₀)
    (h₁ : g₁ z₀ = w₀) (h₂ : g₂ z₀ = w₀)
    (hrel₁ : ∀ᶠ z in 𝓝 z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g₁ z) ^ i = 0)
    (hrel₂ : ∀ᶠ z in 𝓝 z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g₂ z) ^ i = 0) :
    ∀ᶠ z in 𝓝 z₀, g₁ z = g₂ z := by
  have hfactor : ∀ z a b : ℂ,
      (∑ i ∈ P.support, (P.coeff i).aeval z * a ^ i) - (∑ i ∈ P.support, (P.coeff i).aeval z * b ^ i)
        = (a - b) * ∑ i ∈ P.support, (P.coeff i).aeval z *
            (∑ j ∈ Finset.range i, a ^ j * b ^ (i - 1 - j)) := by
    intro z a b
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hg : a ^ i - b ^ i = (∑ j ∈ Finset.range i, a ^ j * b ^ (i - 1 - j)) * (a - b) :=
      (geom_sum₂_mul a b i).symm
    rw [← mul_sub, hg]; ring
  set Q : ℂ → ℂ := fun z => ∑ i ∈ P.support, (P.coeff i).aeval z *
    (∑ j ∈ Finset.range i, (g₁ z) ^ j * (g₂ z) ^ (i - 1 - j)) with hQdef
  have hQ0 : Q z₀ = d := by
    have hd' : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i)
        (∑ i ∈ P.support, (P.coeff i).aeval z₀ * ((i : ℂ) * w₀ ^ (i - 1))) w₀ := by
      have key : (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i)
          = ∑ i ∈ P.support, (fun w => (P.coeff i).aeval z₀ * w ^ i) := by
        funext w; simp only [Finset.sum_apply]
      rw [key]
      exact HasDerivAt.sum (fun i _ => (hasDerivAt_pow i w₀).const_mul ((P.coeff i).aeval z₀))
    have huniq := hd'.unique hpartial
    show (∑ i ∈ P.support, (P.coeff i).aeval z₀ *
      (∑ j ∈ Finset.range i, (g₁ z₀) ^ j * (g₂ z₀) ^ (i - 1 - j))) = d
    rw [h₁, h₂, ← huniq]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hinner : ∀ j ∈ Finset.range i, w₀ ^ j * w₀ ^ (i - 1 - j) = w₀ ^ (i - 1) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [← pow_add]; congr 1; omega
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hQcont : ContinuousAt Q z₀ := by
    apply tendsto_finsetSum
    intro i _
    apply ContinuousAt.mul ((Polynomial.contDiff_aeval (𝕜 := ℂ) (P.coeff i) ⊤).continuous.continuousAt)
    apply tendsto_finsetSum
    intro j _
    exact (hg₁.pow j).mul (hg₂.pow _)
  have hQne : ∀ᶠ z in 𝓝 z₀, Q z ≠ 0 :=
    hQcont.eventually_ne (by rw [hQ0]; exact hd)
  filter_upwards [hrel₁, hrel₂, hQne] with z h1 h2 hQz
  have hz : (g₁ z - g₂ z) * Q z = 0 := by
    have h := hfactor z (g₁ z) (g₂ z)
    rw [h1, h2] at h
    simpa [hQdef] using h.symm
  rcases mul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hQz

/-- **Branch uniqueness across a boundary point (`nhdsWithin` form).** Like `branch_unique_poly`, but the
second function `g₂` is only defined on a set `s` (the basin side of a Julia point `z₀`): it need only
*tend* to the simple root `w₀` along `𝓝[s] z₀` — not be continuous at `z₀`, where `φ_c` has no value
(the natural boundary). Then `g₁ = g₂` eventually along `𝓝[s] z₀`. This is the matching tool for the
natural-boundary crossing: `g₁` = the algebraic branch analytic across `z₀` (`exists_analyticAt_branch_poly`),
`g₂` = the basin Böttcher branch, `s` = the basin `(filledJulia c)ᶜ`. The cofactor `Q` now *tends* to
`d ≠ 0` along `𝓝[s] z₀` (using `g₂ → w₀`), so it is eventually nonzero and `(g₁ − g₂)·Q = 0` forces
`g₁ = g₂`. -/
theorem branch_unique_poly_within {z₀ w₀ d : ℂ} (P : Polynomial (Polynomial ℂ))
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    {s : Set ℂ} {g₁ g₂ : ℂ → ℂ}
    (hg₁ : ContinuousAt g₁ z₀) (h₁ : g₁ z₀ = w₀)
    (hg₂ : Tendsto g₂ (𝓝[s] z₀) (𝓝 w₀))
    (hrel₁ : ∀ᶠ z in 𝓝[s] z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g₁ z) ^ i = 0)
    (hrel₂ : ∀ᶠ z in 𝓝[s] z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g₂ z) ^ i = 0) :
    ∀ᶠ z in 𝓝[s] z₀, g₁ z = g₂ z := by
  have hfactor : ∀ z a b : ℂ,
      (∑ i ∈ P.support, (P.coeff i).aeval z * a ^ i) - (∑ i ∈ P.support, (P.coeff i).aeval z * b ^ i)
        = (a - b) * ∑ i ∈ P.support, (P.coeff i).aeval z *
            (∑ j ∈ Finset.range i, a ^ j * b ^ (i - 1 - j)) := by
    intro z a b
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hg : a ^ i - b ^ i = (∑ j ∈ Finset.range i, a ^ j * b ^ (i - 1 - j)) * (a - b) :=
      (geom_sum₂_mul a b i).symm
    rw [← mul_sub, hg]; ring
  have hval : (∑ i ∈ P.support, (P.coeff i).aeval z₀ *
      (∑ j ∈ Finset.range i, w₀ ^ j * w₀ ^ (i - 1 - j))) = d := by
    have hd' : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i)
        (∑ i ∈ P.support, (P.coeff i).aeval z₀ * ((i : ℂ) * w₀ ^ (i - 1))) w₀ := by
      have key : (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i)
          = ∑ i ∈ P.support, (fun w => (P.coeff i).aeval z₀ * w ^ i) := by
        funext w; simp only [Finset.sum_apply]
      rw [key]
      exact HasDerivAt.sum (fun i _ => (hasDerivAt_pow i w₀).const_mul ((P.coeff i).aeval z₀))
    rw [← hd'.unique hpartial]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hinner : ∀ j ∈ Finset.range i, w₀ ^ j * w₀ ^ (i - 1 - j) = w₀ ^ (i - 1) := by
      intro j hj; rw [Finset.mem_range] at hj; rw [← pow_add]; congr 1; omega
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hg1t : Tendsto g₁ (𝓝[s] z₀) (𝓝 w₀) := by
    rw [← h₁]; exact (hg₁.tendsto).mono_left nhdsWithin_le_nhds
  have hQt : Tendsto (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z *
      (∑ j ∈ Finset.range i, (g₁ z) ^ j * (g₂ z) ^ (i - 1 - j))) (𝓝[s] z₀)
      (𝓝 (∑ i ∈ P.support, (P.coeff i).aeval z₀ *
        (∑ j ∈ Finset.range i, w₀ ^ j * w₀ ^ (i - 1 - j)))) := by
    apply tendsto_finsetSum
    intro i _
    apply Tendsto.mul
    · exact ((Polynomial.contDiff_aeval (𝕜 := ℂ) (P.coeff i) ⊤).continuous.continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    · apply tendsto_finsetSum
      intro j _
      exact (hg1t.pow j).mul (hg₂.pow _)
  have hQne : ∀ᶠ z in 𝓝[s] z₀, (∑ i ∈ P.support, (P.coeff i).aeval z *
      (∑ j ∈ Finset.range i, (g₁ z) ^ j * (g₂ z) ^ (i - 1 - j))) ≠ 0 := by
    rw [hval] at hQt
    exact hQt.eventually (eventually_ne_nhds hd)
  filter_upwards [hrel₁, hrel₂, hQne] with z h1 h2 hQz
  have hz : (g₁ z - g₂ z) * (∑ i ∈ P.support, (P.coeff i).aeval z *
      (∑ j ∈ Finset.range i, (g₁ z) ^ j * (g₂ z) ^ (i - 1 - j))) = 0 := by
    have h := hfactor z (g₁ z) (g₂ z)
    rw [h1, h2] at h
    simpa using h.symm
  rcases mul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hQz

/-- **Gluing pillar for algebraic continuation.** Two analytic branches `g₁, g₂` of the relation
`Σᵢ (P.coeff i)(z)·wⁱ = 0` (each holding near `w₁`) on a preconnected open `W`, agreeing at one simple-root
point `w₁ ∈ W` (`∂_Y P` at `(w₁, g₁ w₁)` is `d ≠ 0`), agree on all of `W`. Via `branch_unique_poly` (local
agreement near `w₁`) + the identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`). The
consistency step that makes path-continuation of the algebraic function single-valued: consecutive local
branches sharing one value glue into one. -/
theorem branch_eqOn_of_eq_at {P : Polynomial (Polynomial ℂ)} {W : Set ℂ}
    (hWc : IsPreconnected W) {g₁ g₂ : ℂ → ℂ}
    (hg₁ : AnalyticOnNhd ℂ g₁ W) (hg₂ : AnalyticOnNhd ℂ g₂ W)
    {w₁ d : ℂ} (hw₁W : w₁ ∈ W)
    (hrel₁ : ∀ᶠ z in 𝓝 w₁, ∑ i ∈ P.support, (P.coeff i).aeval z * (g₁ z) ^ i = 0)
    (hrel₂ : ∀ᶠ z in 𝓝 w₁, ∑ i ∈ P.support, (P.coeff i).aeval z * (g₂ z) ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval w₁ * w ^ i) d (g₁ w₁))
    (hd : d ≠ 0) (heq : g₂ w₁ = g₁ w₁) :
    Set.EqOn g₁ g₂ W := by
  have hloc : ∀ᶠ z in 𝓝 w₁, g₁ z = g₂ z :=
    branch_unique_poly P hpartial hd (hg₁ w₁ hw₁W).continuousAt (hg₂ w₁ hw₁W).continuousAt
      rfl heq hrel₁ hrel₂
  exact hg₁.eqOn_of_preconnected_of_eventuallyEq hg₂ hWc hw₁W hloc

end Bottcher
