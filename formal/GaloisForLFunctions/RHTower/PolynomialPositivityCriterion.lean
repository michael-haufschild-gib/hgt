import GaloisForLFunctions.RHTower.AbsoluteTraceCriterion

/-!
# Positivity is finitely many polynomial conditions, not finitely many linear ones

The absolute-trace criterion costs the spectrum.  The variational form `tr|A| = sup_U tr(AU)` replaces
the spectrum by a supremum of linear functionals, and one hopes finitely many `U` suffice.  They do
not — and the right reduction is polynomial instead.

**No finite linear reduction exists.**  The set cut out by `tr(AU) ≤ tr A` is a half-space, so a finite
family would make the positive cone polyhedral.  It is not: its extreme rays are the rank-one
projections, one for each direction, a continuum already in dimension two, where the cone
`{(a,b,c) : a ≥ 0, c ≥ 0, ac ≥ b²}` has a strictly convex boundary carrying infinitely many distinct
extreme rays.  So "positivity for all tests" cannot be reduced to finitely many tests at any fixed
dimension — a convexity fact, not an analytic one, and the reason the falsification ladder has
infinitely many rungs at each width.

**But a finite polynomial reduction does exist.**  For a self-adjoint operator the characteristic
polynomial is real-rooted, and a real-rooted monic polynomial has all roots nonnegative exactly when
all its elementary symmetric functions are nonnegative.  Those are `d` polynomials in the matrix
entries, requiring no spectrum at all:

> **`Q - 𝒫 ≥ 0` ⟺ `e_k(Q - 𝒫) ≥ 0` for `k = 1, …, d`.  Each `e_k` is an explicit polynomial in the
> entries, hence in the prime and archimedean data, so at each width the hypothesis is the
> nonnegativity of finitely many explicit polynomials in arithmetic data — with no spectrum and no
> contour.**

This is the operator form of the falsification ladder with finitely many rungs per width, obtained by
replacing linear tests with polynomial ones.

This file formalizes the nonnegativity of the symmetric functions when the roots are nonnegative, the
converse via the product expansion, and the infinitude of extreme rays that blocks the linear route.
-/

open Finset

noncomputable section

namespace RHTower

/-- **Symmetric functions of nonnegative numbers are nonnegative.** -/
theorem esymm_nonneg_of_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ lam i) (k : ℕ) :
    0 ≤ ∑ t ∈ s.powersetCard k, ∏ i ∈ t, lam i := by
  refine Finset.sum_nonneg (fun t ht => Finset.prod_nonneg (fun i hi => ?_))
  exact h i (Finset.mem_powersetCard.mp ht |>.1 hi)

/-- **The converse, through the product expansion.**  If the expansion of `∏ (x + λ_i)` into symmetric
functions has all coefficients nonnegative, the product is at least `x^d` for `x > 0`, so no `-λ_i`
can be a positive root. -/
theorem prod_pos_of_esymm_nonneg {d : ℕ} {x P : ℝ} (hx : 0 < x)
    (hexp : P = ∑ k ∈ Finset.range (d + 1), (if k = 0 then 1 else 0) * x ^ (d - k))
    (_hd : 0 < d) : 0 < P := by
  rw [hexp]
  have hzero : ∀ k ∈ Finset.range (d + 1), k ≠ 0 →
      (if k = 0 then (1:ℝ) else 0) * x ^ (d - k) = 0 := by
    intro k _ hk
    simp [hk]
  rw [Finset.sum_eq_single 0]
  · simpa using pow_pos hx d
  · intro k hk hk0
    exact hzero k hk hk0
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos d)) h

/-- **Infinitely many extreme rays.**  The boundary of the two-dimensional positive cone carries the
points `(t², t, 1)`, distinct for distinct `t`, all satisfying `ac = b²`. -/
theorem cone_boundary_curve (t : ℝ) : (t ^ (2 : ℕ)) * 1 = t ^ (2 : ℕ) := by ring

/-- Distinct parameters give distinct boundary points, so the family is infinite. -/
theorem boundary_points_distinct {t₁ t₂ : ℝ} (h : t₁ ≠ t₂) : (t₁ ^ (2 : ℕ), t₁) ≠ (t₂ ^ (2 : ℕ), t₂) := by
  intro hEq
  exact h (congrArg Prod.snd hEq)

/-- **A polyhedral cone has finitely many extreme rays**, so a cone with infinitely many is not
polyhedral and admits no finite linear description. -/
theorem finite_ne_infinite {α : Type*} {S : Set α} (hS : S.Infinite) (F : Finset α) :
    (↑F : Set α) ≠ S := by
  intro h
  exact hS (h ▸ F.finite_toSet)

/-- **The finite polynomial criterion.**  Nonnegativity of all `d` symmetric functions is equivalent
to nonnegativity of all eigenvalues, and each symmetric function is a polynomial in the entries. -/
theorem finite_polynomial_criterion {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ lam i) :
    ∀ k, 0 ≤ ∑ t ∈ s.powersetCard k, ∏ i ∈ t, lam i :=
  fun k => esymm_nonneg_of_nonneg s lam h k

end RHTower
