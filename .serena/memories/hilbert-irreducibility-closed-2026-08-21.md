# Hilbert's irreducibility theorem — CLOSED in Lean (2026-08-21)

`GaloisForLFunctions.HTGeometry.HilbertIrreducibility.hilbert_irreducibility`

```
∀ {F : Polynomial (Polynomial ℚ)},
  Irreducible F → 1 ≤ F.natDegree →
  {b : ℚ | Irreducible (Polynomial.map (Polynomial.evalRingHom b) F)}.Infinite
```

Unconditional, `#print axioms` → `[propext, Classical.choice, Quot.sound]`.  Integral form
`hilbert_irreducibility_int` likewise.  Card: `docs/drafts/pipeline/3-formalized/
hilbert-irreducibility-theorem.md`.  **Mathlib has neither HIT nor Hilbertian fields.**

## Do not reopen the p-adic route
The plan previously recorded (p-adic ramification + Puiseux branch, `PadicRamifiedSpecialisation`)
*cannot* prove HIT:
* a single prime kills only roots on **ramified** branches — unramified branches still take
  `ℚ_p`-values;
* several primes force the specialised Galois group only to **meet** the inertia conjugacy classes,
  and a proper subgroup can meet many classes (Jordan's theorem gives the converse, not this);
* `X⁴+1` is reducible over **every** `ℚ_p`, so no purely local criterion can ever certify
  irreducibility.
HIT is irreducibly global.  `PadicRamifiedSpecialisation.lean` remains a valid standalone asset.

## The route used
Coleman–Zwald, *Hilbertian fields and Hilbert's irreducibility theorem*, arXiv:1809.10977, Thm 7.
Elementary: no Chebotarev, no large sieve, no Riemann–Hurwitz, no thin-set density theory.

Two design decisions that removed most of the friction:
1. **Base point in `ℤ`, base ring `ℤ[X]`.**  `Polynomial.taylor s₀` (with `s₀ : ℤ`) composed with
   `Polynomial.reflect D` performs `X ↦ s₀ + 1/T` *inside* `ℤ[T]`, so the monic relation satisfied
   by `t^D · w(s₀+1/t)` already has integer coefficients — the rational-root theorem applies with
   **no denominator clearing anywhere in the middle of the proof** (only once, at the very top, to
   pass from `ℚ[X][Y]` to `ℤ[X][Y]`).
2. **`IsRatGerm s₀ w` demands `q(s₀) ≠ 0`.**  Strengthening the rationality predicate is *free*: it
   is assumed (by contradiction) in step 1, where the stronger form is what makes `D(s₀) ≠ 0`, and
   it is produced in `Core` only with `q = 1`.

## Module map (`formal/GaloisForLFunctions/HTGeometry/HilbertIrreducibility/`)
* `ThinSets` — `Thin S` (any `m+1` far-out members are spread by `α t₀^q < (t_m−t₀)^E`);
  `thin_of_bddAbove`, `thin_of_inter`, `exists_gt_notMem_of_thin`, `infinite_compl_of_thin`
  (finitely many gap-thin sets cannot cover `ℤ`).  **Reusable, HIT-independent.**
* `DividedDifference` — iterated Rolle and `exists_dividedDiff_eq` (`f[t₀..t_m] = f⁽ᵐ⁾(u)/m!`).
  Derivatives are carried as an explicit sequence `D : ℕ → ℝ → ℝ` with `HasDerivAt (D j) (D (j+1) x) x`
  on an open set — this dodges every `iteratedDeriv` regularity side condition.  **Reusable.**
* `RationalInterpolation` — `exists_map_eq_of_eval_mem_range` (a poly over `L` of degree `< #s`
  with `K`-rational values at `K`-rational nodes is defined over `K`).
* `TaylorTail` — `tailSeq F j` with `A_{j+1} x = −x²·A_j' x`; `hasDerivAt_tailSeq_inv` transports
  `d/dt` through `t ↦ t⁻¹`; `analyticOrderAt_tailSeq`; `thin_or_eventually_poly` (cases a/c).
* `GermIntegral` — `Filter.Germ (𝓝 s₀) ℂ` as an `R[X]`-algebra (`scoped instance germAlgebra`),
  `bivEval`, and `IsIntegral ↔ ∃ monic bivariate relation`.  **Reusable pattern.**
* `ReflectSubstitution` — `shiftReflect`, `shiftedPoly`, `bivEval_shiftedPoly`.
* `IntegerRoot` — rational roots of a monic `ℤ[T][Y]` relation are integers.
* `Core` — `exists_int_value`, `thin_of_not_isRatGerm` (case b via
  `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` on the imaginary part; the polynomial branch
  closes by rebuilding the rational function with `reflect` and the local identity theorem
  `AnalyticAt.frequently_eq_iff_eventually_eq`).
* `AnalyticBranches` — `exists_analytic_branches`, built on the corpus'
  `U0.HolomorphicIFT.holo_implicit` + `root_complete` + `separable_specialize`.
* `IntegralCoefficients` / `AnalyticCoefficients` — coefficients of `∏ (C c·X − C vᵢ)`:
  transport along ring homs, integrality, analyticity (one shared one-step coefficient recursion).
* `MonicScaling` — `f̂ = Y^n + Σ_{k<n} a_k a_n^{n-1-k} Y^k`, `f̂(s, a_n(s)y) = a_n(s)^{n-1} f(s,y)`.
* `SubsetCoefficients` — step 2 `irreducible_fibre_of_not_rational`, step 1 `exists_not_ratGerm`
  (via `Polynomial.resultant` + `resultant_map_map` + `resultant_eq_zero_iff`, **not** Bézout).
* `Main` — `exists_regular_int`, `exists_int_clear` (denominator clearing via
  `IsLocalization.integerNormalization`), `hilbert_irreducibility_int`, `hilbert_irreducibility`.

## Downstream
HIT was the named gate on two top-level `2-fully-proven` cards (see `toplevel-2fp-remaining-ten`);
§2 of `algebraic-two-local-instant-exact-complexity` needs only 2-transitivity, not `S_D`.
