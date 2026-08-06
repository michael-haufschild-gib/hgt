# Littlewood Z5 opened: block bound off the line (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockSigma.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`dirichlet_block_sigma_bound (hσ : 0 ≤ σ) (t) (N M) (hN : 1 ≤ N) (hNM : N ≤ M) (P)` with prefix
hypothesis `∀ m ∈ [N,M], ‖∑_{Ico N m} n^{−It}‖ ≤ P`:

`‖∑_{Ico N M} n^{−σ−It}‖ ≤ P · N^{−σ}`.

Exact analogue of `dirichlet_block_one_bound`; same Abel step with `w n = n^{−σ}` instead of
`n^{−1}` (antitone and nonneg for `σ ≥ 0`), so `abel_block_bound` applies unchanged.

## The structural point

**Nothing in the derivative test changes.** The k-th derivative test controls the *pure phase* sum
`∑ n^{−It}`, which does not involve `σ`; the weight is what carries it off the line. So the whole Z3
chain is σ-independent up to the final Abel step, and the rectangle version costs only this
substitution plus re-running the assembly with `N^{−σ}` for `N^{−1}`.

## Next

σ-analogue of `dirichlet_block_one_full` (same prefix bound from `dirichlet_block_bound`, new
weight), then the assembly. Then `PNTPlus/ZetaBounds`'s Landau/3-4-1 pipeline consumes it.

## Lean note

`((n:ℝ):ℂ)^(−(σ:ℂ)) = (((n:ℝ)^(−σ) : ℝ) : ℂ)`: rewrite the exponent to `((−σ : ℝ) : ℂ)` first
(`show (-(σ:ℂ)) = (((-σ:ℝ)):ℂ) by push_cast; ring`), then `← Complex.ofReal_cpow hx.le (−σ)`.
`Complex.ofReal_cpow` will not fire against `−(σ:ℂ)` directly.
