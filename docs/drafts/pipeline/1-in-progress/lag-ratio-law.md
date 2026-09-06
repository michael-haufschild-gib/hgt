# Lag ratio law: sampling sets with `n_{j+1}/n_j → 1`

**Status:** conjecture, 2026-09-06. Companion of `integer-lag-law-notes.md` (MUST-250–255, CANNOT-328).

## Conjecture (ratio law)

For every infinite `N ⊆ ℕ` with `n_{j+1}/n_j → 1`: `sup_{n ∈ N} a_n < ∞ ⟹ RH`, where
`a_n = Φ(log n) = Σ_ρ n^{ρ−½}/(ρ(1−ρ))`.

Known cases: gaps `≤ √n · n^{o(1)}` (Lipschitz route, MUST-250), primes and prime powers (Landau with the
strip `Θ ≤ ¾`, MUST-251/254), `k`-th powers and every support with a ζ-like counting series (MUST-252/253).
Sets like `{⌊e^{√m}⌋}` (gaps `n/(2 log n)`, no usable counting series) are open.

## The attained case is elementary

If `Θ = sup Re ρ > ½` is attained, let `ρ_1, …, ρ_k` be the zeros with `Re ρ_j = Θ` (finitely many by the count
bound in any bounded region? no — the top line can carry infinitely many zeros; assume finitely many, or truncate by
height with the weights `w_ρ ≪ γ^{−2}` making the far top zeros negligible). Then
`a_n = n^{Θ−½} P(log n) + O(n^{Θ−½−δ})` with `P(L) = Σ_j 2|w_j| cos(γ_j L + φ_j)`, a real trigonometric polynomial
with positive coefficients, mean zero, not identically zero, hence `sup P > 0`, and by Bohr almost periodicity the
set `{L : P(L) > sup P / 2}` is relatively dense (Lean tool: `exists_fin_simultaneous_integer_approximation_quantitative`
gives the simultaneous translation numbers). Since `log n_{j+1} − log n_j → 0`, the log-image of `N` meets every long
interval, so `a_n ≥ (sup P / 2) n^{Θ−½} − O(n^{Θ−½−δ}) → ∞` along `N`.

## The non-attained case is where the conjecture lives (and where abstract configurations fail)

For abstract configurations (symmetric under `ρ ↦ ρ̄`, `ρ ↦ 1 − ρ`, local count `≪ log T`, weights `1/(ρ(1−ρ))`)
the ratio law is false. Sketch: take `β_j = Θ − 2^{−j}`, `γ_j = exp(4^j)`, weights `|w_j| ≍ γ_j^{−2}`. The
`j`-th quadruple dominates `Φ_Z(L)` on the window `L ∈ [L_j, L_{j+1}]` with `L_j ≍ 8^j`, with geometric domination
over the others, and there `Φ_Z(L) ≈ 2|w_j| e^{L(β_j−½)} cos(γ_j L + φ_j)`. The negative arcs of the two
dominant cosines have `n`-length `≍ n/γ_{j+1} ≫ 1` for `n = e^L ≥ e^{8^j} ≫ γ_{j+1} = e^{4^{j+1}}` (`j ≥ 3`), so one
can choose integers `n ∈ N` inside them with consecutive ratios `1 + O(1/γ_{j+1}) → 1`, and `Φ_Z ≤ O(1)` on `N`
while `Θ > ½`. Consequently:

- **CANNOT (analysis):** no configuration-free proof of the ratio law exists; any proof must use ζ-specific
  input — either that `Θ` is attained (open), or a bound on the frequencies of near-top zeros relative to their
  weights (a "spectral regularity"). The integer lag law's Lipschitz bound `|a_m − a_n| ≤ 8(m−n+1)(log m+2)²/√n`
  is exactly such an input (it fails for the configuration above), but it is useless for gaps `> √n`.
- The Landau route circumvents the problem for supports with a counting series, because the ray argument uses a
  single pole and never needs the top to be attained.

## Verdict

`SURVIVES PRELIMINARY ATTACK` for ζ (no known counterexample; the abstract obstruction only shows what a proof
must use). Not a producer: RH-equivalent receiver. Lean target for the attained case: Bohr relative density of
positivity sets of trigonometric polynomials with positive coefficients (from the corpus simultaneous
approximation lemma); not built.

## Update 2026-09-06: attained case in Lean

`LagRatioLawAttained.exists_lag_gt_of_attainedTop_of_logDense` (STATUS MUST-256) proves the attained case for every
log-dense `N` (ratio → 1 suffices), with the mean-value route above (no Kronecker/Dirichlet approximation needed: the
window mean square of a real trigonometric polynomial with the conjugation symmetry is bounded below by half the sum
of squared moduli, and positivity is extracted from mean ≈ 0 and mean square ≥ m). The non-attained case remains the
open core; the abstract obstruction stands.
