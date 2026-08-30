# T1 finite-order rough-polynomial prime-projection no-go

- **ID:** T1-FORP
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · T1 LAND
- **Statement:** No fixed finite-order differential heads, convolved with arbitrary finite-support mollifiers and combined in any finite multi-piece sum, can equal true-prime logarithmic half-density throughout T1's `N^49`-rough source window through `N^100` once `N ≥ 2^(d+2)`.

## Goal

Kill T1's full-minus-omitted LAND subroute when landing is attempted by a fixed finite Levinson--Conrey differential polynomial and finite-support mollifier. Proof chain under attack:

`literal smoothed theta/prime detector → differentiated Selberg diagonal and signed full-minus-omitted current → coefficient-faithful fixed critical Weil pairing → boundedness → RH`.

The intended discharge is terminal for the finite-order detector-native LAND class: its coefficient-faithful fixed-pairing arrow is impossible before analytic estimates enter.

## Gates

- [x] 0 → 1 in-progress: source-pure, exact convolution model, rough-tail attack, Door passport stated
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile audit
- [x] 2 → 3 formalized: Lean theorem, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4 publication-ready

## Conjecture loop

- **C1 (failed significance):** fixed-support corrections cannot repair the co-moving normalized secant. True, but immediate from existing exterior-prime coefficient vanishing; no new route information.
- **C2 (failed novelty):** any co-moving correction carries unbounded prime half-density mass. Already subsumed by formal non-summability of Euler prime half-density mass/capacity.
- **C3 (proved): finite-order polynomial rough-tail no-go.** A finite derivative combination has head `P(log n)/sqrt n`. If a mollifier is supported on `q ≤ M`, then at every positive `M`-rough index the divisor convolution has exactly one surviving divisor, `q=1`; hence it equals `moll(1) P(log n)/sqrt n`. Finite sums replace `P` by the exact unit-weighted polynomial `Σ_i C(moll_i(1))P_i`.

## Paper attack

Let `P ∈ ℂ[X]` and let `moll : ℕ → ℂ` vanish above `M`.

1. If `n>0` is `M`-rough, each divisor `q|n` with `q≤M` equals `1`. Every `q>M` has zero mollifier coefficient. Thus
   `Σ_{q|n} P(log(n/q))/sqrt(n/q) moll(q) = moll(1)P(log n)/sqrt n`.
2. Suppose this equals `log p/sqrt p` for more than `deg(P-X)` distinct exterior primes. Since `log` is injective on positive reals, `P-X` has too many distinct roots, so `P=X`.
3. For any such exterior prime `p`, `p²` is `M`-rough and composite. The same coefficient is then `log(p²)/sqrt(p²) ≠ 0`, whereas true-prime half-density is zero.
4. Finite-window strengthening: the iterated Bertrand reservoir gives `d+1` distinct exterior primes below `R=2^(d+1)(M+2)`. If `R²≤L`, all these primes and their squares lie in the source window `n≤L`; therefore no residual-degree `<d+1` detector can be coefficient-faithful on that window.
5. At T1's fixed schedule `M=N^49`, `L=N^100`, the explicit threshold `N≥2^(d+2)` gives `R²≤L`: use `N^49+2≤2N^49`, square, and absorb `2^(2d+4)` into `N²`. Therefore every fixed derivative order fails within the actual AFE window, not only on an abstract infinite tail.

This is dependency-closed and `[PROVED HERE]`.

## No-go closure

- **Exact killing theorem/mechanism:** rough support makes finite mollification invisible; finite differentiation leaves only polynomial dependence on `log n`; exterior-prime interpolation forces the prime profile on exterior prime squares.
- **Strongest positive survivor:** exact rough-tail classification plus finite-window degree lower bound. Any coefficient-faithful detector on a window containing `r` suitable exterior primes and their squares must have residual log-polynomial degree at least `r`; viable T1 LAND therefore needs derivative order growing with source scale, nonlinear valuation-aware prime-power subtraction, or a representation that does not factor through a finite log jet.
- **New insight:** quadratic aperture horizon persists for every fixed finite differential order and every finite-support mollifier, including finite sums and multi-piece mollifiers with arbitrary unit weights. Changing finite mollifier weights cannot repair the obstruction.
- **Status:** paper proof dependency-closed; hostile audit strengthened normalized mollifiers to arbitrary unit weights and eliminated the residual-degree hypothesis from the capstone. Formalized by `not_forall_finiteOrderMollifiedCriticalDetectorCombinationCoeff_eq_truePrime_t1AfeWindow` in `XiMassLevinsonFiniteOrderPolynomialNoGo.lean`. Targeted build passed; `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`. Global lint is currently red only because unrelated owned modules elsewhere are unwired; this module is wired into `RHTower.lean` and produced no lint violation.

## Literature audit

- Conrey-style mollifiers use a fixed polynomial `Q(-L⁻¹ d/ds)` and optimize zero-density proportions; no source found claims coefficientwise prime projection. See [Short mollifiers of the Riemann zeta-function](https://arxiv.org/abs/2508.11108).
- [Farmer](https://www.cambridge.org/core/journals/mathematika/article/abs/long-mollifiers-of-the-riemann-zetafunction/A7CD0C1361DEABDE407AC25D66C82A43) studies long mollifiers; [Bettin--Gonek](https://arxiv.org/abs/1604.02740) show sufficiently long mollifiers imply RH. Neither supplies a finite-order coefficient-faithful prime landing.
- 2026 automorphic extensions retain finite derivative polynomials for proportion estimates, not exact true-prime extraction; see [arXiv:2605.24363](https://arxiv.org/abs/2605.24363).

## Log

- 2026-08-30 — created after corpus-defined T1 LAND audit; C1 and C2 rejected; C3 selected as hardest route-terminal conjecture.
- 2026-08-30 — C3 proved on paper and in Lean; hostile audit removed normalization and degree premises; T1 fixed-finite-order detector-native LAND subroute retired.
