# Growing-packet full prime–pole cancellation

- **ID:** growing-packet-full-prime-pole-cancellation
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../../reports/review-3110/obstacles-summary.md, A2 at `dbc7d26186`
- **Statement:** For some explicit `c>0`, the full prime–pole remainder tends uniformly to zero on bounded-coefficient packets with both cell indices at most `exp(c√log Y)`.

## Existing inputs

`TheFullPrimeWindowCancelsTheGrowingHeadPole` identifies the literal all-prime mixed source and proves cancellation for each fixed finite packet. `Sieve.ChebyshevSharpSelfRateOne.exists_abs_sum_vonMangoldt_sub_self_kappa_one_rate` gives unconditional error `B x exp(−√log x/960000)`.

## Proposed proof

Abel summation with the Chebyshev error gives
`|Σ_(n≤x) Λ(n)/√n−2√x| ≤ C√x exp(−√log x/1920000)` eventually. Bound the initial interval `t≤x^(1/4)` by Chebyshev; beyond it, use the PNT error uniformly.

For detail and window indices `1≤a,b≤M`, the prime-window endpoints on the detail support lie between `Y/(M+1)` and `(M+1)Y`. If `M≤exp(c√log Y)`, their logarithms are eventually at least `(log Y)/2`. The endpoint errors, the strict-cutoff correction, and the second mixed pole term therefore admit a uniform bound polynomial in `M` times `exp(−δ√log Y)`, with numerical `δ>0`. Sum over at most `M²` pairs and choose `c` below the resulting exponent margin.

## Gates

- [x] Exact source and unconditional analytic input identified.
- [ ] Uniform quantitative window and packet estimates proved.
- [ ] Lean formalization, direct file audit, and transitive axiom audit.
