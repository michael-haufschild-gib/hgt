# The logarithmic boundary of prime-star compensation

- **ID:** RIAC-logarithmic-star
- **Stage:** 3-formalized
- **Type:** SHARP BOUNDARY
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md), critical torsion
- **Statement:** For prime diagonals `D_α(p)=d(p)+(log p)^α`, finite central compensation exists exactly when `α>2`.

## Exact classification and proof

The diagonal is positive since `d(p)≥0` and `log p>0`.
For `α>2`, its payment density is at most

`(log p)²/(p(log p)^α)=1/(p(log p)^(α−2))`.

The existing theorem `RHTower.Sieve.summable_primes_one_div_mul_log_rpow`
proves convergence for every positive logarithmic exponent. Its Chebyshev
bound and dyadic-shell proof are unconditional; comparison with all integers
would lose the range where that exponent is at most one.

For `α≤2`, eventually `log p≥1`, hence
`d(p)+(log p)^α≤log p+(log p)²≤2(log p)²`. The formalized logarithmic-square
obstruction gives divergence. The exact star classification therefore gives
finite positive completion precisely for `α>2`.

The least payment is `Σ_p (log p)²/(p D_α(p))`. Below or at the boundary,
every central budget has a finite negative probe with root coefficient one
and leaf coefficients `(log p/√p)/D_α(p)`.

## Lean status and positive survivor

`LogarithmicStarCompensation.lean` contains
`primeStar_log_payment_summable_iff`, `primeStar_log_completion_iff`,
`primeStar_log_minimal_completion` and `primeStar_log_negative`.
The direct production check and six transitive axiom audits pass with
standard axioms only.

The survivor is an explicit minimal positive completion at logarithmic cost,
sharper than every fixed positive conductor power. The prime-series estimate
is prior corpus work; no priority claim is made. Composite interactions and
nonlocal archimedean compensation remain separate problems.
