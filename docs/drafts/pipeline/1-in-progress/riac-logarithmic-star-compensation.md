# The logarithmic boundary of prime-star compensation

- **ID:** RIAC-logarithmic-star
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md), critical torsion
- **Statement:** For prime diagonals `D_α(p)=d(p)+(log p)^α`, finite central compensation exists exactly when `α>2`.

## Target

The formalized arbitrary-diagonal classification reduces this to convergence
of `Σ_p (log p)²/(p D_α(p))`. The candidate replaces every positive power of
the conductor by a logarithmic cost, isolating the critical scale more sharply.

For `α≤2`, the existing eventual logarithmic-square obstruction applies.
For `α>2`, the payment is bounded by `1/(p (log p)^(α−2))`. The existing theorem
`RHTower.Sieve.summable_primes_one_div_mul_log_rpow` proves convergence of
that prime series for every positive logarithmic exponent. It does not follow by comparison with all integers
when the exponent is at most one. Its Chebyshev prime-count bound and dyadic
shell proof is unconditional. The exact diagonal comparison remains under
formalization.

## Required proof and survivor

Verify that prime-logarithmic summability already exists before rebuilding it.
Prove the exact exponent, retain the actual prime-star matrix comparison,
and construct the minimal positive completion using the convergent payment.
No theorem or priority is yet claimed. This diagonal completion still leaves
composite interactions and nonlocal archimedean compensation unresolved.

## Dependency-closed argument under Lean verification

The diagonal is strictly positive since `d(p)≥0` and `log p>0`.
For `α>2`, its payment density is at most
`(log p)²/(p(log p)^α)=1/(p(log p)^(α−2))`, summable by the existing prime-tail
theorem. For `α≤2`, eventually `log p≥1`, hence
`d(p)+(log p)^α≤log p+(log p)²≤2(log p)²`; the formalized logarithmic-square
obstruction gives divergence. The existing exact star classification then
gives finite positive completion iff `α>2`, its least payment as the full
series, and explicit finite negative probes at every other exponent.

The new diagonal comparison and threshold are in an unchecked Lean draft;
no formalized status is claimed.
