# Complete-multiplicativity tangent diagnostic

Run on the user-designated Runpod, 2026-09-06, Python/SymPy 1.13.3; six independent
processes on its 32-core host. Reproduce with `python3 tangent.py > tangent-results.json`.
The script uses exact rational arithmetic, nullspaces and quadratic evaluations.
It uses no floating-point sign test. Outputs are exploratory evidence, not Lean certificates.

For `a_d(n)=1-d[d|n]`, impose the seven deletion endpoints for nontrivial divisors of 30
on positive completely multiplicative weights through cutoff `N`. At the uniform weight,
prime-value variations give `phi(n)=sum_p v_p(n)x_p`. The program restricts
`sum_n k(n)phi(n)^2` to the tangent constraints `sum_n a_d(n)phi(n)=0`, where
`k=2(a_6-a_3+5a_15-5a_30)`.

| N | Constraint rank | Tangent dimension | Restricted rank | Witnesses found |
|---:|---:|---:|---:|---|
| 30 | 6 | 4 | 0 | zero |
| 60 | 7 | 10 | 3 | positive, zero |
| 90 | 7 | 17 | 4 | positive, zero |
| 120 | 7 | 23 | 6 | positive, zero |
| 180 | 7 | 34 | 11 | negative, positive, zero |
| 210 | 7 | 39 | 13 | negative, positive, zero |

Search tests individual nullspace basis vectors and their pairwise sums/differences.
Absence of a negative witness at a cutoff does **not** certify nonnegativity there.
Exact directions and matrices are retained in `tangent-results.json`.

Negative tangents alone do not prove exact nonlinear counterexamples. They prompted a
separate symbolic construction: two primes above the square-root cutoff, with equal
numbers of multiples, permit opposite prime-value perturbations whose endpoint
cancellations are exact. This construction gives negative curvature at `N=930`, using
primes 59 and 61, and positive curvature using primes 251 and 257. Its proof does not
use the computed matrices or tangent vectors; see
[the paper proof](../../euler-deletion-paired-prime-freedom.md).

Consequence: complete multiplicativity does not rescue the proposed **finite**
endpoint-to-curvature sign constraint. Neither the calculation nor its symbolic
countermodel settles any implication specific to the infinite Mellin weights or zeta zeros.
