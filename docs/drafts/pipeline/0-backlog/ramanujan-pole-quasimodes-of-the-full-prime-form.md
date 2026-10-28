# Ramanujan pole profiles are quasimodes of the full finite prime form

- **ID:** ramanujan-pole-quasimodes-of-the-full-prime-form
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** RAPT valuation steps and actual finite-sieve adjunction operator; RBG Ramanujan germs; Mertens finite part
- **Count:** uncounted; novelty and dependency-closed proof remain

## Target

Let c_m(n) be the Ramanujan sum, m>=1, and let P_N be the literal real symmetric
matrix `weilPrimeKernel(n,k)` for 1<=n,k<=N. Define

`u_(m,N)(n)=c_m(n)/sqrt(phi(m)*n)`,
`E(m)=gamma+log(m)+tameDifferent(m)`.

Conjecture, for every fixed m,

`||P_N u_(m,N)-(log(N)-E(m))u_(m,N)||^2/log(N) -> 0`,
`||u_(m,N)||^2/log(N) -> 1`.

Distinct fixed m should have inner product divided by log(N) tending to zero.
Consequently each fixed finite packet of distinct arithmetic energies should
produce distinct actual matrix eigenvalues at `log(N)-E(m)+o(1)`. The proposed
statement does not order the entire spectrum or exclude additional eigenvalues.
It supplies no RH or full Weil-test sign inference.

## Connection to audit

For a prime power m=p^k, k>=1, the normalized Ramanujan sum is

`c_(p^k)(n)/sqrt(phi(p^k))`
`=sqrt(phi(p^k))*(1_(v_p(n)>=k)-1/(p-1)*1_(v_p(n)=k-1))`.

This appears to be exactly the density-normalized local Blaschke excitation.
Products over primes should identify every finite-sieve eigenmode with the
corresponding normalized Ramanujan profile. This arithmetic identification
must be proved from the corpus Ramanujan formulas.

For a bounded valuation profile g, divide the actual prime row on g(n)/sqrt(n)
by 1/sqrt(n). The up and down divisor sums should give

`g(n)*(Mertens(floor(N/n))+log(n))`
`+sum_(p in support(g)) log(p)*sum_(p^j<=N/n) p^(-j)*(g(np^j)-g(n))`
`+sum_(p in support(g)) log(p)*sum_(1<=j<=v_p(n)) (g(n/p^j)-g(n))`.

Replacing each finite up sum by its geometric tail completion gives the actual
local pole-gauge generator. The error is bounded by a constant times the
Mertens remainder, logarithmic floor roundoff, and geometric quotient tails.
All tend to zero when N/n tends to infinity and remain bounded everywhere.
The harmonic boundary-layer lemma should make their squared row error o(log N).
The complete-period Ramanujan Gram should supply the normalized inner products.

Exact row reindexing, the generator/eigenmode identity, uniform error domination,
periodic harmonic transfer, and spectral-distance transfer remain obligations.
No dependency-closed paper proof is claimed yet.

## Novelty leads

- `RAPT/TheValuationTowerIsExactlySolvable.lean` proves pointwise local pole-gauge
  eigenvectors and a sharp finite-class gap. Its formalized card anticipates the
  Kronecker energy list. These are baseline.
- The active finite-sieve adjunction package proves an actual maximal-domain
  operator on supported-integer class coordinates. The proposed target acts on
  every integer up to N with the full literal prime matrix; it requires a new
  row-error estimate, not only convergence of quadratic forms.
- Corpus searches for valuation approximate eigenvectors and Ramanujan prime
  quasimodes found those local equations and generic approximate-eigenvector
  tools, but no instance of this full-matrix assertion.
- `RAPT/TheArchimedeanPlacePaysTheArithmeticPoint.lean` through its joint Gram
  was inspected. Its `jointMode` already uses c_m/sqrt(phi(m)), and
  `periodMean_ramanujanMode_mul` proves exact complete-period orthogonality.
  The normalization and periodic Gram are baseline inputs; the new target is
  their actual full-prime row residual.
- `ALG/TheLocalFactorTricklesDownByRamanujan.lean` was inspected through its
  Ramanujan datum: it concerns the finite-field trace bound, not Ramanujan sums.
- The card `constrained-prolate-arithmetic-dilation-operator-limit.md` was
  inspected through its operator and spectral limit: it concerns a different
  positive dilation-response matrix with an explicit trace-class diagonal limit.

## Gates

- [ ] Complete novelty and significance audit.
- [ ] Dependency-closed paper proof of the actual full-matrix assertion.
- [ ] Exact Lean formalization, direct-source and transitive axiom audits.

Current finite-sieve adjunction formalization remains the active task.
