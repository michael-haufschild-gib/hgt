# CCM-FU: fixed-core density, weighted moments and actual block limits

- **Stage:** 3-formalized; exact-file checks and new-declaration audit passed; Lake packaging pending.
- **Parent:** [fixed-core energy limit](../1-in-progress/ccm-fu-fixed-core-energy-limit.md).
- **Closed:** Finite-prime squarefree density, every half-integer source moment, arbitrary positive cutoff rescaling, and the exact quadratic limit of every actual quotient-energy block.
- **Open:** Signed correlation control, reserve renewal through changing cores, full selection, uniform signed Abel bound, RH. Unbounded quotient depth is now assembled in the [complete energy limit](ccm-fu-fixed-core-energy-limit.md).

## Exact source statements

Let A_P(N) count squarefree integers 1<=r<=N whose prime factors avoid P,
where P is any fixed finite set of primes. Then

`A_P(N)/N -> rho_P=(6/pi²)*product_(p in P) p/(p+1)`.

The real-cutoff ratio A_P(floor(Y))/Y has the same limit. The exact prime
step, including all integer endpoints, is

`A_P(N)=A_(P+p)(N)+A_(P+p)(floor(N/p))`.

For every natural k, the complete weighted source satisfies

`(1/N)*sum_(r in source through N) sqrt(r/N)^(k+1) -> 2*rho_P/(k+3)`.

At every fixed c>0, replacing the source cutoff by floor(c*N) gives

`(1/N)*sum_(r in source through floor(c*N)) sqrt(r/N)^(k+1)`

`-> [2*rho_P/(k+3)]*c*sqrt(c)^(k+1)`.

In particular, for any real a,b,

`(1/N)*sum_(r in source through floor(c*N)) (a+b*sqrt(r/N))²`

`-> rho_P*[a²*c+(4/3)*a*b*c*sqrt(c)+b²*c²/2]`.

Every sum contains the full arithmetic source in its stated interval.
No numerical or unknown density premise is introduced.

## Actual divisor-energy consumer

Let H_P be the literal processed head. Set

`a_n=(H_P(n+1)-H_P(n))/(sqrt(n+1)-sqrt(n))`,

`b_n=H_P(n)-a_n*sqrt(n)`.

For every positive r with M/r=n, the exact clipped sample satisfies

`sqrt(r)*I_P(M,r)=a_n*sqrt(M)+b_n*sqrt(r)`.

Define B_(P,n)(M) as the sum of r*I_P(M,r)² over all squarefree
1<=r<=M avoiding P and satisfying M/r=n. For every fixed n>=1,

`B_(P,n)(M)/M² -> rho_P*[Phi_(P,n)(1/n)-Phi_(P,n)(1/(n+1))]`,

where

`Phi_(P,n)(c)=a_n²*c+(4/3)*a_n*b_n*c*sqrt(c)+b_n²*c²/2`.

Thus the limit is attached to the literal quotient cell, with exact
endpoints and source values. The [complete energy limit](ccm-fu-fixed-core-energy-limit.md) separately
assembles all cells. The sign of a prime-merger difference remains open.

## Dependency-closed paper proof

Split the squarefree avoiding count by divisibility by p. Multiplication
by p maps squarefree cofactors avoiding P+p bijectively onto the divisible
class. Real normalization gives g(Y)=f(Y)+p^-1*f(Y/p). Subtract p^-1*g(Y/p):
the result is f(Y)-p^-2*f(Y/p²). The corpus's divided-argument contraction
theorem applies because every normalized count is bounded by one (and is
zero at negative cutoffs). Its limiting multiplier simplifies to p/(p+1).
Induction over P starts from the unconditional squarefree density theorem.

For 0<=t<=1, the normalized survival count of magnitudes sqrt(r/N) equals
[A_P(N)-A_P(floor(N*t²))]/N. The density theorem makes it tend to
rho_P*(1-t²) for t>0; it lies between zero and one. The existing finite
polynomial layer-cake identity expresses the kth moment as its integral
against (k+1)*t^k. Dominated convergence on [0,1] gives 2*rho_P/(k+3).
Rescale the child cutoff floor(c*N), whose ratio to N tends to c.
Expanding the square proves the affine-square weighted limit.

The physical clipping identity makes each actual head block affine in
sqrt(M) and sqrt(r). Squaring gives r*I²=M*(a_n+b_n*sqrt(r/M))².
The quotient condition M/r=n is exactly M/(n+1)<r<=M/n. Therefore the
normalized cell energy is the difference of two affine-square prefix
sums. Apply their established limits at c=1/n and c=1/(n+1).

## Lean validation

New leaves: `FixedCoreSquarefreeDensity`, `FixedCoreSquarefreeMoments`,
and `MobiusDivisorFixedCoreBlockLimit`, all in `GaloisForLFunctions.RHTower`.
Twelve public theorems pass scratch checks and an external-scratch axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`. The formal lint gate passes, and the declaration index is refreshed. Leaves are wired into
`RHTower.lean`; only the three needed leaf oleans are emitted with
`lake env lean <file> -o <leaf.olean>`. No full or umbrella build is run.
The known Lake packaging audit remains pending to avoid its broad
prerequisite rebuild; exact-file verification is recorded separately.

Owned scratch files and validation logs are removed; no owned Lean process remains.
