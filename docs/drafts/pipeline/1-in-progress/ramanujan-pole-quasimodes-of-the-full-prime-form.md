# Ramanujan pole profiles are quasimodes of the full finite prime form

- **ID:** ramanujan-pole-quasimodes-of-the-full-prime-form
- **Stage:** 1-in-progress
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

Finite-sieve adjunction final checks remain active. This candidate is undergoing
its paper and implementation audit and is not counted.

## Additional checked bridges and proof design

The corpus already identifies the primitive-root Ramanujan sum with the real
BVI coefficient: TTPC `ramanujanSum_eq_ramanujanLagCoefficient` and
`ramanujanMode_eq_ramanujanLagCoefficient` in
`ParitySensitiveRamanujanStabilizerTransfer.lean`. BVI
`NonMarkovianLagOperatorAlgebraAndPrimePowerRevival.lean` supplies coprime
multiplicativity and the exact prime-power multiplier. Its
`RamanujanLagCoefficientAndTotientQuotient.lean` gives the gcd-divisor formula.
These discharge the arithmetic identification and unit-multiplication invariance
at the paper level; the eventual Lean bridge should reuse these exact results.
The local step equations and their proof were reread. No local mode formula is new.

RAPT `roundoff_le` in `TheFinitePartIsEulersConstant.lean` gives precisely
`0 <= log N-log(floor(N/n))-log n <= 1/floor(N/n)` for 1<=n<=N.
That module also supplies `mertensSum(y)-log(y) -> -gamma`.
The general real Cesaro-to-logarithmic mean theorem is
`RHTower.pm_tendsto_harmonic_average_of_mean` in
`PMPowerDampedMobiusCovarianceCancellation.lean`. RBG's periodic prefix bound
and the complete-period Gram give its hypotheses for every fixed pair of modes.

No explicit rate for a prime-power tail is needed. For a finite support Q set
`T_p(y)=sum_(a>=1,p^a>y) p^(-a)`. Geometric summability and exhaustion of each
fixed exponent imply `T_p(y)->0`. If |g|<=B, the missing upward correction is
bounded by `2B sum_(p in Q) log(p) T_p(y)`, uniformly in the row n.
Together with Mertens and roundoff this gives a nonnegative function
`F(y)=B*(|mertensSum(y)-log(y)+gamma|+1/y)
      +2B sum_(p in Q)log(p)T_p(y)` tending to zero, with
`|rowResidual(N,n)| <= F(floor(N/n))/sqrt(n)`.
The existing harmonic boundary-layer bound applied to F squared then yields
the required squared residual limit. This avoids imposing a uniform pointwise
row limit near the upper edge of the horizon.

For a finite Hermitian matrix, expanding a nonzero vector x in an orthonormal
eigenbasis gives `min_j |lambda_j-mu| <= ||(A-mu)x||/||x||`: otherwise every
term of the squared residual expansion exceeds the claimed lower bound times
its squared coefficient. This elementary finite-dimensional lemma will be
formalized if no exact corpus instance is found. For a finite set of distinct
arithmetic energies, choose disjoint intervals smaller than one third of their
minimum separation. The residual limits eventually put an actual matrix
eigenvalue in each interval. The target should state the finite-packet result
with an arbitrary prescribed accuracy, and also retain the asymptotically
orthonormal Ramanujan vectors, rather than claim an ordering of the full spectrum.

Additional novelty query restricted to RAPT returned the existing coarse pole
row bound, local tower equations, and the current supported-integer operator;
no full-matrix Ramanujan residual theorem. Whole-corpus and neighbouring
programme exclusions remain part of the final novelty audit.

The exact quotient limit already exists as
`RHTower.tendsto_harmonicQuotientMean_div_log` in
`RHTower/HarmonicQuotientToeplitz.lean`; its complete source was checked.
A convergent squared majorant is bounded automatically, so it directly supplies
the residual averaging step. No new generic harmonic quotient theorem is needed.

Whole-corpus queries excluding RAPT also returned unrelated objects: the BVI
Ramanujan evaluation/prefix matrix, PM primitive/divisor-energy kernels, and CCM
Guinand-Weil source matrices. The CCM completed-source card was read: it reconstructs
a restricted-Weil matrix on centered cosine modes, not the matrix on positive
integer orders used here. The TTPC parity-twin card was read through its stated
results and proof mechanisms: it computes Abel/digamma germ limits and a local
short-cycle positivity statement, not full prime-matrix quasimodes. AIT search
returned the existing local tower/KMS identities and the literal prime-form
sum over towers. None supplies the present norm-residual limit.

## Paper proof under implementation audit

Fix m>=1 and put g(n)=c_m(n)/sqrt(phi(m)), k_p=v_p(m),
Q={p:p divides m}, and kappa=log(m)+tameDifferent(m). The BVI multiplicativity
and prime-power formula give

`g(n)=product_(p in Q) sqrt(phi(p^k_p))*valuationStep(p,k_p,v_p(n))`.

In particular g is bounded, real, m-periodic, and unchanged by multiplication
or division by a prime power coprime to m. Let B>=0 bound |g|.

For any real profile g, literal divisibility reindexing of the prime row gives

`sum_(j<=N) P(n,j)g(j)/sqrt(j)`
`=1/sqrt(n) * [sum_(t<=N/n) Lambda(t)g(nt)/t
                 +sum_(d divides n) Lambda(d)g(n/d)]`.

The factor n is positive and n<=N. The upward sum includes t=1 harmlessly;
the downward sum includes d=1 harmlessly, because Lambda(1)=0. Subtract g(n)
inside both sums and use `sum_(d divides n)Lambda(d)=log(n)`. This yields

`1/sqrt(n)*[(Mertens(N/n)+log(n))g(n)+C_(N/n)(g,n)]`,

where C_y is the finite upward difference plus the exact downward difference.
The scratch `ThePrimeRowsReadPoleProfiles.lean` implements this exact identity
for arbitrary g; it has not yet been checked.

The upward difference has an absolutely convergent completion: nonzero terms
have t=p^a with p in Q, and their absolute sum is at most
`2B sum_(p in Q)log(p)/(p-1)`. Define C_infinity by this completion. Changing
only the p-adic valuation leaves every other product factor fixed. Thus its
p-component is log(p) times

`L_p y(v)=sum_(a>=1)p^(-a)(y(v+a)-y(v))
           +sum_(a=1..v)(y(v-a)-y(v))`.

For y=valuationStep(p,k), k>=1, the already proved tower equation says
`L_p y=-(k+1/(p-1))*y`. Directly: below k-1 the one negative upward term cancels
the geometric tail; at k-1 the upward tail and k-1 downward terms give the
same multiplier; at v>=k the downward terms contribute
`-p/(p-1)-(k-1)=-(k+1/(p-1))`, and the upward terms vanish.
Multiplying by the other local factors and summing p gives
`C_infinity(g,n)=-kappa*g(n)`. For m=1 the product and Q are empty,
g=1, kappa=0, and both differences vanish identically.

Let `T_p(y)=sum_(a>=1,p^a>y)p^(-a)` and
`T(y)=2B sum_(p in Q)log(p)T_p(y)`. Absolute convergence gives
`|C_y(g,n)-C_infinity(g,n)|<=T(y)` for every n>=1, independently of n.
Every T_p tends to zero by exhaustion of the summable geometric series;
Q is finite, so T tends to zero. Mertens gives
`e(y)=Mertens(y)-log(y)+gamma -> 0`. The exact roundoff theorem gives
`0<=r(N,n)=log(N)-log(N/n)-log(n)<=1/(N/n)`.
Consequently, with E=gamma+kappa,

`|sum_(j<=N)P(n,j)u(j)-(log(N)-E)u(n)|
 <= [B*(|e(N/n)|+1/(N/n))+T(N/n)]/sqrt(n)`.

The bracket is F(N/n) with F->0. The actual squared residual is nonnegative
and at most `sum_(n<=N)F(N/n)^2/n`. Apply the existing complementary-quotient
harmonic mean theorem to the bounded convergent sequence F squared. Division
by log(N) makes the upper bound tend to zero, proving the target residual limit.

For two fixed conductors m,l, take common period q=m*l. Complete-period
orthogonality gives mean(g_m*g_l)=1 if m=l and 0 otherwise. Subtract that mean;
periodicity bounds every partial sum of the resulting sequence by a fixed
constant. Dividing by N proves its Cesaro mean is zero. The existing
Cesaro-to-logarithmic theorem therefore gives
`sum_(n<=N)g_m(n)g_l(n)/n/log(N) -> [m=l]`.
This proves the norm and cross-inner-product limits of the actual pole profiles.

Finally expand any nonzero vector x in a finite Hermitian eigenbasis. Its
squared residual at mu is
`sum_j (lambda_j-mu)^2*|<e_j,x>|^2`, while its squared norm is
`sum_j |<e_j,x>|^2`. At least one eigenvalue therefore has distance at most
the residual/norm ratio. For each fixed m that ratio tends to zero by the two
limits already proved. Distinct arithmetic energies are separated: choose a
finite prime set containing all prime factors of a fixed finite packet and
apply the proved finite-sieve energy injectivity. With disjoint intervals about
`log(N)-E(m)`, simultaneous eventual residual bounds provide distinct literal
P_N eigenvalues, at every prescribed accuracy. No statement about the other
matrix eigenvalues is used or follows.

All dependencies in this paper argument are identified; the remaining audit is
exact Lean realization of the row correction, arithmetic product identification,
uniform tail estimate, and finite-dimensional spectral transfer. This card stays
in progress and uncounted while those are implemented.
