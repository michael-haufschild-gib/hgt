# PM: the coupled prime-square source

- **ID:** PM-prime-square-coupled-source
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `../../../../../reports/rh-current-frontier-map.md`, route PM; predecessor `pm-logarithmic-covariance-balance.md`.
- **Statement:** Determine the actual prime core on the square-scale slab, retaining its prime convolution and semiprime sector together.

## Goal

The full open problem remains a lower bound for the complete signed compensation
`M_epsilon(N)-Q_epsilon(N)/2`. The first-band theorem controls the dilated factor
`F_<p(p*t)` when `1/t` lies in `[3*p^2/2,7*p^2/4]`; the paired factor `F_<p(t)`
is now uniformly negative by the audited theorem below. This card continues with the resulting negative mixed current. A local sign theorem alone would
not give the required global compensation or RH.

## Gates

- [x] 0 → 1: actual source, explicit scale and analytic mechanism.
- [ ] 1 → 2: complete audited paper proof, no open dependency.
- [ ] 2 → 3: exact theorem formalized, targeted build and axiom audit.

## Corpus inputs

- `PMPowerDampedMobiusPrimeSlabBounds`: uniform first-band approximation and
  positive lower bound for the literal prime core.
- `PMRamanujanComplementarySourceBounds`: unconditional `log^4` saving for the
  actual divisor remainder. The floor correction and centered difference
  extend this to the actual reciprocal source.
- `PMPowerDampedMobiusMellin.hasMellin_pmPowerDampedFermiSource`: exact quotient
  on `max(0,1-epsilon)<Re(s)<1`.
- `Sieve.PrimeCountingBigO.primeCounting_sub_logIntegral_isBigO`: unconditional
  error `O(x*exp(-c*sqrt(log x)))`, with some `c>0`.
- `PMPowerDampedMobiusDivisorHaar`: actual divisor coefficients lie in `[0,1]`;
  the reciprocal source is their dyadic count difference.

Searches201–202 completed; search203 was partial after a semantic-worker
disconnect. Inventories complete (65259,65260,65264 files respectively), compiler
freshness mixed, semantic coverage unmeasured, background refresh incomplete.
All returned candidate/source statements and ingredient groups were inspected.
The suggested Sonin continuation chain in203 does not prove this boundary
moment. Direct source inspection established the exact PNT theorem above.
The existing terminal-band weighted PNT theorem assumes a nondecreasing power
weight and does not directly cover this signed step-function weight.

Searches204–206 completed (inventories65267,65275,65276). All twenty candidate
and twenty source statements and proposed groups in each were inspected.
Compiler freshness remains mixed, semantic coverage unmeasured, refresh
incomplete. The proposed L2 boundary-decay chain in204 requires the admission
being sought and was not used. The prime-leakage chain in205 concerns a
different source. Search206 supplies finite floor-interchange patterns and
the actual first-band identity; it does not supply the weighted prime-head
transfer or the square-band sign.

## Proposed proof, with obligations kept explicit

Fix `0<epsilon<1/2`; put `a=1-epsilon`, `f(u)=A_epsilon(1/u)`, and `L=log x`.
For `x=y*P^2`, with `y` in `[3/2,7/4]`, finite rough inversion predicts

`F_<P(1/x)=f(x)+sum_(P<=q<=x, q prime) q^(-epsilon)*f(x/q)`

`            +sum_(P<=q<=r, q,r prime, q*r<=x) (q*r)^(-epsilon)`.

This finite identity, proposed in the predecessor log, is now audited in
`PMPowerDampedMobiusPrimeSquareDecomposition.lean`. Repeated prime factors, especially squares, must be
included. The existing semiprime-cell API counts distinct primes and cannot
silently replace this sum.

### Subexponential cofactor split

Choose `1/3<alpha<1/2` and `H=exp(L^alpha)`. On the prime head `q>=x/H`,
the PNT error in Stieltjes partial summation is bounded by

`O(x^a * (1+H^epsilon) * exp(-c'*sqrt(L)))`.

Reason: every jump of `f` is bounded by an absolute constant, since its two
divisor-count jumps have coefficients in `[0,1]`. A jump at cofactor `n`
costs `O((x/n)^a*exp(-c'*sqrt(L)))`; summing `n<=H` costs `O(H^epsilon)`.
The smooth derivative of `q^(-epsilon)` obeys the same bound. Because
`alpha<1/2`, this error is `o(x^a/L^2)`. Unlike a power cutoff `H=P^delta`,
this split absorbs the variation loss.

On the tail `P<=q<x/H`, the source bound gives
`|q^(-epsilon)f(x/q)| <= C*x^a/(q*log(x/q)^4)`.
Partition cofactor space into `[e^j*H,e^(j+1)*H)`. Prime counting contributes
`1/log q=O(1/L)` throughout this square scale. Consequently the absolute tail
is `O(x^a/(L*(log H)^3))=o(x^a/L^2)`, since `alpha>1/3`.
Dropping that prime-density factor would give an insufficient estimate.
The corresponding integral tail has the same bound.

These estimates would justify, uniformly in the stated slab,

`sum q^(-epsilon)f(x/q)`
` = x^a * integral_1^(x/P) f(u)*u^(epsilon-2)/(L-log u) du + o(x^a/L^2)`.

### Boundary moments

The needed identities are

`integral_1^infinity f(u)*u^(epsilon-2) du = 0`,

`integral_1^infinity f(u)*u^(epsilon-2)*log u du = -D_epsilon`,

`D_epsilon=(1-2^epsilon)*zeta(1-epsilon)/(1-epsilon)`.

They are NOT imported as premises. Proposed proof: the source log-four bound
gives absolute convergence with zero, one, and two logarithmic factors. Approach
`s=a` from the right in the verified Mellin quotient, using the zeta residue at
one; differentiate from the right by a dominated difference quotient. This
requires a boundary argument, not the interior Mellin differentiation theorem.

Expanding `1/(L-log u)` to first order leaves an error bounded by
`2/L^3` times the absolute second logarithmic moment, because
`log(x/P)/L` is eventually bounded away from one. The removed zeroth/first
moment tails are `O(L^-3)`/`O(L^-2)`. Thus the proposed asymptotic is

`sum_(P<=q<=x, q prime) q^(-epsilon)f(x/q)`
` = -D_epsilon*x^a/L^2 + o(x^a/L^2)`.

### Joint sign target

At `epsilon` tending to zero, the residue identity predicts
`D_epsilon -> log 2`. A useful upper bound for the semiprime term is one half
the square of the number of primes in `[P,y*P]`, times `P^(-2*epsilon)`, plus
the prime-square diagonal. Its normalized limsup is at most `(y-1)^2/2`.
The diagonal is smaller by a power of `P`. Therefore, for all sufficiently
small positive damping, the predicted square-slab core is uniformly NEGATIVE,
of size `P^(2-2*epsilon)/log(P)^2`, while its paired first-band factor is positive.
The symbolic inequalities `log 2>2/3` and
`3*(y-1)^2<y` on `[3/2,7/4]` give a uniform strict gap at damping zero.
This is a proposed proof mechanism, not a numerical experiment or an already
verified sign theorem.

## Remaining work

Boundary moments, prime convolution, rough inversion, square-inclusive
decomposition and the uniform negative core are now fully audited; see
`../../../3-formalized/pm-prime-square-source-sign.md`. Quantify the negative
mixed-current mass and determine how it is compensated across prime scales.
The local theorem does not bound the complete signed current.

## Detailed paper audit of the proposed estimates

The Stieltjes head error can be bounded without an unproved variation estimate.
Write `E(v)=pi(v)-Li(v)`. On `[x/H,x]`, the PNT gives
`|E(v)|<=C*v*exp(-c'*sqrt(L))` for all sufficiently large `x`, uniformly in
the slab. Between cofactor jumps, the derivative of
`h(v)=v^(-epsilon)*f(x/v)` is `-epsilon*v^(-epsilon-1)*f(x/v)`.
The elementary count bound `|f(u)|<=2*u` gives
`integral |E(v)*h'(v)| dv <= C_epsilon*x^a*H^epsilon*exp(-c'*sqrt(L))`.
The endpoint terms satisfy the same estimate. A jump at `v=x/n` has size
at most `3*(x/n)^(-epsilon)`, hence costs at most
`3*C*x^a*n^(-a)*exp(-c'*sqrt(L))`. Integral comparison bounds the sum by
`C_epsilon*x^a*(1+H^epsilon)*exp(-c'*sqrt(L))`.
Endpoints that are primes or cofactor jumps contribute at most this same
bound; the choice of closed or half-open finite intervals is harmless only
after this endpoint estimate is included.

For the tail, set `U=e^j*H`. A cofactor block `[U,e*U)` has primes in
`(x/(e*U),x/U]`, truncated below by `P`. Their count is at most
`C*x/(U*log(x/U))`, and every reciprocal prime weight is at most `e*U/x`.
Because `U<=x/P`, `log(x/U)>=log P` is a fixed positive fraction of `L`.
The block contribution is at most `C*x^a/(L*(log H+j)^4)`. Summing and
comparing with the integral of `(log H+t)^(-4)` gives the claimed tail.
The integral tail follows by `v=log u` and `L-v>=log P`.

The Mellin boundary calculation uses the regularized residue
`U(s)=(s-1)*zeta(s)`, extended by `U(1)=1`; its analyticity is already
formalized in `ZetaLogDerivResidue`. The quotient gives exactly

`Mellin(A)(a+delta)/delta`
` = (1-2^(epsilon-delta))*zeta(a+delta)/((a+delta)*U(1+delta))`.

Absolute domination by the log-four envelope makes its boundary mass the
limit of `Mellin(A)(a+delta)`, hence zero. The difference quotient is dominated
by the first absolute log moment, using
`|(exp(-delta*log u)-1)/delta|<=log u` for `delta>0,u>=1`.
Its limit is minus the first signed log moment. Thus that moment equals
`-D_epsilon`. This is a one-sided argument and assumes no continuation
to the left of the boundary.

For the uniform denominator expansion, `v=log u<=log(x/P)` and
`L-v>=log P` give
`1/(L-v)=1/L+v/L^2+v^2/(L^2*(L-v))`.
The last integral is bounded by a constant times the absolute second log
moment divided by `L^3`. The omitted zeroth and first moment tails are
`O((log(x/P))^-3)` and `O((log(x/P))^-2)`, respectively. This proves the
stated prime-convolution asymptotic at paper level once the source envelope
has been extended from integer remainders to real reciprocal arguments.
The source value `f(x)` itself is `O(x^a/L^4)`.

For the semiprime upper bound let `J` be the number of primes in `[P,y*P]`.
Every admissible prime pair belongs to this interval and has weight at most
`P^(-2*epsilon)`. Thus the term is at most
`P^(-2*epsilon)*(J^2+J)/2`; this includes squares. PNT uniformly on
`y in [3/2,7/4]` gives `J*log P/P -> y-1`. After normalization, the linear
`J` term vanishes. No squarefree substitution is used.

Finally, `D_epsilon -> log 2` follows by factoring through
`U(1-epsilon)` and the derivative of `2^epsilon` at zero. Choose positive
`epsilon` sufficiently small that
`Re(D_epsilon)*(7/4)^(-epsilon)>2/3`. Then the normalized limiting upper
bound is at most
`-y/6+(y-1)^2/2 <= -1/96` throughout the slab: the concave quadratic
`y-3*(y-1)^2` has minimum `1/16` at the upper endpoint. Uniform error
control leaves a strict negative bound for all sufficiently large `P`.

This paper audit identifies no unpaid RH-type input, but the card stays in
progress until the boundary integrals, Stieltjes step-weight transfer, and
rough inversion have been checked in Lean. The result is not a global
compensation theorem.

### Simpler finite-head implementation

For Lean, the head transfer need not implement general bounded variation.
The exact divisor-count formula expands `f(x/q)` into two finite sums with
coefficients in `[0,1]`, at cutoffs `x/n` and `x/(2*n)`. Swapping these finite
sums reduces the head error to at most `3*floor(H)` weighted prime-band
errors, all with endpoints in `[x/H,x]`. The existing
`PrimeRpowStrongPNTBandTransfer.abs_primeRpowSumIoc_diff_sub_logRpowIntegral_diff_le`
allows arbitrary real exponents; only its later terminal-band corollary
assumes a nondecreasing weight. Apply the general theorem at `a=1-epsilon`.
Crude uniform bounds on the weight, derivative, and Chebyshev error give
`O_epsilon(x^a*H^(epsilon+2)*exp(-c'*sqrt(L)))` after the finite sum.
This larger subexponential loss is still absorbed when `alpha<1/2` and
avoids introducing a new Stieltjes integration framework. The tail still
requires the retained prime-density factor proved above.

### Consequence for the complete mixed current, still pending Lean

The joint sign would be stronger than an isolated negative example. For
`p in [P,2*P]`, integrate on `t in [4/(7*p^2),2/(3*p^2)]`.
The square core is at most `-c*p^(2-2*epsilon)/log(p)^2`; the first-band
dilated core is real and at least `c'*p^(1-epsilon)/log p`. Including the
prime-update weight `p^(-epsilon)` and the interval length gives a negative
contribution of size at least `c''*p^(1-4*epsilon)/log(p)^3` per prime.
Prime-window counting then gives size `P^(2-4*epsilon)/log(P)^4`.
These intervals all lie above the full-current cutoff `1/(8*P^2)`.
Thus, if the joint sign is formalized, the negative part of the mixed current
itself has a positive power lower bound for small damping. A successful PM
producer must compensate it with positive mixed contributions across scales;
bounding the negative part separately by every positive power cannot work.
This consequence has not yet been used as a Lean premise or declared proved.

## Log

- 2026-10-04: subexponential split repairs the previously identified variation
  loss on paper; precise proof obligations recorded before formalization.
- 2026-10-04: actual boundary moments formalized and audited; next producer is
  the signed prime-convolution transfer, with its full tail retained.

### Direct tail Abel proof (2026-10-04; paper, Lean pending)

Search207 completed with all twenty candidate/source statements inspected
(inventory65282, compiler freshness mixed, semantic coverage unavailable,
background refresh incomplete). Its suggested Gaussian Abel identity is not
an estimate for this source. The useful inputs are the actual theta linear
bound and finite Abel summation. Search208 likewise completed with all returned
statements inspected (inventory65289); the proposed algebraic Jacobian lemma
is unrelated. The one-dimensional measurable change-of-variables theorem
used by `ArchimedeanMellinFourier` does apply to the head integral.

The tail can avoid a separate dyadic-partition formalization. For
`2<=a<=b` and `log(X/b)>=8`, set
`v(t)=log(X/t)` and `g(t)=1/(t*v(t)^4*log t)`.
Then `g>=0`, and differentiation gives

`-g'(t) = ((v(t)-4)*log t+v(t))/(t^2*v(t)^5*(log t)^2) >= 0`.

Use the actual unconditional `theta(t)<=C*t`. Abel summation gives

`sum_(a<p<=b) 1/(p*v(p)^4)`
` <= C*(b*g(b) + integral_a^b (-g'(t))*t dt)`
` = C*(a*g(a) + integral_a^b g(t) dt)`.

The lower endpoint has nonnegative theta mass and was discarded with its
negative sign; the displayed integration-by-parts equality retains the upper
boundary term before cancellation. Thus

`sum <= C/log(a) * (1/v(a)^4 + (1/v(b)^3-1/v(a)^3)/3)`
`     <= 2*C/(log(a)*v(b)^3)`.

The primitive used here is `1/(3*(log(X/t))^3)`. Choosing `a=P/2` includes
the prime `P` and still has `log(a)` comparable to `log(P)`. Multiplication
by the audited actual-source log-four envelope gives the required tail
`O(X^(1-epsilon)/(log(P)*(log H)^3))`. This corrects the tempting but
incorrect endpoint simplification with `b*g(b)` alone: the final boundary
term is `a*g(a)`.

The prime-head draft now has an exact finite divisor/prime interchange and
an exact finite divisor/integral interchange. Its intended unconditional
export compares the actual signed source on `(u,X]` to its integral with
error `K*X^3*u^(-epsilon-2)*exp(-c*sqrt(log X))`. Setting `u=X/H` gives
`K*X^(1-epsilon)*H^(epsilon+2)*exp(-c*sqrt(log X))`.
The three head exports now live in `PMPowerDampedMobiusPrimeHead.lean`:
`pmPowerDampedFermiSource_prime_head_transfer`,
`pmPowerDampedFermiSource_prime_head_integral`, and
`pmPowerDampedFermiSource_prime_cofactor_transfer`. Targeted `--old` leaf
build, final actual-file Lean check, and three-export axiom audit passed.
Only the standard three axioms occur. Full certificate:
`../../../3-formalized/pm-signed-prime-head-transfer.md`.
The module is wired once and indexed. Global lint reports thirteen unrelated
unreachable modules, including `RoutePNativeMassPrefixMoments`; no PM failure.

### Use the head kernel directly (2026-10-04)

The full convolution asymptotic does not require transferring its entire
integral up to `X/P`. The newly checked head formula already has upper
cofactor cutoff `H=exp((log X)^alpha)`. Expand that kernel directly:

`integral_1^H w/(L-log u)`
` = (integral_1^H w)/L + (integral_1^H w*log u)/L^2 + remainder`.

The second absolute logarithmic moment bounds the remainder by `2*M2/L^3`
when `H<=sqrt(X)`. The first truncated logarithmic moment tends to `-D`.
Zero total mass and the log-four source envelope give
`|integral_1^H w|=|integral_H^infinity w|<=C/(log H)^3`.
Thus the zeroth-moment term is `O(L^(-1-3*alpha))`, which is `o(L^-2)` for
`alpha>1/3`. The prime tail has the same order after retaining `1/log P`.
This removes the separate long-range integral-tail transfer from the Lean
obligations. The quantitative zeroth-moment tail remains necessary:
absolute second-moment admission alone gives only `o((log H)^-2)`, which
would not suffice for any fixed `alpha<1/2`.

Search209 completed and all returned candidate/source statements and proposed
groups were inspected (inventory65309, mixed compiler freshness, semantic
coverage unavailable, background refresh incomplete). The rough Lambert
support-cardinality law in `MobiusRoughLambertBoundary` concerns a different
coefficient and does not supply the positive rough indicator needed here.
The applicable finite ingredients remain `CoprimeMobius.sum_divisors_mobiusAF`,
Möbius/zeta inversion, and divisor-antidiagonal interchange. The proposed
incidence-algebra chain was not treated as a proof of the actual PM identity.

For the remaining finite inversion, a divisor-count implementation can avoid
new Fermi-dilation infrastructure. First prove `mu*rough=mu_<P` as arithmetic
functions, damp the divisor convolution using complete multiplicativity of
`n^(-epsilon)`, then convolve with zeta. This yields
`c_<P,epsilon = c_epsilon * rough_epsilon`. Finite divisor-antidiagonal
interchange gives the summatory identity; its dyadic difference is exactly
the required source identity. The semiprime bound must retain the factor
one half and the square diagonal `(J^2+J)/2`: the weaker `J^2` bound does
not close the uniform sign on the whole chosen slab.

An even shorter kernel limit uses dominated convergence after centering the
kernel. On `1<u<=H<=sqrt(X)`, with `v=log u`,

`L^2/(L-v)-L = v*L/(L-v)`, whose absolute value is at most `2*v`.

The centered truncated integrand therefore tends pointwise to `v*w(u)` and
is dominated by the already admitted first absolute logarithmic moment.
Its integral tends to `-D`. The remaining term is `L*integral_1^H w`,
which tends to zero by the quantitative mass tail above. This avoids an
explicit second-order remainder in Lean; the audited second moment remains
available but is not needed for this shorter limiting argument.


The actual-source prime tail is now formalized in
`PMPowerDampedMobiusPrimeTail.lean`, with three audited exports:
`pm_prime_log_cofactor_tail`, `pmPowerDampedFermiSource_prime_tail_bound`,
and `pmPowerDampedBoundaryWeight_mass_tail_bound`. Targeted old leaf build,
final actual-file Lean check, three-export axiom audit and index passed.
Only the standard three axioms occur. The leaf is wired once; global lint
reports eighteen unrelated unreachable modules and no PM failure.
Certificate: `../../../3-formalized/pm-prime-and-boundary-tails.md`.

The quantitative boundary mass tail needs no new fourth-log primitive.
For `x>=H>1`,
`1/(x*log(x)^4) <= log(H)^(-2)/(x*log(x)^2)`.
The existing root theorem `integral_inv_div_log_sq_Ioi` integrates the
right-hand side to `log(H)^(-3)`. Combined with the actual source envelope,
this bounds the tail of `w` and then its signed mass. This deliberately
uses a coarse constant; only the third logarithmic power matters.

Uniform semiprime counting can use the existing relative theta estimate,
without a new uniform prime-counting asymptotic. If `J` counts primes in
`[P,y*P]`, then `J*log(P)<=theta(y*P)-theta(P)+log(P)`; the last term retains
the possible prime endpoint `P`. A common relative theta error `delta` at
both arguments gives
`J*log(P)/P <= y-1+delta*(y+1)+log(P)/P` uniformly on the chosen compact
`y` slab. This retains the dependence on `y` needed for the joint quadratic
sign. Replacing `y` independently by opposite slab endpoints would lose
that sign margin.

### Quantitative centered kernel (2026-10-04)

The audited absolute second moment gives a direct finite remainder bound.
Let `r=Re(w_epsilon)`, `z=log(x)`, and let `M2` dominate
`integral_1^infinity |r(x)|*z^2 dx`. For `H>1` and `L>=2*log(H)`,

`L^2/(L-z) = L+z+z^2/(L-z)` on `(1,H]`.

The last term has absolute integral at most `2*M2/L`. The omitted first
moment has absolute integral at most `M2/log(H)`. Zero total mass and the
quantitative mass-tail estimate give `|L*integral_1^H r|<=C*L/log(H)^3`.
Consequently

`|L^2*integral_1^H r(x)/(L-log(x)) dx+Re(D_epsilon)|`
` <= C*L/log(H)^3+M2/log(H)+2*M2/L`.

This is a paper proof of the actual-source kernel asymptotic, without a
new dominated-convergence theorem. Taking `L=s^5` and `H=exp(s^2)` makes
the three errors multiples of `1/s`, `1/s^2`, and `1/s^5`. The prime-head
exponential saving survives this cutoff. This parameterization avoids
fractional-power bookkeeping; it does not assume or weaken the desired
prime convolution limit. Both the finite estimate and parameterized limit
are now formalized in `PMPowerDampedMobiusBoundaryKernel.lean`. Targeted old
leaf build, final actual-file Lean check and both axiom audits passed
(standard three only). The module is wired once and indexed. Global lint
reports twelve unrelated unreachable modules, no PM failure. Certificate:
`../../../3-formalized/pm-actual-boundary-kernel.md`.

Search210 inspected all twenty candidate statements, twenty source-argument
statements and the proposed ingredient group. Inventory65331 was complete;
compiler freshness mixed, semantic coverage unmeasured, refresh incomplete.
The proposed theta/contour zero-integral chain concerns different functions
and does not prove this kernel estimate. The actual PM moment theorems and
the finite scalar kernel identity remain the applicable inputs.

### Complete prime-convolution draft (2026-10-04)

The new draft `/tmp/pm_prime_convolution_work.lean` combines the audited
head, tail and kernel theorems. Its proposed finite estimate is uniform in
`R<=H<=sqrt(X)` and `2<=a<=X/H`. After multiplication by
`log(X)^2/X^(1-epsilon)`, the error from `-Re(D_epsilon)` is at most

`K*(log(X)/log(H)^3+1/log(H)+1/log(X)`
`  +log(X)^2*H^(epsilon+2)*exp(-c*sqrt(log(X)))`
`  +log(X)^2/(log(a)*log(H)^3))`.

Taking `X=exp(s^5),H=exp(s^2)` makes the kernel errors vanish. Uniformly
for `sqrt(X)/2<=a<=sqrt(X)`, `log(a)>=s^5/4` eventually, so the last error
is at most `4/s`. Eventually `c*sqrt(s^5)>=(epsilon+3)*s^2`; hence the
prime-head error is at most `s^10*exp(-s^2)`, which also vanishes.
The inverse substitution `s=(log X)^(1/5)` covers every sufficiently large
real `X`, not merely a sequence. This paper proof identifies the full
signed prime convolution uniformly throughout the required cutoff band.
The complete convolution is now audited in
`PMPowerDampedMobiusPrimeConvolution.lean`: finite error, uniform parameter
limit and all-real-X asymptotic. Targeted old leaf build, final actual-file
Lean check and all four public-declaration axiom audits passed (standard
three only). Wired once, indexed; global lint twelve unrelated unreachable
modules, no PM failure. Certificate:
`../../../3-formalized/pm-signed-prime-convolution.md`.
Finite rough inversion and the semiprime sector remain.

### Direct finite rough inversion (2026-10-04)

Search211 returned partial deep results, with complete inventory65348,
mixed compiler freshness, semantic coverage unmeasured and refresh
incomplete. All twenty candidate and twenty source-argument statements and
the proposed group were inspected. The suggested damping factors concern
other functions; the useful ingredients are actual arithmetic-function
convolution and finite divisor-antidiagonal interchange.

A shorter source-level implementation avoids a new damping ring homomorphism
and avoids introducing an intermediate divisor-count source. With
`E=complement(S)`, the existing divisor identity says
`mobiusAF(E)*zeta=smoothAF(E)`. Möbius inversion therefore gives
`mu*smoothAF(E)=mobiusAF(E)`, whose coefficient is exactly the finite-prime
aperture coefficient. Expand each actual source in its finite Fermi sum.
The identity `G_d(m*t)=G_(m*d)(t)` and complete multiplicativity of
`n^(-epsilon)` turn the positive rough dilation sum into this convolution.
The existing `sum_Icc_divisorsAntidiagonal_swap` performs the exact finite
reindexing. Consequently

`F_S(t)=sum_(m<=floor(1/t)) smoothAF(complement(S),m)*m^(-epsilon)*A(m*t)`.

This preserves every prime power and repeated prime. It is a paper-proof
implementation plan grounded in the literal finite-source expansions;
the exact rough identity is now formalized and audited in
`PMPowerDampedMobiusRoughInverse.lean`. Targeted old leaf build, final
actual-file Lean check and axiom audit passed (standard three only). Wired
once and indexed; global lint twelve unrelated unreachable modules, no PM
failure. Certificate: `../../../3-formalized/pm-exact-rough-inverse.md`.

Search212 inspected all twenty candidate and twenty source statements and
the proposed group (inventory65351 complete, compiler freshness mixed,
semantic coverage unmeasured, refresh incomplete). The `PrimeCells`
semiprime set requires distinct factors and cannot represent this source's
square diagonal. The proposed prime-square-multiple counting chain does
not supply the needed rough-factor classification. Applicable local APIs
include `Nat.minFac_prime`, `Nat.not_prime_iff_exists_mul_eq`,
`Finset.card_sym2` and `Sym2.mul`.

The next scratch `/tmp/pm_prime_square_work.lean` starts with the exact
classification: a positive integer with all prime divisors at least P and
less than P^3 is 1, prime, or an ordered product p*q with P<=p<=q. Its first
Lean check is running. Below 2*P^2 (P>=2), this is exhaustive. The finite
semiprime set can be covered by the product image of the prime set's
`sym2`; image cardinality is at most `choose(J+1,2)`. This retains the
square diagonal without requiring a new uniqueness-of-factorization map.

The rough-below-cube classification now passes Lean. Its first attempt's
`simp_all` recursed through the min-factor product identity; explicit zero
and unit-factor contradictions fixed this without any resource-limit change.
The scratch now includes the actual prime-square source decomposition and
`pmPrimeSquareRoughMass`: positive mass of rough, nonprime, nonunit integers.
In the current range the checked classification identifies all of them
with two-prime products, including squares. The decomposition uses the
existing `pmPowerDampedFermiSource_first_band` to make each such source
term exactly one. That extended draft is undergoing its first check.

The exact prime-square decomposition now passes Lean in the scratch. Its
indicator cases use explicit `if_pos`/`if_neg`: feeding a universally
quantified roughness proof to `simp` treated it as a rewrite rule for its
conclusion rather than replacing the whole indicator predicate. Explicit
case rewrites resolved that mismatch.

The draft now adds the square-inclusive weighted mass bound
`mass <= (J^2+J)/2 * P^(-2*epsilon)`, where J counts primes in `[P,X/P]`.
Each rough composite maps into the product image of the prime set's
`sym2`; every such integer is at least P^2. `Finset.card_sym2` and
`Nat.cast_choose_two` give the exact diagonal-inclusive factor. The
extended draft is undergoing its first check. Joint uniform sign remains.

The complete square-inclusive decomposition and weighted pair bound now
pass Lean. They have been placed in
`PMPowerDampedMobiusPrimeSquareDecomposition.lean` with explicit minimal
imports (RoughInverse, Mean, finite symmetric pairs and binomial casts),
wired once, and submitted to the targeted old leaf build. Final actual-file
and axiom audits remain.

Search213 inspected all twenty candidate and source statements, the proof
idea and proposed group (inventory65356 complete, compiler freshness mixed,
semantic coverage unmeasured, refresh incomplete). The log-integral and
Littlewood chain is not the uniform local prime count needed here. The
applicable corpus result is `chebyshevTheta_eventually_relative`, found
through the already used prime-power bound; exact shell sums retain the
lower endpoint.

For the remaining uniform prime count, using `theta(y*P)-theta(P-1)`
directly includes the possible prime P. The relative theta estimate at
both endpoints gives, for every delta>0 and all sufficiently large natural
P, uniformly for y>=1,

`J*log(P)/P <= y-1+delta*(y+1)+1/P`,

where J counts primes in `[P,y*P]`. This preserves the needed y dependence
and avoids a separate endpoint correction by log(P). Its paper proof is
the finite comparison `J*log(P)<=sum log(q)` followed by the two relative
theta bounds. This and the actual convolution asymptotic are the remaining
analytic ingredients for the joint sign, not numerical experimentation.

For the joint sign it is cleaner to normalize the entire core by
`X^(1-epsilon)/log(X)^2`, matching the already audited prime-convolution
limit. Write `y=X/P^2`. The limiting normalized semiprime bound is
`2*(y-1)^2*y^(epsilon-1)`, at most
`(7/4)^epsilon*9/14` on `3/2<=y<=7/4`.
The rational inequality is exact:
`2*(y-1)^2-(9/14)*y = 2*(y-7/4)*(y-4/7) <= 0`.
Since `Re(D_epsilon)*(7/4)^(-epsilon)>2/3` for sufficiently small positive
epsilon, this leaves a uniform gap at least `(7/4)^epsilon/42` before
the vanishing full-source, prime-convolution and counting errors. This
keeps the signed prime limit unchanged and postpones conversion to the
P-normalized scale until the later mixed-current integral.

### Prime-square decomposition audited (2026-10-04)

Targeted old leaf build, final actual-file Lean check and all-three-export
axiom audit passed (standard three only). Wired once, indexed; twelve
unrelated unreachable modules remain in global lint, no PM failure.
Certificate: `../../../3-formalized/pm-prime-square-source-decomposition.md`.
The exact decomposition and square-inclusive bound are now closed; the
uniform interval-count draft is being checked for the joint sign.

Search214 inspected all twenty candidate/source statements and proposed
group (inventory65358 complete, compiler freshness mixed, semantic coverage
unmeasured, refresh incomplete). The direct PM pair bound is applicable;
the proposed prime-incidence kernel is a different object and does not
supply this count. Existing squarefree semiprime estimates also omit the
diagonal. The endpoint-correct uniform prime-count theorem now passes
Lean in the scratch. The mass normalization uses the actual pair bound,
log(y*P^2)/log(P) -> 2 uniformly on the slab, and the exact polynomial
inequality recorded above. Its first broad arithmetic proof exhausted the
default heartbeat budget; explicit local inequalities replace that tactic
search, with no resource-limit increase.

The uniform rough-composite upper limit now passes Lean:
for every epsilon>=0 and delta>0, eventually in P and uniformly for
3/2<=y<=7/4, normalized mass is at most `(7/4)^epsilon*(9/14+delta)`.
The proof retains both the pair diagonal and the y-dependent count.
All arithmetic runs under the default heartbeat limit after restricting
tactics to their local inequalities.

The complete negative-core draft now combines this bound with the existing
prime-convolution asymptotic, the full-source log-four envelope, and the
boundary-jet limit. The lower prime cutoff is exactly P-1, so the possible
prime P is included. The normalized error allocation leaves a fixed
positive gap; no numerical experiment is involved. The target is eventual
in positive epsilon, with an explicit positive constant and uniformity over
the entire square slab. It is being checked in the same scratch.

### Uniform negative source passed (2026-10-04)

`PMPowerDampedMobiusPrimeSquareSign.lean` passed the targeted old leaf build
(only this leaf newly built) and the final actual-file `lake env lean`
check with empty output. All three exports are indexed and wired once.
Axiom audit is running. Global lint currently reports nineteen unrelated
unreachable modules, no PM failure; it is not a global lint pass.

The literal source theorem is eventual as epsilon approaches zero from the
right: some c>0 satisfies, eventually for every natural P and uniformly
for 3/2<=y<=7/4,

`Re F_<P,epsilon(1/(y*P^2)) <= -c*(y*P^2)^(1-epsilon)/log(y*P^2)^2`.

The proof closes all formerly open local dependencies: endpoint-correct
counting, square-inclusive semiprime mass, signed prime convolution,
source remainder and small-damping boundary-jet gap. RH and complete
signed-energy compensation are still open.

Search215 inspected twenty candidate/source statements and its proposed
group (inventory65364 complete, mixed compiler freshness, semantic coverage
unmeasured, refresh incomplete). The suggested exponential identities do
not close the mixed-current problem. The applicable inputs are the actual
first-band source lower bound and the newly checked square-band sign.
Their product, with the actual prime-update weight, predicts negative
mixed density of magnitude at least c*P^(3-4*epsilon)/log(P)^3 throughout
`4/(7*P^2)<t<=2/(3*P^2)`. Integrating this slab predicts negative mass
at least c'*P^(1-4*epsilon)/log(P)^3 per prime. The scratch
`/tmp/pm_prime_mixed_work.lean` contains the direct density proof, not yet
checked. Complete current compensation cannot discard this negative part.

All three sign-module axiom audits passed with standard three axioms only.
Certificate: `../../../3-formalized/pm-prime-square-source-sign.md`.

The mixed-density and per-threshold negative-part integral drafts elaborate
apart from one scalar reassociation in the core normalization; an explicit
negation identity replaces that arithmetic tactic. The extended scratch now
also sums over all primes P<p<=2P at horizon 8P^2. The existing actual prime
shell count then predicts

`negativeCurrent_epsilon(8P^2) >= c*(2P)^(2-4*epsilon)/log(2P)^4`.

Consequently its division by `(8P^2)^kappa` should tend to infinity for
every `0<=kappa<1-2*epsilon`, for all sufficiently small positive epsilon.
This is the negative part of the literal weighted mixed current, not a
surrogate kernel. That strengthened power obstruction is being checked.
The complete signed combination, which can cancel both large parts, is
still the target; divergence of a separated part is not RH falsification.

The complete negative-current proof reached the targeted module build in
`PMPowerDampedMobiusNegativePrimeCurrent.lean`. Its only final scratch
failure was the order of generated goals for a division comparison; using
all explicit theorem arguments resolves that elaboration issue. The proof
also exposes a stronger survivor: the divergence theorem needs only
`kappa<1-2*epsilon`, with no nonnegativity restriction on kappa. The same
positive-power comparison proves all these real exponents. Final
actual-file and axiom audits are still pending.

Search216 inspected all candidate/source statements and its proposed group
(inventory65368 complete, mixed compiler freshness, semantic coverage
unmeasured, refresh incomplete). The proposed whole-half-line prime-core
norm theorem is not a bound for the physical truncated source and cannot
be substituted for one. The exact insertion theorem and canonical aperture
successor identity are the applicable inputs for telescoping the complete
signed current. This is the next bridge needed to quantify the forced
positive compensation without discarding the newly exposed negative part.

The negative-current module passed the targeted old leaf build (only that
leaf newly built) and final actual-file Lean check with empty output.
All eleven exports are wired once and indexed. Separate axiom audit is
running. Global lint has twelve unrelated unreachable modules and no PM
failure. No global lint pass, full build or numerical experiment.

The negative part therefore cannot be assigned an independent subpower
budget. Its positive survivor is the actual paired-source sign and the
quantified integrated negative mass, now formalized. The next conjecture
retains all updates: at each physical t>0, finite-prime core energy equals
seed energy plus the sum of the quadratic densities minus twice the signed
mixed densities. The corpus insertion law and aperture successor identity
give a dependency-closed induction proof; its draft is in
`/tmp/pm_prime_balance_work.lean` and awaits its first check.

For subsequent research, telescoping gives
`E_N = seed_N + Q_N - 2*(Mpositive_N-Mnegative_N)`.
The hard bound remains `Mpositive-Mnegative-Q/2 >= -C_epsilon`.
The newly proved large negative mass requires global compensation. A
weaker but unconditional positive survivor to attack first is forced
positive compensation at the leading negative-current scale: if the
actual log-four source envelope is integrated with the moving horizon,
its energy is negligible compared with the new negative-part lower bound.
Then the exact balance and Q>=0 force `Mpositive >= (1-o(1))*Mnegative`.
This is a paper target, not a proved RH-strength energy estimate.

All eleven negative-current axiom audits passed with the standard three
axioms only. Certificate: `../../../3-formalized/pm-negative-mixed-prime-current.md`.
The independent negative-current budget is retired with its quantified
positive survivor in `../../../5-failed/pm-separate-negative-mixed-current-budget.md`.
The exact signed pointwise telescope is now in its first Lean check.

The complete signed-energy balance now passes Lean in the scratch. The
module `PMPowerDampedMobiusPrimeEnergyBalance.lean` is wired once and in its
targeted old leaf build. It includes the exact pointwise telescope,
physical-horizon identification with the full source, finite truncated
energy, complete signed mixed current and its positive-minus-negative
reconstruction. No infinite-energy premise was used.

Search217 was partial, but all twenty available candidate/source statements
were inspected (inventory65372 complete, mixed compiler freshness, semantic
coverage unmeasured, background refresh incomplete). No proposed proof group.
The reciprocal-log dissipation and arbitrary coefficient-envelope bounds are
different objects and do not prove the actual moving-horizon estimate.
The applicable input remains the audited actual log-four source envelope.

Paper proof for the next quantitative compensation step: write
`a=1-2*epsilon>0` and use reciprocal energy density
`g(x)=norm(A_epsilon(1/x))^2/x^2`.
Beyond a fixed R>=e, the audited envelope gives
`g(x)<=C^2*x^(-2*epsilon)/log(x)^8`.
The compact head has finite energy by the newly checked truncated-source
integrability theorem. For N>=R^2, split at sqrt(N). The part from R to
sqrt(N) is at most `C^2*N^(a/2)/a`, and the remaining part is at most
`256*C^2*N^a/(a*log(N)^8)`. Hence
`E(N)*log(N)^4/N^a -> 0` for every 0<epsilon<1/2.
Combining this actual energy estimate with the negative-current lower
bound and exact signed balance would force, for every delta>0,
`Mpositive(8P^2)>=(1-delta)*Mnegative(8P^2)` eventually. This is a
leading compensation theorem, not the required bounded remainder.

### Complete signed balance audited (2026-10-04)

Targeted old leaf build, final actual-file Lean and all eight axiom audits
passed (standard three only). Wired once, indexed; twelve unrelated
unreachable modules remain in global lint, no PM failure. Certificate:
`../../../3-formalized/pm-complete-prime-energy-balance.md`.

The next scratch `/tmp/pm_energy_budget_work.lean` begins the actual
moving-horizon energy bound with exact reciprocal transport and finite
integrability. Its first check is running. The new compensation target
and dependency-closed paper split are recorded above; the bounded signed
remainder remains open.

Exact reciprocal energy transport, finite reciprocal integrability, the
actual log-eight energy-density envelope, and the needed power primitive
bound now pass Lean in `/tmp/pm_energy_budget_work.lean`. The extended
draft adds the complete split at R and sqrt(N), retaining the compact head
energy and both explicit error terms. It is undergoing its first check.
The next step is normalization and then forced positive compensation.

The complete actual energy split at R and sqrt(N) now passes Lean. The
next draft proves the normalized limit `E_N*log(N)^4/N^(1-2*epsilon)->0`
using the two positive-power/logarithm limits and the inverse log-four
limit. It is being checked in `/tmp/pm_energy_budget_work.lean`.
No canonical admission assumption is introduced; the signed remainder
needed for RH is still open.

The normalized energy-limit proof elaborated completely; its only reported
issue was a trailing ring tactic after field_simp had already closed the
last identity. That redundant tactic was removed. The scratch now adds the
first global signed-compensation theorem: eventually for small positive
epsilon, for every delta>0, `(1-delta)*Mnegative(8P^2)<=Mpositive(8P^2)`
eventually in P. It uses the exact common horizon, the newly established
energy limit and the actual negative-part lower bound. The proof makes no
claim that the remaining difference is bounded.

### Leading compensation scratch passed (2026-10-04)

The normalized energy limit and complete leading positive-compensation
statement both pass the scratch Lean check with empty output. The failed
elaboration was traced to applying the field-only const-multiple limit
lemma to natural cutoffs. Explicitly typing the square map and using the
Archimedean version fixes the issue at default resource limits. The scalar
scale comparison is isolated from the filter argument.

Promoted to `PMPowerDampedMobiusPrimeCompensation.lean`, wired once; targeted
old leaf build and final actual-file/axiom audits remain pending. The hard
bounded signed remainder remains open. This closes a global compensation
survivor, not the small-damping admission problem.

Search218 and219 each completed without a partial flag, inventory65383
complete, mixed compiler freshness, semantic coverage unmeasured and
background refresh incomplete. All20 candidate and20 source statements
and proposed groups were inspected. Unrelated generic energy derivatives
in218 do not apply;219 returns the actual centered logarithmic recursion,
whose full dilation-minus-forcing covariance remains unbounded by any
proved estimate. The suggested prime log-tail bound does not pay that
quadratic covariance. Next research keeps the actual source-change and
forcing terms, rather than inferring a bound from separated current signs.

### Leading complete-current compensation closed (2026-10-04)

`PMPowerDampedMobiusPrimeCompensation.lean` proves actual normalized energy
negligibility and one-sided leading positive compensation. Both exports
pass the targeted old leaf build (26s), final actual-file Lean with empty
output and separate axiom audit with the standard three axioms only.
Wired once; global lint twelve unrelated unreachable modules, no PM failure.
Certificate: `../../../3-formalized/pm-leading-prime-compensation.md`.

This advances the forced global cancellation law but does not improve the
positive-power residual to the RH-strength bound. Continue on the actual
joint logarithmic dilation/forcing covariance or the equivalent complete
prime-current remainder. Do not repeat the finished audits.
