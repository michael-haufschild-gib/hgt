# The horizon finite part on several prime valuation classes

- **ID:** finite-prime-horizon-finite-part
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** RAPT open topic 6; review-2710 B3.28; AIT transverse towers
- **Count:** contribution 1 of the connect-dots-250 task; supporting lemmas count together

## Statement

Let Q be a finite set of primes, P_Q their product, and

`delta_Q=product_(p in Q)(1-1/p)`,
`gamma_Q=gamma+sum_(p in Q) log(p)/(p-1)`.

A supported order d divides a power of P_Q and is positive. Put
`w_d(n)=1_(d divides n, gcd(n/d,P_Q)=1)/sqrt(n)`,
`w_d^A(n)=1_(n<=A) w_d(n)`,
`H_Q(A)=sum_(1<=n<=A, gcd(n,P_Q)=1)1/n`,
`H_d(A)=H_Q(floor(A/d))/d`, and `delta_d=delta_Q/d`.
Write B_N for the actual Weil prime-kernel bilinear form, and
`||x||_N^2=sum_(1<=n<=N)x(n)^2`.

Choose any finite family of distinct supported orders d_i. Its actual class
polar coordinates and tensor counterterm are

`ell_i,N(x)=sum_(1<=n<=N)x(n)w_(d_i)(n)`,
`C_N(x)=sum_i ell_i,N(x)^2/delta_(d_i)`.

For any finite generator set, a class label a(r), arbitrary real c_r, and
independent cutoffs M_r<=N, set `x=sum_r c_r w_(d_(a(r)))^(M_r)`. Define

`K_Q(d,e,A,B)=P(d,e)/sqrt(d*e) * H_Q(min(floor(A/d),floor(B/e)))`.

**Uniform finite part.** For every eta>0 there is C>=0, depending only on Q
and eta, such that every such family and profile satisfies

`|B_N(x,x)-C_N(x)+2 gamma_Q ||x||_N^2`
` -sum_(r,s)c_r c_s K_Q(d_(a(r)),d_(a(s)),M_r,M_s)|`
` <= (eta harmonicSum(N)+C)(sum_r |c_r|)^2`.

The constant is independent of the raw class orders, cutoffs, and number of
generators. For a fixed finite class family there is also K>=0 such that

`|B_N(x,x)-C_N(x)|<=K(harmonicSum(N)+1)(sum_r |c_r|)^2`.

**Normalized common-horizon limit.** For fixed real b_i and
`x_b=sum_i b_i w_(d_i)/sqrt(delta_(d_i))`,

`(B_M(x_b,x_b)-C_M(x_b))/log(M)`
` -> -2 gamma_Q sum_i b_i^2 +sum_(i,j)b_i b_j P(d_i,d_j)`.

The last kernel is the exact sum of AIT's local tower kernels over Q. Euler's
constant occurs once in the shared gamma_Q, rather than once per tower.

**Covariance and survival.** If t is Q-supported and `(T_t x)(tn)=x(n)`, with
zero values away from multiples of t, the counterterm for classes td_i at
horizon tM equals C_M(x). The same is true of B-C. Moreover,
`C_M(x)=0` iff every selected class charge is zero. Once M>=d_i for all i,
the map taking x to its finite vector of class charges is surjective.

## Dependency-closed paper proof

### 1. Supported/unit factorization

A supported integer is coprime to every Q-unit. Consequently `d*k=e*l`, with
d,e supported and k,l units, forces d=e and k=l. A nonzero von Mangoldt
quotient is a prime power. If its prime belongs to Q, only the supported
factor changes; otherwise only the unit factor changes. Hecke invariance of
the prime kernel therefore gives the exact splitting

`P(d*k,e*l)=1_(d=e) P(k,l)+1_(k=l) P(d,e)`.

Reindexing by n=d*k gives the displayed H_d, disjoint class supports, and
the rectangular class identities

`B_N(w_d^A,w_d^B)=B_Q(floor(A/d),floor(B/d))/d`,
`B_N(w_d^A,w_e^B)=K_Q(d,e,A,B)` for d!=e,
`sum_(n<=N)w_d^A(n)w_e^B(n)=1_(d=e)H_d(min(A,B))`,
`ell_d,N(w_e^B)=1_(d=e)H_d(B)`.

Here B_Q is the unit Gram. These are identities for the actual arithmetic
kernel and polar functionals, with no matrix approximation assumed.

### 2. The two sieve constants

Deleting a prime p not in Q gives

`H_(Q+p)(N)=H_Q(N)-H_Q(floor(N/p))/p`.

The harmonic limit at Q empty is Euler's constant. Induction, using
`log(floor(N/p))-log(N)->-log(p)`, proves

`H_Q(N)-delta_Q log(N)->delta_Q gamma_Q`.

For `A_Q(N)=sum_(n<=N, unit) Lambda(n)/n`, a nonzero Mangoldt term is a
power of exactly one prime. Deleting p removes precisely its geometric tail,
whose limit is `log(p)/(p-1)`. The existing unconditional Mertens limit
`A_empty(N)-log(N)->-gamma` therefore gives

`A_Q(N)-log(N)->-gamma_Q`.

These inputs are proved corpus results and finite deletion identities, not
additional analytic hypotheses.

### 3. Uniform quotient boundary

If f tends to zero, choose Y with `|f(y)|<=eta` for y>=Y and a global bound K.
For any S contained in `[1,A]` and A<=B, split the sum at `floor(B/k)>=Y`.
That part costs at most `eta sum_(k in S)1/k`. On the other part,
`B<Y*k`, hence `1/k<=Y/B`; since `#S<=B`, its cost is at most K*Y. Thus

`|sum_(k in S)f(floor(B/k))/k|<=eta sum_(k in S)1/k+K*Y`.

The zero horizon is empty. No property of the subset beyond its horizon is used.

### 4. The rectangular unit finite part

For A<=B, split each row into upward and downward divisibility. The downward
divisors of a unit remain units, and `sum_(d|k)Lambda(d)=log(k)`. Thus

`B_Q(A,B)=sum_(k<=A, unit)[A_Q(floor(B/k))+log(k)]/k`.

Put `e(y)=A_Q(y)-log(y)+gamma_Q` and
`h(y)=H_Q(y)/delta_Q-log(y)-gamma_Q`; both tend to zero. For positive k<=B,
the existing logarithmic floor bound gives

`0<=r(B,k)=log(B)-log(floor(B/k))-log(k)<=1/floor(B/k)`.

Since `B<=2*k*floor(B/k)`, its total weighted sum over units k<=A is at most
2. The exact row identity now becomes

`B_Q(A,B)-H_Q(A)H_Q(B)/delta_Q+2 gamma_Q H_Q(A)`
` =sum_(k<=A, unit)e(floor(B/k))/k`
`  -sum_(k<=A, unit)r(B,k)/k-H_Q(A)h(B)`.

Apply the quotient-boundary estimate with eta/2 to e. Above a fixed threshold
for B, the last term costs at most `(eta/2)H_Q(A)`. Below it, boundedness of h
and harmonic monotonicity give a fixed constant. The empty horizon is
immediate; symmetry handles B<A. This proves the uniform unit estimate.
Dividing by d gives the diagonal class estimate with the same nonnegative
constant, since d>=1 and H_d(A)<=harmonicSum(A).

### 5. Signed assembly

Expand B by bilinearity and C using the exact class polar coordinates from
step 1. Its entries are the same-class products `H_d(A)H_d(B)/delta_d`.
The ordinary squared norm expands with entries `1_(d=e)H_d(min(A,B))`.
All cross-class remainders vanish exactly. Each diagonal remainder is bounded
by `eta harmonicSum(N)+C`. The triangle inequality for the double sum gives
the displayed bound times `(sum |c_r|)^2`, preserving every coefficient sign.
For fixed classes, the finitely many values `|P(d,e)|/sqrt(d*e)` are bounded;
all unit harmonic factors and ordinary class masses are bounded by
harmonicSum(N). This gives the leading tensor-law corollary.

### 6. The common-horizon limit

One may also obtain this endpoint without the rectangular Mertens argument.
Let `L_Q(N)=sum_(n<=N, unit)log(n)/n`. The divisor identity gives the exact
diagonal Gram `2 L_Q(floor(M/d))/d`. Its deletion recursion is

`L_(Q+p)(N)=L_Q(N)-(L_Q(floor(N/p))+log(p)H_Q(floor(N/p)))/p`.

At Q empty, `L_empty(N)-log(N)^2/2` converges: the successive error is
bounded by `(log(n)+1)/n^2`, a summable sequence. The recursion and the
harmonic limit imply `(2 L_Q(N)-delta_Q log(N)^2)/log(N)->0`.
Indeed, for `r=log(floor(N/p))-log(N)+log(p)->0`, the only quadratic
cross term is `log(p)^2-2log(N)r-r^2`, which vanishes after division by log(N).

The harmonic limit gives
`H_d(M)=delta_d(log(M)-log(d)+gamma_Q)+o(1)`.
Subtracting `H_d(M)^2/delta_d` from the exact diagonal Gram and dividing by
log(M) gives `-2 gamma_Q delta_d`. The exact mixed Gram divided by log(M)
tends to `delta_Q P(d,e)/sqrt(d*e)`. Density normalization and finite
bilinearity give the stated signed limit. AIT's transverse-tower identity
identifies its last kernel with the sum over primes in Q.

### 7. Covariance, survival, and independent charges

Reindexing multiples of t gives
`ell_(td),tM(T_t x)=ell_d,M(x)/sqrt(t)` and `delta_(td)=delta_d/t`.
These factors cancel exactly in C. The original prime form is Hecke invariant,
so B-C is invariant as well. Positive densities make C a sum of nonnegative
squares, yielding the survival equivalence. If M>=d, the term n=d gives
H_d(M)>0. Disjointness then realizes arbitrary charges u_i by
`x=sum_i u_i w_(d_i)/H_(d_i)(M)`, proving independence.

## Novelty and scope

Corpus searches for several-prime horizon counterterms, finite-sieve Euler
finite parts, and independent cutoffs found the one-prime tensor, covariance,
and finite-part modules. RAPT topic 6 explicitly asks for their several-prime
extension. AIT already supplies the transverse tower structure. The new result
identifies the actual horizon counterterm, shared finite part, covariance,
and signed profile law for every finite prime set. Supporting deletion,
factorization, and boundary lemmas are not separate contributions.

The normalized common-horizon limit fixes a finite class family. The uniform
step estimate uses raw class coordinates; it does not give uniform errors
after normalization by densities tending to zero. Neither an all-primes
Weil sign theorem nor a zero-location theorem is asserted.

## Lean realization and audit

All endpoints are in `GaloisForLFunctions.RenormalizedArithmeticPotentialTheory`.

| Exact endpoint | Source module |
|---|---|
| `exists_sieveStepProfile_finitePart_bound` | `TheFiniteSieveCountertermIsPolarOnStepProfiles` |
| `exists_sieveStepProfile_tensor_bound` | `TheFiniteSieveCountertermIsPolarOnStepProfiles` |
| `tendsto_sieveProfile_finitePart` | `TheFiniteSieveHasTheTowerFinitePart` |
| `tendsto_sieveProfile_sum_towers` | `TheFiniteSieveHasTheTowerFinitePart` |
| `sieveTensorCounterterm_heckeShift` | `TheFiniteSieveCountertermIsHeckeCovariant` |
| `sieveFinitePart_heckeShift` | `TheFiniteSieveCountertermIsHeckeCovariant` |
| `sieveTensorCounterterm_eq_zero_iff` | `TheFiniteSieveCountertermIsHeckeCovariant` |
| `sieveClassPolar_surjective` | `TheFiniteSieveCountertermIsHeckeCovariant` |

Supporting modules: `TheFiniteSieveHasOneEulerConstant`,
`ThePrimeKernelSplitsOverAFiniteSieve`, `TheSieveClassesHaveExactPrimeGrams`,
`TheSievedLogarithmHasTheSameQuadraticDivergence`,
`TheFiniteSieveHasTheMertensConstant`, `TheFiniteSieveUnitGramHasTwoHorizons`,
`TheSieveClassesHaveExactTruncatedGrams`, and HTGeometry's
`LogHarmonicFinitePart` and `HarmonicBoundaryLayer`.

All twelve source modules passed Lean. Dependency oleans were generated only
where another new module imports them. The two final leaves passed direct
repository-source checks with `lake --old env lean`; no leaf olean or umbrella
build was needed. Both leaves are imported by the RAPT umbrella, and both
general analytic helpers by HTGeometry.

The eight endpoints above passed a transitive `#print axioms` audit, each with
exactly `propext`, `Classical.choice`, and `Quot.sound`. Audit output is retained
in `logs/finite-prime-horizon-finite-part-axioms-2026-10-28.log`. A source audit
found no forbidden proof shortcuts or raised elaboration limits. The analytic
limits used by the endpoints are proved, not supplied as assumptions.

Fresh corpus searches and source inspection confirm that the one-prime tensor,
covariance, Euler finite part, and AIT transverse tower decomposition are the
baseline. Their finite-prime horizon synthesis, including arbitrary signed step
profiles and the shared Euler term, closes RAPT topic 6 in the stated finite scope.

- [x] 0 → 1: explicit frontier question and corpus novelty search.
- [x] 1 → 2: dependency-closed paper proof of the precise endpoints above.
- [x] 2 → 3: complete Lean verification and final audits.
