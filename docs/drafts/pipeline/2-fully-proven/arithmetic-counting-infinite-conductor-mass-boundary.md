# Infinite prime counts have zero or unit conductor mass

- **ID:** ACP-INFINITE-CONDUCTOR-MASS-BOUNDARY
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; immediate formalization)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Lean target:** InfinitePrimeCountsHaveAZeroOrUnitConductorMass.lean
- **Input:** ../3-formalized/arithmetic-counting-all-prime-pattern-harmonic-density.md

## Objects and exact statements

For an arbitrary prime pattern P with harmonic Euler density c, define

b_P(m)=sum_(d|m)mu(m/d)omega_P(d),
w_P(m)=b_P(m)^2/phi(m),
a_P(m)=c b_P(m)/sqrt(phi(m)).

All sums below run over natural numbers. The zero conductor contributes
zero, so these equal the corresponding positive-conductor sums. The six
exact endpoints are:

1. b_P(m) equals its finite-prime cutoff transform whenever Q>=m.
2. a_P(m)^2=c^2 w_P(m), including the zero conductor.
3. w_P is summable if and only if c>0.
4. The total squared coefficient mass is one if c>0 and zero if c=0.
5. The literal mixed harmonic Ramanujan count has the exact divisor formula
   given below.
6. Its normalized harmonic mean is c b_P(m), for every conductor m.

No infinite-series convergence or harmonic mean is assumed. The product
regimes are separated internally, and the final statements cover every P.

## Exact finite-cutoff compatibility and monotonicity

Every divisor d of m is at most m. If Q>=m, the full prime sign and its
finite cutoff agree on every such divisor. Substitution in the literal
Mobius divisor sum gives b_P(m)=b_(F_Q)(m), hence equality of the squared
weights at that conductor.

For arbitrary Q,m, choose R=max(Q,m). The proved finite-prime weight
monotonicity gives

w_(F_Q)(m)<=w_(F_R)(m)=w_P(m).

All these weights are nonnegative. Every finite-prime cutoff has exact
total unnormalized mass c_Q^(-2).

## Positive-density total mass

Suppose c>0. A packet of conductors m<N fits inside prime cutoff N, so

sum_(m<N)w_P(m)=sum_(m<N)w_(F_N)(m)<=c_N^(-2)<=c^(-2).

The nonnegative bounded-partial-sum criterion therefore proves summability
of w_P, with total at most c^(-2). Conversely, pointwise domination of each
finite-prime weight gives

sum_m w_P(m)>=sum_m w_(F_Q)(m)=c_Q^(-2)

for every Q. Since c_Q->c>0, the total is at least c^(-2). Thus the exact
unnormalized total is c^(-2). Multiplication by c^2 and the coefficient
square identity yield total normalized mass one.

## Sharp summability boundary and zero normalized mass

If w_P were summable with finite total W while c=0, finite-prime domination
would give 1<=W c_Q^2 for every Q. Taking Q to infinity would give 1<=0.
Thus summability forces c>0; the preceding argument proves the converse.

At c=0 every normalized coefficient a_P(m) equals zero directly, so its
squared series has sum zero. This step does not multiply a divergent
unnormalized sum by zero. It proves the normalized series term by term.
Consequently the unconditional normalized mass is exactly
if c=0 then 0 else 1.

## Actual harmonic Ramanujan coefficients

Let R_m(n) be the existing real Ramanujan lag coefficient and put
T_P(m,N)=sum_(n<=N)omega_P(n)R_m(n)/n. Expand the exact divisor incidence
formula for R_m, interchange the finite sums, and apply multiplicativity
on the multiples of each divisor d. This gives

T_P(m,N)=sum_(d|m)mu(m/d)omega_P(d)S_P(floor(N/d)).

For fixed d>0, the signed harmonic shell is bounded by 1+log d. Therefore

|S_P(N)-S_P(floor(N/d))|/H_N <= (1+log d)/H_N ->0.

The already proved mean S_P(N)/H_N->c then yields
S_P(floor(N/d))/H_N->c. Pass the limit through the finite divisor sum to
obtain T_P(m,N)/H_N->c b_P(m). Division by sqrt(phi(m)) identifies exactly
the normalized coefficients a_P(m) above. The zero conductor is empty and
contributes zero throughout.

## Scope, positive content and novelty audit

The result identifies a sharp arithmetic completeness boundary: positive
Euler density retains unit mass in fixed harmonic Ramanujan conductors;
zero density annihilates all fixed coefficients, while the unnormalized
weight series diverges. The exact mixed count certifies that these are
actual harmonic coefficients, not a formal probability normalization.

The exact harmonic cutoff boundary is formalized separately in
../3-formalized/arithmetic-counting-prime-pattern-cutoff-boundary.md. It has the same
positive-density threshold, but is not an input to this proof. Actual
prime-matrix eigenline coordinates, omitted eigenline mass and optimal-gap
transfer remain separate obligations. No complete Weil positivity or
zero-gap converse follows merely from these means.

Corpus searches identified the finite-prime unit-mass and coordinate
results, finite weight monotonicity and the bounded nonnegative-series
criterion. Their statements were read before reuse. The new contribution
is the all-pattern arithmetic mass dichotomy and exact harmonic coefficient
bridge; no literature-wide priority claim is made.

## Formalization

The immediate full six-endpoint draft is
/tmp/acp-infinite-conductor-mass-check.lean. It imports the formalized
all-pattern mean leaf and ConductorMassBoundsGapLossAndProbePrecision,
whose existing finite-weight total is reused. The latter's first olean is
required by this actual draft and has not yet been built. Existing oleans
are preserved; no numerical experiment or extra analytic premise is used.

- [x] Complete paper proof, including zero-product divergence and normalization.
- [x] Immediate full Lean draft with the same six endpoints.
- [ ] Scratch and transitive axiom audit.
- [ ] Canonical source check, umbrella and durable evidence.
