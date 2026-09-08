# CCM-FU: literal fixed-core prime correlation

- **Stage:** 1-in-progress; signed reserve control. The exact source correlation and its complete coefficient series are [formalised](../3-formalized/ccm-fu-fixed-core-prime-correlation.md).
- **Parent:** [fixed-core coefficient and reserve](ccm-fu-fixed-core-energy-limit.md).
- **Goal:** Signed reserve supply and renewal through changing cores, exhaustive selection, uniform signed Abel bound, RH.

## Closed source reduction

For p prime outside P, the complete source avoiding P+p now satisfies

`Q_P(M)-Q_(P+p)(M)=2*sqrt(p)*sum_r r*I_P(M,r)*I_P(M,p*r)`.

The finite source has 1<=r<=M, r squarefree, primeFactors(r) disjoint P+p.
Both signed head factors are literal clipped samples. This is the actual
paired source, not a positivity assumption. The exact fibre merger and
product interpolation identify it directly in Lean.

On quotient n=M/r, the second head quotient is floor(n/p). If a_n,b_n are
the already defined physical head slope and intercept, the normalized
release summand is twice the square-root polynomial

`a_n*a_(n/p)+(sqrt(p)*a_n*b_(n/p)+b_n*a_(n/p))*sqrt(r/M)`

`+sqrt(p)*b_n*b_(n/p)*(r/M)`.

The proved source density and moments therefore give its explicit signed
block limit. The proved absolute quotient-tail estimate, obtained from the actual
fibre amplitude bound and at most floor(M/T) source integers, joins all
blocks into an absolutely convergent signed correlation series. Its sum
is exactly kappa_P-kappa_(P+p), with finite-prefix error at most
2*C_P²/T for C_P=(3/5)*2^(card(P)-1), using natural truncated subtraction.
No additional continuous integral representation is needed for this identity.

## Closed proof chain

1. Reindex the exact prime-merger cross sum by the product of its remaining
   prime label; omitted inactive terms vanish and the terminal sample is zero.
2. On each quotient cell use the two exact affine head formulas. The nested
   quotient identity M/(p*r)=(M/r)/p retains every clipping endpoint.
3. Expand the product; apply the established count, square-root and linear
   moments at endpoints 1/n and 1/(n+1), with density rho_(P+p).
4. Bound the entire signed remainder absolutely and pass to the infinite
   block series. Its equality to kappa_P-kappa_(P+p) identifies the actual
   reserve coefficient.

## Remaining arithmetic obligation

Prove a sign and size law supplying renewable reserve through changing cores.
The exact coefficient and its error bound are established; source sign is
not a consequence of absolute summability or of the fixed-core energy limit. No experiment is planned for these
algebraic and weighted-limit steps, and no numerical input enters Lean.

A [uniformly positive signed source moment](../3-formalized/ccm-fu-fixed-core-signed-head-moment.md)
is now proved for every finite core. Its continuous head agrees with every
literal clipped rational sample, and its inverse-cube integral is
J_empty*product_(p in P)(1-p^(-3/2)), with a positive lower bound independent
of P. This does not determine the signed cross correlation.

The next source target is the weighted dilation average described in the
[signed-head moment card](ccm-fu-fixed-core-signed-head-moment.md).
The existing leading-mean theorem proves
only H_P(M)/sqrt(M)->0 for nonempty P. It does not prove a constant limit
for H_P or the sign needed in its distant-prime correlation. The corpus's
`SquareRootSummatoryMellin` and literal `log(n)-tau(n)+2gamma` source give
an analytic starting point; a Mellin continuation or residue calculation
alone must not be mistaken for a proved pointwise remainder estimate.
