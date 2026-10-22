# CCM-FU: literal fixed-core prime correlation

- **Stage:** 1-in-progress; signed reserve control. The exact source correlation and its complete coefficient series are [formalised](../../../3-formalized/ccm-fu-fixed-core-prime-correlation.md).
- **Parent:** [fixed-core coefficient and reserve](../../ccm-fu-fixed-core-energy-limit.md).
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

A [uniformly positive signed source moment](../../../3-formalized/ccm-fu-fixed-core-signed-head-moment.md)
is now proved for every finite core. Its continuous head agrees with every
literal clipped rational sample, and its inverse-cube integral is
J_empty*product_(p in P)(1-p^(-3/2)), with a positive lower bound independent
of P. This does not determine the signed cross correlation.

The [physical signed dilation mean](../../../3-formalized/ccm-fu-fixed-core-physical-dilation-mean.md)
has an exact fixed-core residue limit, and its [strict eventual orientation](../../../3-formalized/ccm-fu-divisor-source-residue-sign.md)
is proved: positive for odd card(P), negative for even card(P).
Both the full Mellin pairing and B(-1/2)>1/(272*pi)>0 are formalized.
The [discrete-to-physical theorem](../../../3-formalized/ccm-fu-discrete-physical-prime-release.md)
proves the exact identity

`kappa_P-kappa_(P+p)=2*rho_(P+p)*p^(-3/2)*W_P(p)`.

The discrete block series and the physical average have independent
definitions. Their proved equality transfers the strict parity sign to
the actual coefficient: sufficiently distant unprocessed primes lower
kappa for odd-sized cores and raise it for even-sized cores. Quantitative
control through complete changing-core exhaustion remains open.

The [changing-core pair theorem](../../../3-formalized/ccm-fu-changing-core-pair-reserves.md)
now retains the exact ratio profile with a remainder uniform in the
inserted prime and every next dilation. Comparable large prime pairs
consume order 1/p, exceeding the first prime's possible p^(-3/2) credit.
For every even nonempty core, a separated ratio window instead supplies
arbitrarily large pairs with a positive net reserve of order 1/p and
preserves even cardinality. Both comparisons transfer to actual energies
at all sufficiently large cutoffs for each selected pair. Inclusion of
every prime, intermediate-step payment and uniform cutoff thresholds
remain unproved.

## Closed integral bridge

On u in [n,n+1], the literal continuous head is identified with
a_n*sqrt(u)+b_n, using the already defined block slope and intercept.
The second head G_P(u/p) has the corresponding coefficients at floor(n/p).
This extends the exact rational-sample affine identity to the whole closed
interval; inactive head blocks remain zero.

For the existing correlation primitive Phi_n, direct differentiation then gives

`d/du [-Phi_n(1/u)] = 2*sqrt(p)*G_P(u)*G_P(u/p)/u^3`.

Thus its endpoint difference is precisely the integral over that unit
block. The current correlation mass is rho_(P+p) times this difference.
Absolute integrability follows from the proved real-ray square-root bound,
so summing all unit blocks identifies the already proved complete mass
series with the full integral. Finally substitute u=p*x; the second head
vanishes for x<=1, and the factor becomes p^(-3/2). This yields the
displayed discrete-to-physical identity with every scale factor retained.

The real-interval head formula, block derivative, countable integral
partition and final change of variables are all proved in Lean. The
remaining source problem is uniform reserve propagation while P and the
cutoff change; the coefficient sign by itself is not an every-cutoff
energy inequality.
