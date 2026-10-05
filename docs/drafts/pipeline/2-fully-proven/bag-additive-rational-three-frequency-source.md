# BAG additive rational three-frequency source

- ID: C28.56ag.1.
- Route: BAG complete signed physical cubic.
- Paper status: dependency-closed proof below; all five Lean leaves and all41
  declaration axiom audits passed. See the corresponding 3-formalized card.
- Active parent: ../1-in-progress/bag-three-frequency-ramanujan-source.md.
- Scope: additive rational atoms of the actual divisor source. This is not
  yet the multiplicative six-zeta finite-height transfer or a cubic estimate.

## Exact statement

For a finite set P of naturals, discard nonprimes and let Q be the product of
its remaining primes. On the circle define the literal finite signed atoms

    nu_(e,P) = sum_(d|Q) mu(d) d^(-e)/d * sum_(a mod d) delta_(a/d),
    kappa_(e,P) = (nu_(e,P)-nu_(0,P))/e.

For every complex Schwartz function Phi on R^3, set

    F_Phi(x) = sum_(n in Z^3) Phi(n) exp(2 pi i n.x).

This series is absolutely convergent at every x. The complete finite tensor
kappa_(e,P)^tensor3 acting on F_Phi converges jointly as P tends through all
finite sets and e tends to zero from above to

    sum_(n in Z^3) Phi(n) Lambda(|n1|) Lambda(|n2|) Lambda(|n3|).

All three Fourier coordinates and every finite rational atom are retained.
There is no c=a*b restriction, symmetry assumption, absolute summability
assumption on the all-prime atom weights, or relation between P and e. Phi
is fixed. Its samples are the Fourier coefficients of F_Phi; do not confuse
F_Phi with an unperiodized Schwartz function on the real line.

## Proof

1. Finite torsion orthogonality gives the n-th Fourier multiplier
   sum_(d|Q,d||n|) mu(d)d^(-e) = D_e(gcd(Q,|n|)). The prime product identity
   in PMPowerDampedMobiusDivisorHaar makes this exactly
   product_(p in P, p prime, p|n) (1-exp(-e log p)). At n=0 all retained
   primes act, since gcd(Q,0)=Q. No zero mode is replaced by D_e(0).
2. Subtract the multiplier at e=0 at this same P and divide by e. For n>0
   an empty incidence set gives zero. Otherwise the product is bounded by
   any one factor; 0<=1-exp(-e log p)<=min(1,e log p) and p<=n give a
   compensated coefficient between zero and log n. Once P contains 2,3,
   the coefficient at n=0 is between zero and e log2 log3.
3. At n!=0 the incidence set eventually equals the full set of prime
   factors of |n|. The corpus Wold normal-cone derivative at zero is exactly
   Lambda(|n|). The zero-frequency bound gives limit zero. These are joint
   product-filter limits: there is no cutoff/damping coupling premise.
4. For e<=1 and P containing 2,3, each coefficient is at most 6(1+|n|).
   The product is at most 6^3 times T(n), where
   T(x)=(1+|x1|)(1+|x2|)(1+|x3|). Since T(x)<= (1+norm x)^3, the Schwartz
   seminorm family through order (9,0) gives

       |Phi(x)| T(x) <= 2^9 S_9(Phi) / T(x)^2.

   The right side is summable on Z^3 by the product of three shifted square
   p-series. This proves summability, rather than assuming it.
5. The finite atom action can be exchanged with the Fourier series: there
   are finitely many atoms and the phase has norm one. Torsion orthogonality
   identifies its coefficient with the product from step3. The summable
   envelope in step4 and dominated convergence prove the asserted joint
   limit of the full, unrestricted triple.
6. On any finite integer band 1<n<=M, P=range(M+1) contains all prime
   factors of n and the zero-damping divisor coefficient is zero. Thus the
   compensated coefficient is exactly D_e(n)/e throughout the whole band.

## Novelty and limits

Existing Wold normal-cone results supply the one-coordinate derivative.
Existing Ramanujan expansions supply the actual divisor product and grouped
positive-damping series. The new assertion is the jointly compensated finite
rational atom tensor and its full fixed-Schwartz tested limit, including the
zero coordinate and proved interchange. It does not estimate growing tests.

The six-zeta corpus uses positive-rational multiplicative dilation modes.
Connecting its c=a*b resonance to the finite-height additive action still
requires the full physical Poisson/stationary-phase bridge. The proposed
finite p^2-torsion squarefree filter remains a separate, unproved extension
needed for a smooth prime-only physical test. The complete signed cubic,
growing moments, moving cofactors, common-height self-return and RH are open.

Subsequent continuation01a6 formalized the prime-only extension in C28.56ag.2;
see `bag-prime-only-rational-three-frequency-source.md`. The physical
growing-test and signed cancellation obligations remain.
