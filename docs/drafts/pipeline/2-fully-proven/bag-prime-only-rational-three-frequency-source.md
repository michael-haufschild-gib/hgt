# BAG prime-only rational three-frequency source

- ID: C28.56ag.2, continuation01a6.
- Route: BAG complete signed physical cubic.
- Paper status: dependency-closed proof below; all three production leaf and
  all34 new/exposed declaration axiom audits passed. See the 3-formalized card.
- Parent: ../1-in-progress/bag-three-frequency-ramanujan-source.md.

## Statement

Let Q(P) be the product of the primes in a finite set P. Retain the complete
compensated divisor-torsion source kappa_(e,P) from ag.1. Define the finite
signed rational square-divisor source

    sigma_P = sum_(d|Q(P)) mu(d)/d^2 * sum_(a mod d^2) delta_(a/d^2),
    rho_(e,P) = kappa_(e,P) * sigma_P.

Convolution retains every pair of atoms, adding nodes and multiplying
weights. For every fixed complex Schwartz Phi on R^3, the full tensor
rho_(e,P)^tensor3 acting on the periodic Fourier test

    F_Phi(x) = sum_(n in Z^3) Phi(n) exp(2 pi i n.x)

converges jointly as P ranges through all finite sets and e->0+ to

    sum_(n in Z^3) Phi(n) L(|n1|) L(|n2|) L(|n3|),
    L(m) = log(m) if m is prime, and zero otherwise.

There is no relation between the cutoffs, no discarded rational atom or
Fourier coordinate, and no analytic/RH assumption. The squarefree mask is
in the source; the original smooth profile and its Fourier test are unchanged.

## Proof

1. Torsion orthogonality gives sigma_P's multiplier
   A_P(n)=sum_(d|Q(P),d^2||n|) mu(d). Put g=gcd(Q(P)^2,|n|), which is
   nonzero even at n=0. The summation set equals the square divisors of g:
   d^2|g iff d|Q(P) and d^2||n|. The corpus identity
   HTGeometry.sum_moebius_sq_dvd gives A_P(n)=mu(g)^2. Thus A_P is exactly
   the squarefree indicator of g and belongs to {0,1}.
2. Once P contains 2 and all prime factors of |n|, g is squarefree iff
   |n| is squarefree. Indeed a prime square dividing |n| then divides g;
   conversely g divides |n|. At n=0 the retained prime 2 makes 4|g, so
   both indicators are zero. This proves eventual exactness for every n.
3. The phase of the sum of two rational nodes is the product of their
   phases. Finite sum distributivity gives rho's multiplier exactly as
   A_P(n) times the compensated ag.1 multiplier. Its joint limit is
   1_(Squarefree |n|)*Lambda(|n|), exactly L(|n|) by the corpus theorem
   vaughanSquarefreePart_vonMangoldt. Every proper prime power is removed.
4. Since 0<=A_P<=1, the product of the three projected multipliers is
   nonnegative and bounded by the old product. Hence the already proved
   summable envelope 6^3*|Phi(n)|*product_j(1+|nj|) applies unchanged.
   Dominated convergence gives the unrestricted three-coordinate limit.
5. Each finite atom/Fourier interchange is justified by the existing
   absolute convergence of F_Phi at every point. Three copies of the
   exact one-coordinate atom identity give the full tensor identity,
   then step4 gives the literal finite atom action's joint limit.
6. On 1<n<=M, P=range(M+1) covers every prime factor. The multiplier is
   exactly 1_(Squarefree n)*D_e(n)/e on the entire finite physical band.
   This is not already a prime indicator at positive e: squarefree
   composites remain until the critical limit.

## Novelty and frontier

The Möbius square-divisor identity and squarefree Mangoldt identity were
already in the corpus. The new result is their literal finite rational
convolution with the compensated source and its full joint tensor limit.
No arithmetic mask is placed in a smooth physical profile. No unproved
absolute convergence of the all-prime signed atomic weights is used.

This closes prime-only fixed-test source/interchange. It does not estimate
the growing physical test, justify replacing a finite-height neighborhood
by its exact resonance, or prove o(N/log(N)^2) for the signed cubic.
Growing moments, moving cofactors, common-height self-return and RH remain
open. The new source is additive; the six-zeta trace remains a separate
multiplicative representation requiring physical transfer.
