# BAG uniform original finite Euler–zeta comparison

01at. Dependency-closed symbolic paper proof; exact Lean theorem audited.
This controls moving frequencies, a necessary ingredient for actual mixed
Mellin transfer. No source-integral cancellation is asserted yet.

Fix A>=0. Put L=logN, Q_N(a,t)=product_(p<=N)(1-p^(-1-a/L-it)),
s_N(t)=1+1/L+it. For all sufficiently large N, simultaneously for every
real |a|<=A and every real t,

  exp(-C_A) <= |Q_N(a,t)|*|zeta(s_N(t))| <= exp(C_A).

All products retain the ORIGINAL cutoff. Choose N>=3 and A/(2L)<=1/8.
Write q_p=p^(-1-a/L-it), q_p^0=p^(-1-it),
S_N(t)=sum_(p<=N)cos(t logp)/p. The corpus radialNome estimates give
|q_p|<=3/4 and |q_p|^2<=p^(-3/2), independently of t. Hence each factor
is nonzero and the complex logarithm remainder satisfies

  |log|1-q_p|+Re(q_p)| <= 2*p^(-3/2).

This is the real part of the existing Taylor remainder on the unit disc;
no logarithm of a complex product is taken. Add the REAL logarithms of
its nonzero factor norms to obtain

  |log|Q_N(a,t)|+sum Re(q_p)| <= 2*B,
  B=sum_(n>=0)n^(-3/2)<infinity.

For x=-a*logp/L, q_p=q_p^0*exp(x). Since 0<=logp/L<=1,
|exp(x)-1|<=|x|*exp(|x|)<=A*exp(A)*logp/L. Consequently

  |sum Re(q_p)-S_N(t)|
    <= A*exp(A)/L * sum_(p<=N)logp/p
    <= A*exp(A)*(1+log4).

The final inequality is the corpus MertensFirst upper bound and L>=1.
This handles negative as well as positive abscissa displacement.

At sigma=1+1/L, ZetaLogPrimeSum compares log|zeta(sigma+it)| with
sum'_p Re(p^(-sigma-it)) with error <=pi^2/6. PrimeCosineSum gives the
exact finite-head/infinite-tail decomposition. PrimeTailBound bounds the
absolute prime tail by

  T=2*(log2+2*(2*mertensFirstConst+1/2))/log2.

PrimeSigmaShift bounds the finite head change from sigma to1 by
(sigma-1)*(L+log4)<=1+log4, uniformly in the cosine weights. Thus

  |log|zeta(s_N(t))|-S_N(t)| <= pi^2/6+T+1+log4.

Triangle inequality proves the logarithmic comparison with
C_A=2B+A*exp(A)*(1+log4)+pi^2/6+T+1+log4.
Zeta is nonzero at Re(s_N)>1; Q_N is nonzero by the local norm bound.
Exponentiating the real log identity proves both positive bounds.
No boundary convergence, zero-free strip width, frequency cutoff, RH,
numerical evaluation, or unproved uniformity is assumed.

Corpus verification: actual source files PrimeCosineSum, PrimeSigmaShift,
PrimeTailBound, EulerLogCompare, ZetaLogPrimeSum, ZetaStripPrimeSum,
CharacterDistanceGrowth, SquarefreeCriticalNormalCone. Search39682 partial:
65972files gen1247417, coverage1247450/current1247452; interrupted text/source
retrieval, background refresh incomplete, semantic coverage unmeasured.
All20 candidate and20 source entries inspected; relevant exact zeta-log
and absolute-tail declarations verified in source. Unrelated hits unused.

Next: derive compact-frequency pole-scale estimates and bound the COMPLETE
labelled source, including all collisions, then prove signed cancellation
under actual moving physical profiles and full tails. U1 alone is not RH.
