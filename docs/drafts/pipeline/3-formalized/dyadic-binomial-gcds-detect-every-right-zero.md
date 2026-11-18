# Common prime divisors of dyadic central binomial coefficients

For $q=2^j$, $j\ge1$, put
$$C_j(N)=\gcd_{1\le l\le j}\binom{2^lN}{2^{l-1}N},\qquad X=qN.$$
A zero $\rho$ with $1/2<\Re\rho<1$ precludes a linear main term with error $O(N^b)$, $1/2\le b<\Re\rho$, for every sufficiently large fixed $j$.

## The common divisors

For each prime $p$, write the valuation of each binomial as a sum of binary carries, one for each power $p^r\le X$. At level $r$, the successive binomials read the $j$ low bits of $\lfloor X/p^r\rfloor$. All carry exactly when $q\mid\lfloor X/p^r\rfloor+1$. The number of levels with a common carry is at most the minimum of the $j$ row sums, which is the gcd valuation. If the first level lacks a common carry, some row has no first carry. In both cases the minimum exceeds the common-carry count by at most the number of levels $r\ge2$. Summing over primes gives the one-sided comparison
$$0\le\log C_j(N)-\sum_{m\le X}\Lambda(m)\,\mathbf1_{q\mid\lfloor X/m\rfloor+1}
\le\psi(X)-\vartheta(X)\ll\sqrt X.$$
The constant is independent of $j$. Above $\sqrt X$ the gcd valuation equals the common carry exactly.

## A bound independent of the dyadic depth

Suppose $p\mid C_j(N)$ and $2N<p^2\le qN$. Choose the last dyadic width $q'\ge2$ with $q'N<p^2$. At that earlier width the gcd valuation is exactly the common first carry. Thus for some $k$,
$$0<kp-N\le p/q'\le2N/p<2k.$$
In particular $k\le\sqrt N+1$ and $p\in\{\lfloor N/k\rfloor+1,\lfloor N/k\rfloor+2\}$. For each candidate the contribution is at most $\log(2N+2)$ by the valuation of the first binomial. At $p^2>qN$ there is no discrepancy. The uniform excess bound is $(\lfloor\sqrt{2N}\rfloor+1+2(\lfloor\sqrt N\rfloor+2))\log(2N+2)$. [Prime classification](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PrimeDivisorsAtTheFirstDyadicSquareCrossing.lean) · [Uniform bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/DeepDyadicBinomialGcdsHaveSquareRootSize.lean)

## A symbol that detects every right zero

The row increments are $+1$ at $qk-1$ and $-1$ at $qk$. Their Dirichlet symbol is
$$D_q(s)=\sum_{k\ge1}\big((qk-1)^{-s}-(qk)^{-s}\big).$$
For $\Re s>0$, integration over $[k-1/q,k]$ gives $q^{s+1}D_q(s)\to s\zeta(1+s)$, nonzero throughout this half-plane. The bound for each fixed $s$ has error $O_s(1/q)$. Thus every right zero gives a pole of $D_q(s)(-\zeta'(s)/\zeta(s)-\zeta(s))$ for all sufficiently large dyadic $q$. One increment of the actual prime count has absolute value at most $\sum_{m\mid n}\Lambda(m)=\log n$. Passing from multiples of a fixed $q$ to all cutoffs costs $O_q(1+\log X)$. Subtracting a linear main term contributes a multiple of $\zeta$ and preserves the residue at a right zero.

For $j=1$ the symbol is the alternating eta factor and the single binomial has a Stirling estimate. Larger $j$ replaces the eta factor by a symbol eventually nonzero at each candidate zero. Lean proves that any zero $\rho$ with $\Re\rho>1/2$ obstructs every linear approximation with error $O(N^b)$, $1/2\le b<\Re\rho$, for every sufficiently large fixed dyadic width. Conversely, such bounds at cofinally many fixed widths for every $b>1/2$ would prove RH. The independent bound remains open. [Hurwitz symbol](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLastQuotientClassDetectsEveryRightZero.lean) · [Prime series](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheDirichletSeriesOfDyadicBinomialPrimeCounts.lean) · [Zero obstruction](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/RightZerosObstructPowerBoundsForBinomialGcds.lean)

