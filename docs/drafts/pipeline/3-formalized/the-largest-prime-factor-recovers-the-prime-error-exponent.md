# The largest prime factor recovers the prime-error exponent

Put $P(1)=1$, let $P(n)$ be the largest prime factor of $n>1$, and set $H(N)=\sum_{n\le N}P(n)\log P(n)$. For every $1/2\le b<1$,
$$H(N)-\pi^2N^2/12=O(N^{1+b})\quad\Longleftrightarrow\quad\psi(N)-N=O(N^b).$$

The complete quotient blocks give $W(N)=\sum_{n\le N}\sum_{d\mid n}d\Lambda(d)$. Removing proper prime powers costs at most $N(\psi(N)-\vartheta(N))$. A prime divisor $p<P(n)$ satisfies $pP(n)\mid n$, so $p\le\sqrt N$. Removing these divisors costs at most $N\psi(\sqrt N)$. Both bounds are $O(N^{3/2})$.

For $x=N/d$ and $u=\lfloor x\rfloor$ one has $|u(u+1)-x^2|\le x$. Summation over $d$ and the reciprocal-square tail give $|\sum_{n\le N}\sigma(n)-\pi^2N^2/12|\le N(2+\log N)/2$. The equivalence now follows from complete-block inversion, including at $b=1/2$.

Lean declarations: `primeDivisorSizeMass_sub_largestPrimeLogMass`, `divisorSizeMass_quadratic_error`, `largestPrimeLogMass_quadratic_power_iff`. [Lean source](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLargestPrimeFactorInCompleteQuotientBlocks.lean)
