# The largest prime factor and the confined prime wave

Put $P(1)=1$ and let $P(n)$ be the largest prime factor of $n$ for $n\ge2$. Does the factorization statistic $H(N)=\sum_{n\le N}P(n)\log P(n)$ have an arithmetic estimate independent of the prime wave?

A complete deep quotient block gives $\sum_{m\mid n}m\Lambda(m)$. In the sum through $N$, removing all proper prime powers costs at most $N(\psi(N)-\vartheta(N))=O(N^{3/2})$. Removing the prime divisors other than $P(n)$ costs at most $N\vartheta(\sqrt N)=O(N^{3/2})$, since two distinct primes exceeding $\sqrt N$ cannot divide the same $n\le N$. Thus $H$ has the same summatory exponent as the complete prime blocks down to $N^{3/2}$. The ordinary integer baseline is $\sum_{n\le N}\sigma(n)=\zeta(2)N^2/2+O(N\log(2N))$, by summing $\lfloor N/d\rfloor(\lfloor N/d\rfloor+1)/2$ over $d$.

Complete-block inversion gives, for $1/2\le b<1$,
$$H(N)-\frac{\zeta(2)}2N^2=O(N^{1+b})\quad\Longleftrightarrow\quad \psi(N)-N=O(N^b).$$
[Formal equivalence](../3-formalized/the-largest-prime-factor-recovers-the-prime-error-exponent.md)

Under a single quartet of multiplicity $h$, the complex coefficient of $-2h\Re N^{1+\rho}$ in $H(N)$ should be $\zeta(1+\rho)/(1+\rho)$. Partial summation gives this factor from the weight $m$ and the divisor convolution. The existing divisibility tree already uses $n/P(n)$ as its parent. The open question concerns its edge labels $P(n)$ across successive cutoffs.

At the boundary exponent there is a sharper question. The square levels alone contribute
$$\sum_{d\le N}\sum_{p\le\sqrt{N/d}}p^2\log p\sim \frac{\zeta(3/2)}3N^{3/2}.$$
This follows from partial summation of $\vartheta$ and the summable majorant $Cd^{-3/2}$. Higher powers cost $O(N^{4/3}\log N)$. Non-largest prime divisors $p\le\varepsilon\sqrt N$ cost $O(\varepsilon N^{3/2})$. A larger non-largest divisor must coexist with a prime $P>p$ in the same integer. Both lie between $\varepsilon\sqrt N$ and $\sqrt N/\varepsilon$, and each pair has at most $\varepsilon^{-2}$ multiples. The prime number theorem bounds this contribution by $O_\varepsilon(N^{3/2}/\log N)$. Thus the square levels should give the entire first bias. The next term asks for the two-prime sum with weight $p\log p$ and $p<P$, $dpP\le N$.
