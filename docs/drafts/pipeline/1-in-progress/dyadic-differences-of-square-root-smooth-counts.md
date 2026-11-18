# Dyadic differences of smooth counts

Let $S(x,y)$ count positive integers up to $x$ whose prime factors are all at most $y$. At $y\ge2$ with $y^2\ge 2n$, each integer up to $2n$ that fails this test has exactly one prime factor $p>y$. Its multiples contribute $\lfloor 2n/p\rfloor-2\lfloor n/p\rfloor$ to the difference of the two complementary counts. This is the carry of $p$ in $\binom{2n}n$. Hence
$$2S(n,y)-S(2n,y)=\#\{p>y:p\mid\tbinom{2n}{n}\}.$$
The difference decreases with $y$ in this range. At the least admissible $y$, its distance from the total distinct-prime count is at most $\pi(y)$. The smooth counts require only primes at most $y$.

At $y^3\ge 2n$ the second inclusion–exclusion term counts distinct pairs $p,r>y$ for which $\lfloor 2n/(pr)\rfloor$ is odd. Estimate the centered first mean of the smooth difference at the square-root cutoff directly from its small-prime support. [Distinct-prime criterion](../3-formalized/distinct-primes-in-one-central-binomial-coefficient.md)
