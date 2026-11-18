# Dyadic differences of smooth counts

Let $S(x,y)$ count positive integers up to $x$ whose prime factors are all at most $y$. Whenever $2n<(y+1)^2$, each integer up to $2n$ that fails this test has exactly one prime factor $p>y$. Its multiples contribute $\lfloor 2n/p\rfloor-2\lfloor n/p\rfloor$ to the difference of the two complementary counts. This is the carry of $p$ in $\binom{2n}n$. Hence
$$2S(n,y)-S(2n,y)=\#\{p>y:p\mid\tbinom{2n}{n}\}.$$
The difference decreases with $y$ in this range. Its distance from the total distinct-prime count is at most $\pi(y)$. The smooth counts require only primes at most $y$.

For the first mean through $X$, freeze $y=\lfloor\sqrt X\rfloor$ for all $k<X$. Replacing $\omega(\binom{2n}{n})$ by $2S(n,y)-S(2n,y)$ at $n=\lfloor k/2\rfloor$ subtracts between zero and $X\pi(y)$ from the cumulative total. This is at most $X^{3/2}$. Thus RH is equivalent to
$$\sum_{k<X}\left(2S(\lfloor k/2\rfloor,y)-S(2\lfloor k/2\rfloor,y)-L_2(k)\right)=O_b(X^{1+b})\qquad(1/2<b<1).$$
Only primes up to $y$ enter the two smooth counts. [Lean declarations](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SmoothCountsAndTheLargeFactorsOfTheCentralBinomialCoefficient.lean) · [Distinct-prime criterion](distinct-primes-in-one-central-binomial-coefficient.md)
