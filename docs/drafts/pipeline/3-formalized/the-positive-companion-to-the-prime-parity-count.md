# The positive companion to the prime parity count

Set $v(n)=\prod_p1/v_p(n)!$, $d_+(n)=v(n)/(1+\Omega(n))$ and $F_+(N)=\sum_{n\le N}d_+(n)$. Every $n>1$ contributes $\sum_{p\mid n}d_+(n/p)=v(n)$, so
$$\sum_{p\le N}F_+(\lfloor N/p\rfloor)=\sum_{n\le N}v(n)-1.$$
The signed companion uses the same coefficients multiplied by $(-1)^{\Omega(n)}$. [Signed count](../3-formalized/the-linear-growth-boundary-for-ordinary-prime-quotient-profiles.md)

With $h=v*\mu$, the local generating function is $(1-z)e^z$. Thus $h(p)=0$ and $h(p^k)=-(k-1)/k!$ for $k\ge2$. For $1/2<b\le1$ put $K_b=\sum_{d\ge1}|h(d)|d^{-b}<\infty$ and $c=\sum_{d\ge1}h(d)/d$. Then
$$\left|\sum_{n\le N}v(n)-cN\right|\le K_bN^b.$$
Indeed $v=h*1$, so each summand in the remainder is $h(d)(\lfloor N/d\rfloor-N/d)$. Its modulus is at most $|h(d)|(N/d)^b$ on both sides of $N$. The positive count therefore has every strict half-power error bound unconditionally. The constant is positive, since $v=1$ on squarefree integers. Its Euler product is $\prod_p(1-1/p)e^{1/p}$. [Lean proof of the Euler product, positivity and strict half-power estimates](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ThePositivePrimeFactorialCountHasASquareRootError.lean)

Whenever $h(d)\ne0$, each prime exponent of $d$ is zero or at least two and $|h(d)|\le1$. Thus $d=a^2b^3$ for positive integers $a,b$. For $u>0$ and $a\ge1$,
$$\min(1,u^2/a^2)\le 4u^2\left((u+a-1)^{-1}-(u+a)^{-1}\right).$$
Summing in $a$ with $u=\sqrt{N/b^3}$ bounds the total floor error by $4\zeta(3/2)\sqrt N$. This endpoint bound uses only the support and size of the correction.

An uncentered ordinary-prime count attains the endpoint as well. Let $G(N)=F_+(N)-2F_+(\lfloor N/2\rfloor)$. Since integer division commutes in the two denominators, its prime sum equals the same dyadic difference of the positive prime sum. For $N\ge2$ its main term is $1+c(N\bmod 2)$. For every $N\ge1$ the full sum has modulus at most $(37+c)\sqrt N$. But $G(1)=1$, $|G(N)|\le2N$, and the rigidity theorem excludes $G(N)=O(N^a)$ for every $a<1$. This gives a nonzero linear-growth profile with an unconditional square-root prime count. The factorial parity profile on the same growth boundary has the Mertens error exponent. [Endpoint and profile rigidity](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ASquareRootBoundFromThePowerfulDivisors.lean)
