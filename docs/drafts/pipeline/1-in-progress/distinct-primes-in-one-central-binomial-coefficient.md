# Distinct primes in one central binomial coefficient

Can the number of distinct prime divisors of $\binom{2n}{n}$ detect every right zero, including zeros canceled in its logarithm? Put $L_q(X)=\sum_{2\le m\le X}\mathbf1_{q\mid\lfloor X/m\rfloor+1}/\log m$. For each fixed $q=2^{j+1}$ the candidate RH criterion is
$$\sum_{X<N}\left(\omega(G_j(\lfloor X/q\rfloor))-L_q(X)\right)=O_{q,b}(N^{1+b})\qquad(1/2<b<1).$$
Here $G_0(n)=\binom{2n}{n}$. The depth can be prescribed before choosing the exponent.

For $p^2>q n$, divisibility of $G_j(n)$ is exactly the ordinary-prime last-class indicator. The smaller primes contribute at most $\sqrt{qn}$ to the count discrepancy. Increasing $X$ by one changes the ordinary-prime class sum by at most $\omega(X+1)$, since only prime divisors of $X+1$ can change their quotient. These two bounds pay for sampling at multiples of $q$.

The centered count has jump series $D_q(s)B(s)$, where $B$ is the Dirichlet series of $\mathbf1_{\rm prime}(n)-1/\log n$ with zero reference at $n=1$. Its derivative has a nonzero simple-pole residue at every right zero. The entire function $D_q$ is nonzero at $s=2$, by its positive Mellin-cell expansion. Thus a holomorphic continuation of $D_q B$ would give a meromorphic primitive of $B'$ there, impossible even if $D_q(\rho)=0$. In particular $D_2(s)=(1-2^{1-s})\zeta(s)$ still detects the logarithmic branch. In the other direction the bounded-prefix triangular kernel transfers the ordinary $\pi$-error estimate to the first mean. An independent estimate on the number of distinct factors remains open.
